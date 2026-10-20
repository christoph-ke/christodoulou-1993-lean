module

public import ChristodoulouBV.Uniqueness.ExtensionLocalGap
import ChristodoulouBV.C1Solution.ExtractionMass

/-!
# Local mixed coefficient jets

The frozen incoming and outgoing primitives give the classical mixed jets
on an arbitrary C¹ development. The positive mass gap keeps the rational
coefficient nonsingular.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The mixed coefficient in equations (1.14a) and (1.14b). -/
@[expose] noncomputable def localMixedCoefficient (S : Fields) (u v : ℝ) : ℝ :=
  (2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
    ((1 - 2 * S.m u v / S.r u v) * S.r u v)

/-- The mixed coefficient is continuous on an actual incoming segment with
mass ratio strictly below one. -/
theorem localMixedCoefficient_continuousOn_incoming_segment
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {v a c : ℝ} (hac : a ≤ c)
    (hseg : ∀ s ∈ Icc a c, (s, v) ∈ U) :
    ContinuousOn (fun s => localMixedCoefficient S s v) (Icc a c) := by
  have hm : ContinuousOn (fun s => S.m s v) (Icc a c) :=
    mass_continuousOn_incoming_segment H hac hseg
  have hr : ContinuousOn (fun s => S.r s v) (Icc a c) := by
    refine intervalPrimitive_continuousOn_of_subintervals
      (g := fun s => S.nu s v) hac ?_
    intro t ht
    apply H.solution.radius_in v a t ht.1
    intro p hp
    rcases p with ⟨x, y⟩
    obtain ⟨hx, rfl⟩ : x ∈ Icc a t ∧ y = v := by
      simpa only [inSeg, mem_prod, mem_singleton_iff] using hp
    exact hseg x ⟨hx.1, hx.2.trans ht.2⟩
  have hlam : ContinuousOn (fun s => S.lam s v) (Icc a c) :=
    H.lam_c1.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => subset_closure (hseg s hs))
  have hnu : ContinuousOn (fun s => S.nu s v) (Icc a c) :=
    H.nu_c1.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => subset_closure (hseg s hs))
  have hrne : ∀ s ∈ Icc a c, S.r s v ≠ 0 :=
    fun s hs => ne_of_gt (H.solution.radius_pos (s, v) (hseg s hs))
  have hratio : ContinuousOn
      (fun s => 2 * S.m s v / S.r s v) (Icc a c) :=
    (continuousOn_const.mul hm).div hr hrne
  have hden : ∀ s ∈ Icc a c,
      (1 - 2 * S.m s v / S.r s v) * S.r s v ≠ 0 := by
    intro s hs
    exact mul_ne_zero (ne_of_gt (sub_pos.mpr
      (mass_ratio_lt_one_of_c1_domain H (hseg s hs))))
      (hrne s hs)
  exact (((hratio.mul hlam).mul hnu).div
    ((continuousOn_const.sub hratio).mul hr) hden)

/-- The incoming derivative of the outgoing expansion is the frozen mixed
coefficient at every interior point of a development below the mass barrier. -/
theorem lam_hasDerivAt_u_of_c1_interior
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {u v : ℝ} (hp : (u, v) ∈ interior U) :
    HasDerivAt (fun s => S.lam s v) (localMixedCoefficient S u v) u := by
  have hOpen : IsOpen {s : ℝ | (s, v) ∈ interior U} :=
    isOpen_interior.preimage (continuous_id.prodMk continuous_const)
  obtain ⟨l, r, ⟨hl, hr⟩, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hOpen.mem_nhds hp)
  let a : ℝ := (l + u) / 2
  let c : ℝ := (u + r) / 2
  have hla : l < a := by dsimp [a]; linarith
  have hau : a < u := by dsimp [a]; linarith
  have huc : u < c := by dsimp [c]; linarith
  have hcr : c < r := by dsimp [c]; linarith
  have hmap (s : ℝ) (hs : s ∈ Icc a c) : (s, v) ∈ U :=
    interior_subset (hsub ⟨hla.trans_le hs.1, hs.2.trans_lt hcr⟩)
  have hg : ContinuousOn (fun s => localMixedCoefficient S s v) (Icc a c) :=
    localMixedCoefficient_continuousOn_incoming_segment H
      (hau.le.trans huc.le) hmap
  have hprim (t : ℝ) (ht : t ∈ Ioo a c) :
      IntervalPrimitive (fun s => S.lam s v)
        (fun s => localMixedCoefficient S s v) a t := by
    apply H.solution.lam_in v a t ht.1.le
    intro p hpseg
    rcases p with ⟨s, y⟩
    obtain ⟨hs, rfl⟩ : s ∈ Icc a t ∧ y = v := by
      simpa only [inSeg, mem_prod, mem_singleton_iff] using hpseg
    exact hmap s ⟨hs.1, hs.2.trans ht.2.le⟩
  exact C1Solution.hasDerivAt_of_intervalPrimitive_local hau huc hg hprim

/-- The incoming derivative of `α` is the mixed coefficient times `φ` on
the same interior neighborhood. -/
theorem alpha_hasDerivAt_u_of_c1_interior
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {u v : ℝ} (hp : (u, v) ∈ interior U) :
    HasDerivAt (fun s => S.alpha s v)
      (localMixedCoefficient S u v * S.phi u v) u := by
  have hOpen : IsOpen {s : ℝ | (s, v) ∈ interior U} :=
    isOpen_interior.preimage (continuous_id.prodMk continuous_const)
  obtain ⟨l, r, ⟨hl, hr⟩, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hOpen.mem_nhds hp)
  let a : ℝ := (l + u) / 2
  let c : ℝ := (u + r) / 2
  have hla : l < a := by dsimp [a]; linarith
  have hau : a < u := by dsimp [a]; linarith
  have huc : u < c := by dsimp [c]; linarith
  have hcr : c < r := by dsimp [c]; linarith
  have hmap (s : ℝ) (hs : s ∈ Icc a c) : (s, v) ∈ U :=
    interior_subset (hsub ⟨hla.trans_le hs.1, hs.2.trans_lt hcr⟩)
  have hcoeff : ContinuousOn (fun s => localMixedCoefficient S s v) (Icc a c) :=
    localMixedCoefficient_continuousOn_incoming_segment H
      (hau.le.trans huc.le) hmap
  have hphi : ContinuousOn (fun s => S.phi s v) (Icc a c) :=
    H.phi_c1.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => subset_closure (hmap s hs))
  have hg : ContinuousOn
      (fun s => localMixedCoefficient S s v * S.phi s v) (Icc a c) :=
    hcoeff.mul hphi
  have hprim (t : ℝ) (ht : t ∈ Ioo a c) :
      IntervalPrimitive (fun s => S.alpha s v)
        (fun s => localMixedCoefficient S s v * S.phi s v) a t := by
    apply H.solution.alpha_in v a t ht.1.le
    intro p hpseg
    rcases p with ⟨s, y⟩
    obtain ⟨hs, rfl⟩ : s ∈ Icc a t ∧ y = v := by
      simpa only [inSeg, mem_prod, mem_singleton_iff] using hpseg
    exact hmap s ⟨hs.1, hs.2.trans ht.2.le⟩
  exact C1Solution.hasDerivAt_of_intervalPrimitive_local hau huc hg hprim

/-- The pointwise quotient transport equation (4.10a) on an arbitrary
development below the mass barrier. -/
theorem outgoing_quotient_hasDerivAt_u_of_c1_interior
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {u v : ℝ} (hp : (u, v) ∈ interior U) :
    HasDerivAt (fun s => S.alpha s v / S.lam s v)
      (-((2 * S.m u v / S.r u v) / (1 - 2 * S.m u v / S.r u v)) *
        (S.nu u v / S.r u v) * (S.theta u v / S.lam u v)) u := by
  have hpU : (u, v) ∈ U := interior_subset hp
  have hlam := lam_hasDerivAt_u_of_c1_interior H hp
  have halpha := alpha_hasDerivAt_u_of_c1_interior H hp
  have hlne : S.lam u v ≠ 0 :=
    ne_of_gt (H.solution.lam_pos (u, v) hpU)
  have hrne : S.r u v ≠ 0 :=
    ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hgap : 1 - 2 * S.m u v / S.r u v ≠ 0 :=
    ne_of_gt (sub_pos.mpr (mass_ratio_lt_one_of_c1_domain H hpU))
  have h := halpha.div hlam hlne
  convert h using 1
  dsimp [localMixedCoefficient, Fields.theta]
  field_simp
  ring

/-- The outgoing derivative of the incoming expansion is the same mixed
coefficient at every interior point below the mass barrier. -/
theorem nu_hasDerivAt_v_of_c1_interior
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {u v : ℝ} (hp : (u, v) ∈ interior U) :
    HasDerivAt (S.nu u) (localMixedCoefficient S u v) v := by
  have hOpen : IsOpen {t : ℝ | (u, t) ∈ interior U} :=
    isOpen_interior.preimage (continuous_const.prodMk continuous_id)
  obtain ⟨l, r, ⟨hl, hr⟩, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hOpen.mem_nhds hp)
  let a : ℝ := (l + v) / 2
  let c : ℝ := (v + r) / 2
  have hla : l < a := by dsimp [a]; linarith
  have hav : a < v := by dsimp [a]; linarith
  have hvc : v < c := by dsimp [c]; linarith
  have hcr : c < r := by dsimp [c]; linarith
  have hmap (t : ℝ) (ht : t ∈ Icc a c) : (u, t) ∈ U :=
    interior_subset (hsub ⟨hla.trans_le ht.1, ht.2.trans_lt hcr⟩)
  have hm : ContinuousOn (S.m u) (Icc a c) :=
    mass_continuousOn_outgoing_segment H (hav.le.trans hvc.le) hmap
  have hrad : ContinuousOn (S.r u) (Icc a c) := by
    refine intervalPrimitive_continuousOn_of_subintervals
      (g := S.lam u) (hav.le.trans hvc.le) ?_
    intro t ht
    apply H.solution.radius_out u a t ht.1
    intro p hpseg
    rcases p with ⟨x, y⟩
    obtain ⟨rfl, hy⟩ : x = u ∧ y ∈ Icc a t := by
      simpa only [outSeg, mem_prod, mem_singleton_iff] using hpseg
    exact hmap y ⟨hy.1, hy.2.trans ht.2⟩
  have hlam : ContinuousOn (S.lam u) (Icc a c) :=
    H.lam_c1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => subset_closure (hmap t ht))
  have hnu : ContinuousOn (S.nu u) (Icc a c) :=
    H.nu_c1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => subset_closure (hmap t ht))
  have hrne : ∀ t ∈ Icc a c, S.r u t ≠ 0 :=
    fun t ht => ne_of_gt (H.solution.radius_pos (u, t) (hmap t ht))
  have hratio : ContinuousOn
      (fun t => 2 * S.m u t / S.r u t) (Icc a c) :=
    (continuousOn_const.mul hm).div hrad hrne
  have hden : ∀ t ∈ Icc a c,
      (1 - 2 * S.m u t / S.r u t) * S.r u t ≠ 0 := by
    intro t ht
    exact mul_ne_zero (ne_of_gt (sub_pos.mpr
      (mass_ratio_lt_one_of_c1_domain H (hmap t ht))))
      (hrne t ht)
  have hg : ContinuousOn (fun t => localMixedCoefficient S u t) (Icc a c) :=
    (((hratio.mul hlam).mul hnu).div
      ((continuousOn_const.sub hratio).mul hrad) hden)
  have hprim (t : ℝ) (ht : t ∈ Ioo a c) :
      IntervalPrimitive (S.nu u)
        (fun s => localMixedCoefficient S u s) a t := by
    apply H.solution.nu_out u a t ht.1.le
    intro p hpseg
    rcases p with ⟨x, y⟩
    obtain ⟨rfl, hy⟩ : x = u ∧ y ∈ Icc a t := by
      simpa only [outSeg, mem_prod, mem_singleton_iff] using hpseg
    exact hmap y ⟨hy.1, hy.2.trans ht.2.le⟩
  exact C1Solution.hasDerivAt_of_intervalPrimitive_local hav hvc hg hprim

end ChristodoulouBV.Uniqueness

end
