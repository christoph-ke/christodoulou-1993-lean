module

public import ChristodoulouBV.Uniqueness.ExtensionStripDomain
import ChristodoulouBV.C1Solution.ExtractionMass

/-!
# Local radius jets on a development

The radius primitives differentiate at every point interior to the actual
development. This extraction uses only a short characteristic interval and
the C¹ expansion fields; the domain need not be triangular.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The outgoing radius derivative at an interior development point. -/
theorem radius_hasDerivAt_v_of_c1_interior
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {u v : ℝ} (hp : (u, v) ∈ interior U) :
    HasDerivAt (S.r u) (S.lam u v) v := by
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
  have hlam : ContinuousOn (S.lam u) (Icc a c) :=
    H.lam_c1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => subset_closure (hmap t ht))
  have hprim (t : ℝ) (ht : t ∈ Ioo a c) :
      IntervalPrimitive (S.r u) (S.lam u) a t := by
    apply H.solution.radius_out u a t ht.1.le
    intro p hpseg
    rcases p with ⟨x, y⟩
    obtain ⟨rfl, hy⟩ : x = u ∧ y ∈ Icc a t := by
      simpa only [outSeg, mem_prod, mem_singleton_iff] using hpseg
    exact hmap y ⟨hy.1, hy.2.trans ht.2.le⟩
  exact C1Solution.hasDerivAt_of_intervalPrimitive_local hav hvc hlam hprim

/-- The incoming radius derivative at an interior development point. -/
theorem radius_hasDerivAt_u_of_c1_interior
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {u v : ℝ} (hp : (u, v) ∈ interior U) :
    HasDerivAt (fun s => S.r s v) (S.nu u v) u := by
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
  have hnu : ContinuousOn (fun s => S.nu s v) (Icc a c) :=
    H.nu_c1.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => subset_closure (hmap s hs))
  have hprim (t : ℝ) (ht : t ∈ Ioo a c) :
      IntervalPrimitive (fun s => S.r s v) (fun s => S.nu s v) a t := by
    apply H.solution.radius_in v a t ht.1.le
    intro p hpseg
    rcases p with ⟨x, y⟩
    obtain ⟨hx, rfl⟩ : x ∈ Icc a t ∧ y = v := by
      simpa only [inSeg, mem_prod, mem_singleton_iff] using hpseg
    exact hmap x ⟨hx.1, hx.2.trans ht.2.le⟩
  exact C1Solution.hasDerivAt_of_intervalPrimitive_local hau huc hnu hprim

/-- The outgoing scalar-radius primitive differentiates on the interior of
any C¹ development. -/
theorem scalarRadius_hasDerivAt_v_of_c1_interior
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {u v : ℝ} (hp : (u, v) ∈ interior U) :
    HasDerivAt (fun t => S.r u t * S.phi u t) (S.alpha u v) v := by
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
  have halpha : ContinuousOn (S.alpha u) (Icc a c) :=
    (alpha_contDiffOn_closure H).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => subset_closure (hmap t ht))
  have hprim (t : ℝ) (ht : t ∈ Ioo a c) :
      IntervalPrimitive (fun s => S.r u s * S.phi u s) (S.alpha u) a t := by
    apply H.solution.scalar_radius_out u a t ht.1.le
    intro p hpseg
    rcases p with ⟨x, y⟩
    obtain ⟨rfl, hy⟩ : x = u ∧ y ∈ Icc a t := by
      simpa only [outSeg, mem_prod, mem_singleton_iff] using hpseg
    exact hmap y ⟨hy.1, hy.2.trans ht.2.le⟩
  exact C1Solution.hasDerivAt_of_intervalPrimitive_local hav hvc halpha hprim

/-- The scalar derivative is `θ/r` at an interior point. -/
theorem phi_hasDerivAt_v_of_c1_interior
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {u v : ℝ} (hp : (u, v) ∈ interior U) :
    HasDerivAt (S.phi u) (S.theta u v / S.r u v) v := by
  have hpU : (u, v) ∈ U := interior_subset hp
  have hr := radius_hasDerivAt_v_of_c1_interior H hp
  have hscalar := scalarRadius_hasDerivAt_v_of_c1_interior H hp
  have hrne : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hdiv := hscalar.div hr hrne
  have hOpen : IsOpen {t : ℝ | (u, t) ∈ interior U} :=
    isOpen_interior.preimage (continuous_const.prodMk continuous_id)
  have hEq : (fun t => S.r u t * S.phi u t / S.r u t) =ᶠ[𝓝 v] S.phi u := by
    filter_upwards [hOpen.mem_nhds hp] with t ht
    have htU : (u, t) ∈ U := interior_subset ht
    have htne : S.r u t ≠ 0 := ne_of_gt (H.solution.radius_pos (u, t) htU)
    exact mul_div_cancel_left₀ (S.phi u t) htne
  have h := hdiv.congr_of_eventuallyEq hEq.symm
  convert h using 1
  simp only [Fields.theta]
  field_simp

end ChristodoulouBV.Uniqueness

end
