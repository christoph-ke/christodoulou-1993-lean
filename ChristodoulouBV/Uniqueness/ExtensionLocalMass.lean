module

public import ChristodoulouBV.Uniqueness.ExtensionLocalRadius
import ChristodoulouBV.C1Solution.ExtractionMass

/-!
# Local mass jets on a C¹ development

The mass primitive gives the classical mass derivatives at interior points of
an arbitrary development. No triangular cutoff is used.
-/

public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- A function satisfying the frozen primitive relation on all initial
subintervals is continuous on the entire closed interval. -/
theorem intervalPrimitive_continuousOn_of_subintervals
    {f g : ℝ → ℝ} {a c : ℝ} (hac : a ≤ c)
    (hprim : ∀ t ∈ Icc a c, IntervalPrimitive f g a t) :
    ContinuousOn f (Icc a c) := by
  have hInt : IntervalIntegrable g volume a c :=
    (hprim c ⟨hac, le_rfl⟩).1
  have hCont : ContinuousOn (fun t => f a + ∫ s in a..t, g s) (Icc a c) :=
    continuousOn_const.add (by
      simpa only [uIcc_of_le hac] using
        (intervalIntegral.continuousOn_primitive_interval' hInt left_mem_uIcc))
  apply hCont.congr
  intro t ht
  have h := (hprim t ht).2
  linarith only [h]

/-- Along an outgoing segment in a development, the actual mass is
continuous, including both endpoints. -/
theorem mass_continuousOn_outgoing_segment
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {u a c : ℝ} (hac : a ≤ c)
    (hseg : ∀ t ∈ Icc a c, (u, t) ∈ U) :
    ContinuousOn (S.m u) (Icc a c) := by
  refine intervalPrimitive_continuousOn_of_subintervals
    (g := fun t => (1 - 2 * S.m u t / S.r u t) * (S.theta u t)^2 /
      (2 * S.lam u t)) hac ?_
  intro t ht
  apply H.solution.mass_out u a t ht.1
  intro p hp
  rcases p with ⟨x, y⟩
  obtain ⟨rfl, hy⟩ : x = u ∧ y ∈ Icc a t := by
    simpa only [outSeg, mem_prod, mem_singleton_iff] using hp
  exact hseg y ⟨hy.1, hy.2.trans ht.2⟩

/-- Along an incoming segment in a development, the actual mass is
continuous, including both endpoints. -/
theorem mass_continuousOn_incoming_segment
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {v a c : ℝ} (hac : a ≤ c)
    (hseg : ∀ t ∈ Icc a c, (t, v) ∈ U) :
    ContinuousOn (fun t => S.m t v) (Icc a c) := by
  refine intervalPrimitive_continuousOn_of_subintervals
    (g := fun t => (1 - 2 * S.m t v / S.r t v) * (S.zeta t v)^2 /
      (2 * S.nu t v)) hac ?_
  intro t ht
  apply H.solution.mass_in v a t ht.1
  intro p hp
  rcases p with ⟨x, y⟩
  obtain ⟨hx, rfl⟩ : x ∈ Icc a t ∧ y = v := by
    simpa only [inSeg, mem_prod, mem_singleton_iff] using hp
  exact hseg x ⟨hx.1, hx.2.trans ht.2⟩

/-- The outgoing mass derivative on the interior of any C¹ development. -/
theorem mass_hasDerivAt_v_of_c1_interior
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {u v : ℝ} (hp : (u, v) ∈ interior U) :
    HasDerivAt (S.m u)
      ((1 - 2 * S.m u v / S.r u v) * (S.theta u v)^2 /
        (2 * S.lam u v)) v := by
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
  have hR : ContinuousOn (S.r u) (Icc a c) := by
    refine intervalPrimitive_continuousOn_of_subintervals
      (g := S.lam u) (hav.le.trans hvc.le) ?_
    intro t ht
    apply H.solution.radius_out u a t ht.1
    intro p hpseg
    rcases p with ⟨x, y⟩
    obtain ⟨rfl, hy⟩ : x = u ∧ y ∈ Icc a t := by
      simpa only [outSeg, mem_prod, mem_singleton_iff] using hpseg
    exact hmap y ⟨hy.1, hy.2.trans ht.2⟩
  have htheta : ContinuousOn (S.theta u) (Icc a c) :=
    H.theta_c1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => subset_closure (hmap t ht))
  have hlam : ContinuousOn (S.lam u) (Icc a c) :=
    H.lam_c1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => subset_closure (hmap t ht))
  have hrne : ∀ t ∈ Icc a c, S.r u t ≠ 0 :=
    fun t ht => ne_of_gt (H.solution.radius_pos (u, t) (hmap t ht))
  have hlne : ∀ t ∈ Icc a c, S.lam u t ≠ 0 :=
    fun t ht => ne_of_gt (H.solution.lam_pos (u, t) (hmap t ht))
  have hg : ContinuousOn (fun t =>
      (1 - 2 * S.m u t / S.r u t) * (S.theta u t)^2 /
        (2 * S.lam u t)) (Icc a c) :=
    ((continuousOn_const.sub ((continuousOn_const.mul hm).div hR hrne)).mul
      (htheta.pow 2)).div (continuousOn_const.mul hlam)
      (fun t ht => by exact mul_ne_zero (by norm_num) (hlne t ht))
  have hprim (t : ℝ) (ht : t ∈ Ioo a c) :
      IntervalPrimitive (S.m u)
        (fun s => (1 - 2 * S.m u s / S.r u s) * (S.theta u s)^2 /
          (2 * S.lam u s)) a t := by
    apply H.solution.mass_out u a t ht.1.le
    intro p hpseg
    rcases p with ⟨x, y⟩
    obtain ⟨rfl, hy⟩ : x = u ∧ y ∈ Icc a t := by
      simpa only [outSeg, mem_prod, mem_singleton_iff] using hpseg
    exact hmap y ⟨hy.1, hy.2.trans ht.2.le⟩
  exact C1Solution.hasDerivAt_of_intervalPrimitive_local hav hvc hg hprim

/-- Differentiating the mass ratio in the outgoing direction gives the
identity used before equation (5.2). -/
theorem mass_ratio_hasDerivAt_v_of_c1_interior
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {u v : ℝ} (hp : (u, v) ∈ interior U) :
    HasDerivAt (fun t => 2 * S.m u t / S.r u t)
      ((1 - 2 * S.m u v / S.r u v) * (S.theta u v)^2 /
        (S.r u v * S.lam u v) -
        (2 * S.m u v / S.r u v) * S.lam u v / S.r u v) v := by
  have hr := radius_hasDerivAt_v_of_c1_interior H hp
  have hm := mass_hasDerivAt_v_of_c1_interior H hp
  have hrne : S.r u v ≠ 0 :=
    ne_of_gt (H.solution.radius_pos (u, v) (interior_subset hp))
  have h := ((hm.const_mul 2).div hr hrne)
  convert h using 1; field_simp

end ChristodoulouBV.Uniqueness

end
