module

public import ChristodoulouBV.Uniqueness.ExtensionLocalMass
import ChristodoulouBV.BVSolution.SignAux

/-!
# The positive mass gap on an arbitrary C¹ development

The radius and mass primitives form a scalar linear equation on each
outgoing ray. Its zero axis trace and positive `λ` source force a positive
gap at every point of a domain of development.
-/

public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

private theorem mass_gap_local_linear_equation_of_c1
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {u v a d : ℝ} (hp : (u, v) ∈ U)
    (hua : u < a) (had : a ≤ d) (hdv : d ≤ v) :
    let k : ℝ → ℝ := fun t => -(S.theta u t)^2 /
      (S.r u t * S.lam u t)
    let y : ℝ → ℝ := fun t => S.r u t - 2 * S.m u t
    IntervalIntegrable k volume a d ∧
    IntervalIntegrable (S.lam u) volume a d ∧
    IntervalIntegrable (fun t => k t * y t) volume a d ∧
    ∀ t ∈ Icc a d,
      y t - y a = ∫ s in a..t, (k s * y s + S.lam u s) := by
  dsimp
  let k : ℝ → ℝ := fun t => -(S.theta u t)^2 /
    (S.r u t * S.lam u t)
  let y : ℝ → ℝ := fun t => S.r u t - 2 * S.m u t
  have hmap (t : ℝ) (ht : t ∈ Icc a d) : (u, t) ∈ U :=
    H.solution.development.outgoing_mem hp
      (hua.trans_le ht.1) (ht.2.trans hdv)
  have hseg (t : ℝ) (ht : t ∈ Icc a d) : outSeg u a t ⊆ U :=
    H.solution.development.out_seg_subset hp hua ht.1 (ht.2.trans hdv)
  have hr : ContinuousOn (S.r u) (Icc a d) := by
    refine intervalPrimitive_continuousOn_of_subintervals
      (g := S.lam u) had ?_
    intro t ht
    exact H.solution.radius_out u a t ht.1 (hseg t ht)
  have hm : ContinuousOn (S.m u) (Icc a d) :=
    mass_continuousOn_outgoing_segment H had hmap
  have hlam : ContinuousOn (S.lam u) (Icc a d) :=
    H.lam_c1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => subset_closure (hmap t ht))
  have htheta : ContinuousOn (S.theta u) (Icc a d) :=
    H.theta_c1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => subset_closure (hmap t ht))
  have hden : ∀ t ∈ Icc a d, S.r u t * S.lam u t ≠ 0 := by
    intro t ht
    exact mul_ne_zero
      (ne_of_gt (H.solution.radius_pos (u, t) (hmap t ht)))
      (ne_of_gt (H.solution.lam_pos (u, t) (hmap t ht)))
  have hk : ContinuousOn k (Icc a d) :=
    (htheta.pow 2).neg.div (hr.mul hlam) hden
  have hy : ContinuousOn y (Icc a d) :=
    hr.sub (continuousOn_const.mul hm)
  have hky : ContinuousOn (fun t => k t * y t) (Icc a d) := hk.mul hy
  have hkI : IntervalIntegrable k volume a d :=
    hk.intervalIntegrable_of_Icc had
  have hlamI : IntervalIntegrable (S.lam u) volume a d :=
    hlam.intervalIntegrable_of_Icc had
  have hkyI : IntervalIntegrable (fun t => k t * y t) volume a d :=
    hky.intervalIntegrable_of_Icc had
  refine ⟨hkI, hlamI, hkyI, ?_⟩
  intro t ht
  have hR := H.solution.radius_out u a t ht.1 (hseg t ht)
  have hM := H.solution.mass_out u a t ht.1 (hseg t ht)
  have hkyAt : IntervalIntegrable (fun s => k s * y s) volume a t :=
    (hky.mono (fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)).intervalIntegrable_of_Icc
      ht.1
  have hId : (∫ s in a..t, k s * y s) =
      ∫ s in a..t, -2 * ((1 - 2 * S.m u s / S.r u s) *
        (S.theta u s)^2 / (2 * S.lam u s)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1
    intro s hs
    have hsU := H.solution.development.outgoing_mem hp
      (hua.trans_le hs.1.le) (hs.2.le.trans (ht.2.trans hdv))
    have hrad : S.r u s ≠ 0 :=
      ne_of_gt (H.solution.radius_pos (u, s) hsU)
    have hl : S.lam u s ≠ 0 :=
      ne_of_gt (H.solution.lam_pos (u, s) hsU)
    dsimp [k, y]
    field_simp
  calc
    y t - y a = (S.r u t - S.r u a) -
        2 * (S.m u t - S.m u a) := by dsimp [y]; ring
    _ = (∫ s in a..t, S.lam u s) -
        2 * (∫ s in a..t,
          (1 - 2 * S.m u s / S.r u s) * (S.theta u s)^2 /
            (2 * S.lam u s)) := by rw [hR.2, hM.2]
    _ = (∫ s in a..t, S.lam u s) +
        (∫ s in a..t, k s * y s) := by
      rw [hId, intervalIntegral.integral_const_mul]
      ring
    _ = ∫ s in a..t, (k s * y s + S.lam u s) := by
      rw [intervalIntegral.integral_add hkyAt hR.1]
      ring

/-- Every C¹ solution on a domain of development has a strictly positive
mass gap at every in-domain point. -/
theorem mass_gap_pos_of_c1_domain
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {u v : ℝ} (hp : (u, v) ∈ U) :
    0 < S.r u v - 2 * S.m u v := by
  obtain ⟨c, hc, hlam⟩ := H.lam_bounded_below
  have huv : u < v := (H.solution.development.1 hp).2
  have hrAxis : Tendsto (S.r u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [H.solution.development.axis_filter_eq hp] using
      H.solution.radius_axis u (H.solution.development.axis_mem hp)
  have hmAxis : Tendsto (S.m u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [H.solution.development.axis_filter_eq hp] using
      H.solution.mass_axis u (H.solution.development.axis_mem hp)
  have hgapAxis : Tendsto (fun t => S.r u t - 2 * S.m u t)
      (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    have htwo : Tendsto (fun t => 2 * S.m u t)
        (𝓝[>] u) (𝓝 (0 : ℝ)) := by
      simpa using tendsto_const_nhds.mul hmAxis
    simpa using hrAxis.sub htwo
  apply IsBVSolution.linear_solution_pos_of_axis_trace
    (u := u) (b := v) (c := c)
    (k := fun t => -(S.theta u t)^2 / (S.r u t * S.lam u t))
    (g := S.lam u) (y := fun t => S.r u t - 2 * S.m u t)
    huv hc hgapAxis
  · intro a d hua had hdv
    exact mass_gap_local_linear_equation_of_c1 H hp hua had hdv
  · intro t hut htv
    have htU := H.solution.development.outgoing_mem hp hut htv
    have hr := H.solution.radius_pos (u, t) htU
    have hl := H.solution.lam_pos (u, t) htU
    simpa only [neg_div] using
      (neg_nonpos.mpr (div_nonneg (sq_nonneg (S.theta u t))
        (mul_nonneg hr.le hl.le)))
  · intro t hut htv
    exact hlam (u, t) (H.solution.development.outgoing_mem hp hut htv)

/-- The mass ratio is strictly below one on any C¹ development. -/
theorem mass_ratio_lt_one_of_c1_domain
    {U : Set (ℝ × ℝ)} {S : Fields} (H : IsC1Solution U S)
    {u v : ℝ} (hp : (u, v) ∈ U) :
    2 * S.m u v / S.r u v < 1 := by
  have hr := H.solution.radius_pos (u, v) hp
  apply (div_lt_iff₀ hr).2
  linarith only [mass_gap_pos_of_c1_domain H hp]

end ChristodoulouBV.Uniqueness

end
