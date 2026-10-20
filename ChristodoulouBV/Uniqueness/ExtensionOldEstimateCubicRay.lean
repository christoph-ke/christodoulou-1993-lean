module

public import ChristodoulouBV.Uniqueness.ExtensionOldEstimateLinear
public import ChristodoulouBV.Uniqueness.ExtensionCubicInequality
public import ChristodoulouBV.Uniqueness.ExtensionCutoff
import ChristodoulouBV.BVSolution.AxisTraces
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Cubic estimates on a finite outgoing ray

The radius coordinate and both estimates for the inputs of (5.7) are
constructed on a finite cutoff. The arbitrary bound `A` applies only to
weighted values on that cutoff.
-/

public section

open Set MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

private theorem finite_ray_radius_hasDerivAt
    {b B u t : ℝ} (hu : 0 < u) (hut : u < t) (htB : t < B)
    (hBb : B < b) {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {v : ℝ} (hv : v ∈ Ioo u t) :
    HasDerivAt (fun w => C1Solution.canonicalRadius S (u, w))
      (S.lam u v) v := by
  let R : ℝ → ℝ := fun w => C1Solution.canonicalRadius S (u, w)
  let L : ℝ → ℝ := fun w => S.lam u w
  have hB : 0 < B := hu.trans (hut.trans htB)
  have hmap : MapsTo (fun w : ℝ => (u, w)) (Icc u t)
      (closedCoordTriangle 0 B) := by
    intro w hw
    exact ⟨hu.le, hw.1, hw.2.trans htB.le⟩
  have hL : ContinuousOn L (Icc u t) :=
    (C1Solution.five_fields_contDiffOn hB hBb H).1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap
  have hLint : IntervalIntegrable L volume u v :=
    (hL.mono (Icc_subset_Icc le_rfl hv.2.le)).intervalIntegrable_of_Icc hv.1.le
  have hLat : ContinuousAt L v := hL.continuousAt (Icc_mem_nhds hv.1 hv.2)
  have hMeas : StronglyMeasurableAtFilter L (𝓝 v) :=
    (hL.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo v hv
  have hFTC := intervalIntegral.integral_hasDerivAt_right hLint hMeas hLat
  change HasDerivAt R (L v) v at hFTC
  exact hFTC

private theorem finite_ray_radius_exists
    {b B u t : ℝ} (hu : 0 < u) (hut : u < t) (htB : t < B)
    (hBb : B < b) {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {x : ℝ} (hx : x ∈ Ioo 0 (S.r u t)) :
    ∃ v ∈ Ioo u t, C1Solution.canonicalRadius S (u, v) = x := by
  obtain ⟨hRc1, hRmono, hR0⟩ :=
    finite_cutoff_radius_strictMonoOn hu.le hut htB hBb H
  have hRt : C1Solution.canonicalRadius S (u, t) = S.r u t :=
    C1Solution.canonicalRadius_eq_radius
      (hu.trans (hut.trans htB)) hBb H hu.le hut htB.le
  have hxImage : x ∈ (fun v => C1Solution.canonicalRadius S (u, v)) '' Icc u t := by
    apply intermediate_value_Icc hut.le hRc1.continuousOn
    rw [hR0, hRt]
    exact ⟨hx.1.le, hx.2.le⟩
  obtain ⟨v, hv, hvx⟩ := hxImage
  change C1Solution.canonicalRadius S (u, v) = x at hvx
  have hvu : u < v := by
    rcases eq_or_lt_of_le hv.1 with h | h
    · subst v; rw [hR0] at hvx
      exact (ne_of_gt hx.1) hvx.symm |>.elim
    · exact h
  have hvt : v < t := by
    rcases eq_or_lt_of_le hv.2 with h | h
    · subst v; rw [hRt] at hvx
      exact (ne_of_gt hx.2) hvx |>.elim
    · exact h
  exact ⟨v, ⟨hvu, hvt⟩, hvx⟩

/-- The energy average in (5.7) is bounded by the mass ratio on a finite
outgoing ray. The BV mass formula supplies the axis endpoint of the mass
integral, and the canonical radius supplies the change of variables. -/
theorem cubic_a_le_mass_ratio
    {b B u t ε : ℝ} (hu : 0 < u) (hut : u < t)
    (htB : t < B) (hBb : B < b) (hε : ε < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Icc 0 (S.r u t)))
    (hfQ : ∀ v ∈ Ioc u t,
      f (S.r u v) = S.theta u v / S.lam u v)
    (hμ : ∀ v ∈ Ioc u t,
      2 * S.m u v / S.r u v ≤ ε) :
    ∀ x ∈ Ioc 0 (S.r u t),
      (∫ z in 0..x, (f z)^2) / x ≤ ε / (1 - ε) := by
  intro x hx
  obtain ⟨hRc1, _, hR0⟩ :=
    finite_cutoff_radius_strictMonoOn hu.le hut htB hBb H
  have hRt : C1Solution.canonicalRadius S (u, t) = S.r u t :=
    C1Solution.canonicalRadius_eq_radius
      (hu.trans (hut.trans htB)) hBb H hu.le hut htB.le
  have hxImage : x ∈ (fun v => C1Solution.canonicalRadius S (u, v)) '' Icc u t := by
    apply intermediate_value_Icc hut.le hRc1.continuousOn
    rw [hR0, hRt]
    exact ⟨hx.1.le, hx.2⟩
  obtain ⟨v, hv, hvx⟩ := hxImage
  change C1Solution.canonicalRadius S (u, v) = x at hvx
  have hvu : u < v := by
    rcases eq_or_lt_of_le hv.1 with h | h
    · subst v; rw [hR0] at hvx
      exact (ne_of_gt hx.1) hvx.symm |>.elim
    · exact h
  have hvb : v < b := hv.2.trans_lt (htB.trans hBb)
  have hp : (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hu.le, hvu, hvb⟩
  have hr : 0 < S.r u v := H.solution.radius_pos (u, v) hp
  have hrv : C1Solution.canonicalRadius S (u, v) = S.r u v :=
    C1Solution.canonicalRadius_eq_radius
      (hu.trans (hut.trans htB)) hBb H hu.le hvu (le_trans hv.2 htB.le)
  have hxR : x = S.r u v := hvx.symm.trans hrv
  let R : ℝ → ℝ := fun w => C1Solution.canonicalRadius S (u, w)
  let L : ℝ → ℝ := fun w => S.lam u w
  let F : ℝ → ℝ := fun w => L w * (f (R w))^2
  let M : ℝ → ℝ := fun w => (2 / (1 - ε)) * IsBVSolution.massV S u w
  have hRcont : ContinuousOn R (Icc u v) :=
    hRc1.continuousOn.mono (Icc_subset_Icc le_rfl hv.2)
  have hLcont : ContinuousOn L (Icc u v) := by
    have hmap : MapsTo (fun w : ℝ => (u, w)) (Icc u v)
        (closedCoordTriangle 0 B) := by
      intro w hw
      exact ⟨hu.le, hw.1, le_trans hw.2 (le_trans hv.2 htB.le)⟩
    exact (C1Solution.five_fields_contDiffOn
      (hu.trans (hut.trans htB)) hBb H).1.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn hmap
  have hRrange : MapsTo R (Icc u v) (Icc 0 (S.r u t)) := by
    intro w hw
    have hRmono := (finite_cutoff_radius_strictMonoOn hu.le hut htB hBb H).2.1
    have hwT : w ∈ Icc u t := ⟨hw.1, hw.2.trans hv.2⟩
    constructor
    · have h := hRmono.monotoneOn (left_mem_Icc.mpr hut.le) hwT hw.1
      simpa only [R, hR0] using h
    · have h := hRmono.monotoneOn hwT (right_mem_Icc.mpr hut.le) hwT.2
      simpa only [R, hRt] using h
  have hFint : IntervalIntegrable F volume u v := by
    have hfc := (hf.continuousOn.comp hRcont hRrange).pow 2
    exact (hLcont.mul hfc).intervalIntegrable_of_Icc hvu.le
  have hBV := H.isBVSolution_development (hu.trans (hut.trans (htB.trans hBb)))
  have hMassInt : IntervalIntegrable (IsBVSolution.massV S u) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hvu.le).2
      (hBV.mass_density_integrable_on_axis_slice hp)
  have hMint : IntervalIntegrable M volume u v := hMassInt.const_mul _
  have hpoint : ∀ w ∈ Ioo u v, F w ≤ M w := by
    intro w hw
    have hwt : w ∈ Ioc u t := ⟨hw.1, hw.2.le.trans hv.2⟩
    have hwp : (u, w) ∈ developmentWithInitialEdge b :=
      ⟨hu.le, hw.1, hw.2.trans hvb⟩
    have hrw : 0 < S.r u w := H.solution.radius_pos (u, w) hwp
    have hlw : 0 < S.lam u w := H.solution.lam_pos (u, w) hwp
    have hμw := hμ w hwt
    have hden : 0 < 1 - ε := by linarith
    have hRw : R w = S.r u w :=
      C1Solution.canonicalRadius_eq_radius
        (hu.trans (hut.trans htB)) hBb H hu.le hw.1 (le_trans hwt.2 htB.le)
    have hF : F w = (S.theta u w)^2 / S.lam u w := by
      dsimp [F, L]
      rw [hRw, hfQ w hwt]
      field_simp
    have hM : IsBVSolution.massV S u w =
        (1 - 2 * S.m u w / S.r u w) *
          (S.theta u w)^2 / (2 * S.lam u w) := rfl
    have hTnonneg : 0 ≤ (S.theta u w)^2 / S.lam u w :=
      div_nonneg (sq_nonneg _) hlw.le
    rw [hF]
    dsimp [M]
    rw [hM]
    have hbase : ((S.theta u w)^2 / S.lam u w) * (1 - ε) ≤
        (1 - 2 * S.m u w / S.r u w) *
          ((S.theta u w)^2 / S.lam u w) := by
      nlinarith [mul_le_mul_of_nonneg_right
        (show 1 - ε ≤ 1 - 2 * S.m u w / S.r u w by linarith)
        hTnonneg]
    calc
      (S.theta u w)^2 / S.lam u w ≤
          ((1 - 2 * S.m u w / S.r u w) *
            ((S.theta u w)^2 / S.lam u w)) / (1 - ε) :=
        (le_div_iff₀ hden).2 hbase
      _ = (2 / (1 - ε)) *
          ((1 - 2 * S.m u w / S.r u w) *
            (S.theta u w)^2 / (2 * S.lam u w)) := by
        field_simp
  have hcomp := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a := u) (b := v) (f := R) (f' := L) (g := fun z => (f z)^2)
    (by simpa only [uIcc_of_le hvu.le] using hRcont) (fun w hw => by
      have hw' : w ∈ Ioo u v := by
        simpa only [min_eq_left hvu.le, max_eq_right hvu.le] using hw
      exact finite_ray_radius_hasDerivAt hu hut htB hBb H
        ⟨hw'.1, hw'.2.trans_le hv.2⟩)
    (fun w hw => by
      have hw' : w ∈ Ioo u v := by
        simpa only [min_eq_left hvu.le, max_eq_right hvu.le] using hw
      exact (H.solution.lam_pos (u, w)
        ⟨hu.le, hw'.1, hw'.2.trans hvb⟩).le)
  have hcomp' : (∫ w in u..v, F w) = ∫ z in 0..x, (f z)^2 := by
    simpa only [R, L, F, Function.comp_apply, smul_eq_mul, hR0, hvx,
      mul_comm] using hcomp
  have hbound : (∫ z in 0..x, (f z)^2) ≤
      (2 / (1 - ε)) * S.m u v := by
    rw [← hcomp']
    calc
      (∫ w in u..v, F w) ≤ ∫ w in u..v, M w :=
        intervalIntegral.integral_mono_on_of_le_Ioo hvu.le hFint hMint hpoint
      _ = (2 / (1 - ε)) * S.m u v := by
        rw [intervalIntegral.integral_const_mul, ← hBV.mass_out_integral_from_axis hp]
  have hμv := hμ v ⟨hvu, hv.2⟩
  have hden : 0 < 1 - ε := by linarith
  rw [hxR] at hbound ⊢
  apply (div_le_iff₀ hr).2
  have hmBound : 2 * S.m u v ≤ ε * S.r u v :=
    (div_le_iff₀ hr).mp hμv
  have hfactor : (2 / (1 - ε)) * S.m u v ≤
      (ε / (1 - ε)) * S.r u v := by
    calc
      (2 / (1 - ε)) * S.m u v =
          (2 * S.m u v) / (1 - ε) := by ring
      _ ≤ (ε * S.r u v) / (1 - ε) :=
        div_le_div_of_nonneg_right hmBound hden.le
      _ = (ε / (1 - ε)) * S.r u v := by ring
  exact hbound.trans hfactor

/-- The weighted radial derivative of the quotient in (5.7) is bounded by
`(3-δ)/(2-δ)` times the finite weighted `α′` bound. -/
theorem cubic_b_le_weightedAlphaPrime
    {b B u t δ A : ℝ} (hu : 0 < u) (hut : u < t)
    (htB : t < B) (hBb : B < b)
    (hδ : 0 < δ) (hδ1 : δ < 1) {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Icc 0 (S.r u t)))
    (hfQ : ∀ v ∈ Ioc u t,
      f (S.r u v) = S.theta u v / S.lam u v)
    (hA : ∀ v ∈ Ioc u t,
      (S.r u v) ^ δ *
        |deriv (fun w => S.alpha u w / S.lam u w) v / S.lam u v| ≤ A) :
    ∀ x ∈ Ioo 0 (S.r u t),
      x^δ * |deriv f x| ≤ (3 - δ) / (2 - δ) * A := by
  intro x hx
  obtain ⟨v, hv, hvx⟩ := finite_ray_radius_exists hu hut htB hBb H hx
  have hvb : v < b := hv.2.trans (htB.trans hBb)
  have hp : (u, v) ∈ openDevelopment 0 b :=
    ⟨⟨hu, hv.1.trans hvb⟩, ⟨hv.1, hvb⟩⟩
  have hr : 0 < S.r u v := H.solution.radius_pos (u, v)
    ⟨hu.le, hv.1, hvb⟩
  have hl : 0 < S.lam u v := H.solution.lam_pos (u, v)
    ⟨hu.le, hv.1, hvb⟩
  have hReq : C1Solution.canonicalRadius S (u, v) = S.r u v :=
    C1Solution.canonicalRadius_eq_radius
      (hu.trans (hut.trans htB)) hBb H hu.le hv.1 (le_trans hv.2.le htB.le)
  have hxR : x = S.r u v := by rw [← hReq, hvx]
  have hRderiv := finite_ray_radius_hasDerivAt hu hut htB hBb H hv
  have hFderiv : HasDerivAt f (deriv f x) x :=
    (hf.differentiableOn (by norm_num)) x ⟨hx.1.le, hx.2.le⟩ |>.differentiableAt
      (Icc_mem_nhds hx.1 hx.2) |>.hasDerivAt
  have hQnear :
      (fun w => f (C1Solution.canonicalRadius S (u, w))) =ᶠ[𝓝 v]
        (fun w => S.theta u w / S.lam u w) := by
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with w hw
    have hRw : C1Solution.canonicalRadius S (u, w) = S.r u w :=
      C1Solution.canonicalRadius_eq_radius
        (hu.trans (hut.trans htB)) hBb H hu.le hw.1 (le_trans hw.2.le htB.le)
    rw [hRw, hfQ w ⟨hw.1, hw.2.le⟩]
  have hchain : deriv (fun w => S.theta u w / S.lam u w) v =
      deriv f x * S.lam u v := by
    have hFderiv' : HasDerivAt f (deriv f x)
        (C1Solution.canonicalRadius S (u, v)) := by
      rw [hvx]
      exact hFderiv
    have h := (hFderiv'.comp v hRderiv).congr_of_eventuallyEq (by
      simpa only [Function.comp_def] using hQnear.symm)
    exact h.deriv
  have hα := alpha_ratio_deriv_v H hp
  have hrad : deriv f x =
      deriv (fun w => S.alpha u w / S.lam u w) v / S.lam u v -
        (S.theta u v / S.lam u v) / S.r u v := by
    rw [hchain] at hα
    have hrel : S.theta u v / S.r u v =
        S.lam u v * ((S.theta u v / S.lam u v) / S.r u v) := by
      field_simp [hl.ne', hr.ne']
    rw [hrel] at hα
    apply (eq_sub_iff_add_eq).2
    apply (eq_div_iff hl.ne').2
    rw [add_mul]
    linear_combination -hα
  have hθ := theta_ratio_le_weightedAlphaPrime H hu hv.1 hvb
    hδ hδ1 (fun w hw => hA w ⟨hw.1, hw.2.trans hv.2.le⟩)
  have hA0 : 0 ≤ A :=
    (mul_nonneg (Real.rpow_nonneg hr.le _) (abs_nonneg _)).trans
      (hA v ⟨hv.1, hv.2.le⟩)
  have hpow : (S.r u v)^δ * (S.r u v)^(1 - δ) / S.r u v = 1 := by
    rw [← Real.rpow_add hr]
    have heq : δ + (1 - δ) = (1 : ℝ) := by ring
    rw [heq, Real.rpow_one]
    field_simp
  have hθbound : (S.r u v)^δ * |(S.theta u v / S.lam u v) / S.r u v| ≤
      A / (2 - δ) := by
    rw [abs_div, abs_of_pos hr]
    calc
      (S.r u v)^δ * (|S.theta u v / S.lam u v| / S.r u v)
          ≤ (S.r u v)^δ * ((A / (2 - δ) * (S.r u v)^(1 - δ)) /
              S.r u v) := by
                gcongr
      _ = A / (2 - δ) := by
        calc
          _ = (A / (2 - δ)) *
              ((S.r u v)^δ * (S.r u v)^(1 - δ) / S.r u v) := by ring
          _ = A / (2 - δ) := by rw [hpow, mul_one]
  rw [hrad, hxR]
  have htriangle :
      |deriv (fun w => S.alpha u w / S.lam u w) v / S.lam u v -
        (S.theta u v / S.lam u v) / S.r u v| ≤
      |deriv (fun w => S.alpha u w / S.lam u w) v / S.lam u v| +
        |(S.theta u v / S.lam u v) / S.r u v| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      abs_sub_le (deriv (fun w => S.alpha u w / S.lam u w) v / S.lam u v)
        (0 : ℝ) ((S.theta u v / S.lam u v) / S.r u v)
  have htotal : (S.r u v)^δ *
      |deriv (fun w => S.alpha u w / S.lam u w) v / S.lam u v -
        (S.theta u v / S.lam u v) / S.r u v| ≤ A + A / (2 - δ) := by
    calc
      _ ≤ (S.r u v)^δ *
        (|deriv (fun w => S.alpha u w / S.lam u w) v / S.lam u v| +
          |(S.theta u v / S.lam u v) / S.r u v|) :=
            mul_le_mul_of_nonneg_left htriangle (Real.rpow_nonneg hr.le _)
      _ = (S.r u v)^δ *
            |deriv (fun w => S.alpha u w / S.lam u w) v / S.lam u v| +
          (S.r u v)^δ * |(S.theta u v / S.lam u v) / S.r u v| := by ring
      _ ≤ A + A / (2 - δ) := add_le_add (hA v ⟨hv.1, hv.2.le⟩) hθbound
  calc
    _ ≤ A + A / (2 - δ) := htotal
    _ = (3 - δ) / (2 - δ) * A := by
      have hden : 2 - δ ≠ 0 := by linarith
      field_simp
      ring

/-- Equation (5.8) on a finite outgoing ray. Every weighted `α′` value
needed in the radius argument is bounded by the same arbitrary `A`. -/
theorem theta_ratio_cubic_le
    {b B u t δ ε A : ℝ} (hu : 0 < u) (hut : u < t)
    (htB : t < B) (hBb : B < b)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : ε < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hμ : ∀ v ∈ Ioc u t,
      2 * S.m u v / S.r u v ≤ ε)
    (hA : ∀ v ∈ Ioc u t,
      (S.r u v) ^ δ *
        |deriv (fun w => S.alpha u w / S.lam u w) v / S.lam u v| ≤ A) :
    ∀ v ∈ Ioc u t,
      |S.theta u v / S.lam u v|^3 ≤
        (3 * (3 - δ) / ((1 - δ) * (2 - δ))) *
          (ε / (1 - ε)) * A * (S.r u v)^(1 - δ) := by
  obtain ⟨f, hf, hf0, _, hfQ⟩ :=
    exists_finite_cutoff_radius_reparam hu hut htB hBb H
  have hr : 0 < S.r u t := H.solution.radius_pos (u, t)
    ⟨hu.le, hut, htB.trans hBb⟩
  have hε0 : 0 ≤ ε := by
    have hμ0 := H.mass_ratio_nonneg_of_c1
      (p := (u, t)) ⟨hu.le, hut, htB.trans hBb⟩
    exact hμ0.trans (hμ t (right_mem_Ioc.mpr hut))
  have hA0 : 0 ≤ A :=
    (mul_nonneg (Real.rpow_nonneg hr.le _) (abs_nonneg _)).trans
      (hA t (right_mem_Ioc.mpr hut))
  have ha : 0 ≤ ε / (1 - ε) :=
    div_nonneg hε0 (by linarith : 0 ≤ 1 - ε)
  have hb : 0 ≤ (3 - δ) / (2 - δ) * A :=
    mul_nonneg (div_nonneg (by linarith) (by linarith)) hA0
  have hcubic := cubic_weighted_interval_bound hδ hδ1 hr.le ha hb
    hf hf0 (cubic_a_le_mass_ratio hu hut htB hBb hε H hf hfQ hμ)
    (cubic_b_le_weightedAlphaPrime hu hut htB hBb hδ hδ1 H hf hfQ hA)
  intro v hv
  have hrv : 0 < S.r u v := H.solution.radius_pos (u, v)
    ⟨hu.le, hv.1, hv.2.trans_lt (htB.trans hBb)⟩
  have hRle : S.r u v ≤ S.r u t := by
    have hmono := (finite_cutoff_radius_strictMonoOn hu.le hut htB hBb H).2.1
    have hrv' := hmono.monotoneOn ⟨hv.1.le, hv.2⟩
      (right_mem_Icc.mpr hut.le) hv.2
    rw [C1Solution.canonicalRadius_eq_radius
      (hu.trans (hut.trans htB)) hBb H hu.le hv.1 (le_trans hv.2 htB.le),
      C1Solution.canonicalRadius_eq_radius
        (hu.trans (hut.trans htB)) hBb H hu.le hut htB.le] at hrv'
    exact hrv'
  have h := hcubic (S.r u v) ⟨hrv.le, hRle⟩
  rw [hfQ v hv] at h
  calc
    _ ≤ 3 * (ε / (1 - ε)) * ((3 - δ) / (2 - δ) * A) *
        (S.r u v)^(1 - δ) / (1 - δ) := h
    _ = (3 * (3 - δ) / ((1 - δ) * (2 - δ))) *
        (ε / (1 - ε)) * A * (S.r u v)^(1 - δ) := by
      have hden1 : 1 - δ ≠ 0 := by linarith
      have hden2 : 2 - δ ≠ 0 := by linarith
      field_simp

end ChristodoulouBV.Uniqueness

end
