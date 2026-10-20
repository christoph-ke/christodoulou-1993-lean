module

public import ChristodoulouBV.Uniqueness.ExtensionOldEstimateLinear
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import ChristodoulouBV.ForMathlib.Analysis.Calculus.MixedPartial
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Unweighted outgoing scalar averaging

The zero-weight version of (5.5) converts a uniform bound on `α′` into a
linear-in-radius bound for `θ/λ`. This version keeps the endpoint at the axis.
-/

public section

open Set MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- If `|α′| ≤ B` along an outgoing ray, then the quotient `θ/λ` is at most
`B r/2`. This is (5.5) at weight zero. -/
theorem theta_ratio_le_half_radius_of_alphaPrime_bound
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v B : ℝ} (hu : 0 < u) (huv : u < v) (hvb : v < b)
    (_hB : 0 ≤ B)
    (hprime : ∀ s ∈ Ioc u v,
      |deriv (fun t => S.alpha u t / S.lam u t) s / S.lam u s| ≤ B) :
    |S.theta u v / S.lam u v| ≤ B / 2 * S.r u v := by
  let W := (v + b) / 2
  let K := closedCoordTriangle 0 W
  let R : ℝ → ℝ := fun s => C1Solution.canonicalRadius S (u, s)
  let Q : ℝ → ℝ := fun s => S.alpha u s / S.lam u s
  let L : ℝ → ℝ := fun s => S.lam u s
  have hW : 0 < W := by dsimp [W]; linarith
  have hWb : W < b := by dsimp [W]; linarith
  have hvW : v < W := by dsimp [W]; linarith
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Icc u v) K := by
    intro s hs
    exact ⟨hu.le, hs.1, hs.2.trans hvW.le⟩
  have hRc1 : ContDiffOn ℝ 1 R (Icc u v) :=
    (C1Solution.canonicalRadius_contDiffOn hW hWb H).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn hmap
  have hQc1 : ContDiffOn ℝ 1 Q (Icc u v) :=
    (C1Solution.alpha_div_lam_contDiffOn hW hWb H).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn hmap
  have hL : ContinuousOn L (Icc u v) :=
    (C1Solution.five_fields_contDiffOn hW hWb H).1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap
  have hR0 : R u = 0 := (C1Solution.canonical_outgoing_axis S u).1
  have hReq : ∀ s ∈ Ioc u v, R s = S.r u s := by
    intro s hs
    exact C1Solution.canonicalRadius_eq_radius hW hWb H hu.le hs.1
      (hs.2.trans hvW.le)
  have hRderiv : ∀ s ∈ Ioo u v, HasDerivAt R (L s) s := by
    intro s hs
    have hLint : IntervalIntegrable L volume u s :=
      (hL.mono (Icc_subset_Icc le_rfl hs.2.le)).intervalIntegrable_of_Icc hs.1.le
    have hLat : ContinuousAt L s := hL.continuousAt (Icc_mem_nhds hs.1 hs.2)
    have hMeas : StronglyMeasurableAtFilter L (𝓝 s) :=
      (hL.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs
    have hFTC := intervalIntegral.integral_hasDerivAt_right hLint hMeas hLat
    change HasDerivAt R (L s) s at hFTC
    exact hFTC
  have hRAC : AbsolutelyContinuousOnInterval R u v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le huv.le] using hRc1
  have hQAC : AbsolutelyContinuousOnInterval Q u v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le huv.le] using hQc1
  have hRderivEq : ∀ s ∈ Ioo u v, deriv R s = L s :=
    fun s hs => (hRderiv s hs).deriv
  have hαInt : (∫ s in u..v, deriv R s * Q s) =
      ∫ s in u..v, S.alpha u s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume v] with s hne hs
    have hsIoc : s ∈ Ioc u v := by simpa only [uIoc_of_le huv.le] using hs
    have hs' : s ∈ Ioo u v := ⟨hsIoc.1, lt_of_le_of_ne hsIoc.2 hne⟩
    rw [hRderivEq s hs']
    dsimp [L, Q]
    have hlam : S.lam u s ≠ 0 := ne_of_gt
      (H.solution.lam_pos (u, s) ⟨hu.le, hs'.1, hs'.2.trans hvb⟩)
    field_simp [hlam]
  have hIBP := hRAC.integral_mul_deriv_eq_deriv_mul hQAC
  have hIBP' : (∫ s in u..v, R s * deriv Q s) =
      S.r u v * Q v - ∫ s in u..v, S.alpha u s := by
    rw [hReq v (right_mem_Ioc.mpr huv), hR0, zero_mul, sub_zero, hαInt] at hIBP
    exact hIBP
  have hp : (u, v) ∈ developmentWithInitialEdge b := ⟨hu.le, huv, hvb⟩
  have hr := H.solution.radius_pos (u, v) hp
  have htheta : S.theta u v / S.lam u v =
      (∫ s in u..v, R s * deriv Q s) / S.r u v := by
    rw [theta_ratio_axis_identity H hp, hIBP']
    dsimp [Q]
    field_simp [hr.ne']
  have hR2C : ContinuousOn (fun s => R s ^ 2) (Icc u v) := hRc1.continuousOn.pow 2
  have hRL : ContinuousOn (fun s => R s * L s) (Icc u v) :=
    hRc1.continuousOn.mul hL
  have hRLInt : IntervalIntegrable (fun s => R s * L s) volume u v :=
    hRL.intervalIntegrable_of_Icc huv.le
  have hR2deriv : ∀ s ∈ Ioo u v,
      HasDerivAt (fun t => R t ^ 2) (2 * R s * L s) s := by
    intro s hs
    convert (hRderiv s hs).pow 2 using 1
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_continuousOn_hasDerivAt
    huv.le hR2C ((continuousOn_const.mul hRc1.continuousOn).mul hL)
    hR2deriv
  have hFTC' : (∫ s in u..v, 2 * R s * L s) =
      R v ^ 2 - R u ^ 2 := by
    simpa only [Pi.mul_apply] using hFTC
  have hradial : (∫ s in u..v, R s * L s) = (S.r u v) ^ 2 / 2 := by
    have heq : (fun s => R s * L s) = fun s => (1 / 2 : ℝ) * (2 * R s * L s) := by
      funext s; ring
    rw [heq, intervalIntegral.integral_const_mul, hFTC', hR0,
      hReq v (right_mem_Ioc.mpr huv)]
    ring
  have hmaj : ∀ᵐ s : ℝ, s ∈ Ioc u v →
      ‖R s * deriv Q s‖ ≤ B * (R s * L s) := by
    filter_upwards [Measure.ae_ne volume v] with s hne hsIoc
    have hs : s ∈ Ioo u v := ⟨hsIoc.1, lt_of_le_of_ne hsIoc.2 hne⟩
    have hr_s := H.solution.radius_pos (u, s)
      ⟨hu.le, hs.1, hs.2.trans hvb⟩
    have hlam := H.solution.lam_pos (u, s)
      ⟨hu.le, hs.1, hs.2.trans hvb⟩
    have hbound := hprime s hsIoc
    have hQprime : deriv Q s = L s *
        (deriv Q s / L s) := by
      dsimp [L]
      field_simp [hlam.ne']
    rw [hQprime, Real.norm_eq_abs, abs_mul,
      hReq s hsIoc, abs_of_pos hr_s, abs_mul, abs_of_pos hlam]
    calc
      S.r u s * (L s * |deriv Q s / L s|) =
          (S.r u s * L s) * |deriv Q s / L s| := by ring
      _ ≤ (S.r u s * L s) * B :=
        mul_le_mul_of_nonneg_left hbound
          (mul_nonneg hr_s.le hlam.le)
      _ = B * (S.r u s * L s) := mul_comm _ _
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le huv.le hmaj
    (hRLInt.const_mul B)
  have hIntBound : |∫ s in u..v, R s * deriv Q s| ≤
      B * ((S.r u v) ^ 2 / 2) := by
    simpa only [Real.norm_eq_abs, intervalIntegral.integral_const_mul, hradial]
      using hnorm
  rw [htheta, abs_div, abs_of_pos hr]
  have hdiv := div_le_div_of_nonneg_right hIntBound hr.le
  calc
    |∫ s in u..v, R s * deriv Q s| / S.r u v ≤
        (B * ((S.r u v) ^ 2 / 2)) / S.r u v := hdiv
    _ = B / 2 * S.r u v := by field_simp

end ChristodoulouBV.Uniqueness

end
