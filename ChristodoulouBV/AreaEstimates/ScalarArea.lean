module

public import ChristodoulouBV.AreaEstimates.ScalarAreaDensity
import Mathlib.Tactic

/-!
# Scalar quotient area inequalities (4.16) and (4.18)

The source's four areas are interpreted as smooth analytic Jacobian areas on
the strict unit triangle. The explicit coefficients below are universal and
do not depend on the solution or the initial variation.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace ChristodoulouBV

/-- Equation (4.16): the area of `(φ, α/λ)` is controlled by the incoming
null size `Y`, initial variation `D`, and the area of `(λ, φ)`. The universal
source constant `c` is instantiated by `45`. -/
theorem eq4_16 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    smoothAnalyticArea (sourcePhiAlphaLamMap S) (openCoordTriangle 0 1) ≤
      45 * (sourceD S * sourceY S) +
        45 * (sourceY S + sourceD S) *
          smoothAnalyticArea (sourceLamPhiMap S) (openCoordTriangle 0 1) := by
  let T := openCoordTriangle 0 1
  let A := smoothAnalyticArea (sourceLamPhiMap S) T
  let W := sourceIncomingWeight S
  let F := sourceAlphaMajorantMeasurable S
  let J : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal |(fderiv ℝ (sourcePhiAlphaLamMap S) p).det|
  let K : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal |(fderiv ℝ (sourceLamPhiMap S) p).det|
  have hT : MeasurableSet T := by
    change MeasurableSet (openCoordTriangle 0 1)
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior.measurableSet
  obtain ⟨hW, hWs, hY⟩ := sourceIncomingWeight_fibers H
  have hF : Measurable F := sourceAlphaMajorantMeasurable_measurable S
  have hK : AEMeasurable K (volume.restrict T) :=
    (sourceLamPhiDensity_measurable S).aemeasurable
  have hpoint : ∀ p ∈ T,
      J p ≤ 3 * (W p * F p.2) +
        (45 * ENNReal.ofReal (sourceD S).toReal) * K p := by
    intro p hp
    exact source_alpha_area_density_le H hr hcenter hboot hp
  have hFint : (∫⁻ v in Ioo (0 : ℝ) 1, F v) ≤ sourceD S + A :=
    sourceAlphaMajorantMeasurable_integral_le H hr hcenter hboot
  have hKint : (∫⁻ p in T, K p) = A :=
    (smooth_analytic_area (sourceLamPhiMap S) hT).symm
  have hraw := scalar_area_weighted_bound W J K F
    3 (45 * ENNReal.ofReal (sourceD S).toReal)
    (sourceY S) (sourceD S) A hW hF hK hWs hY
    hpoint hFint hKint
  have hD : ENNReal.ofReal (sourceD S).toReal = sourceD S :=
    ENNReal.ofReal_toReal (sourceD_ne_top_unit H)
  rw [hD] at hraw
  have hA : smoothAnalyticArea (sourcePhiAlphaLamMap S) T =
      ∫⁻ p in T, J p := smooth_analytic_area _ hT
  rw [hA]
  calc
    (∫⁻ p in T, J p) ≤
        3 * (sourceY S * (sourceD S + A)) +
          (45 * sourceD S) * A := hraw
    _ ≤ 45 * (sourceY S * (sourceD S + A)) +
          (45 * sourceD S) * A := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ≥0∞) ≤ 45) bot_le)
        le_rfl
    _ = 45 * (sourceD S * sourceY S) +
          45 * (sourceY S + sourceD S) * A := by ring

/-- Equation (4.18): the area of `(φ, β/ν)` is controlled by the outgoing
null size `X`, the two axis variations, and the area of `(ν, φ)`. The source's
universal constants are instantiated by `72` and `6`. -/
theorem eq4_18 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    smoothAnalyticArea (sourcePhiBetaNuMap S) (openCoordTriangle 0 1) ≤
      72 * sourceX S *
        (eVariationOn (fun t => S.beta t t) (Ioo 0 1) +
          6 * sourceD S *
            eVariationOn (fun t => S.nu t t) (Ioo 0 1)) +
        72 * (sourceX S + sourceD S) *
          smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 1) := by
  let T := openCoordTriangle 0 1
  let A := smoothAnalyticArea (sourceNuPhiMap S) T
  let V := eVariationOn (fun t => S.beta t t) (Ioo 0 1) +
    6 * sourceD S * eVariationOn (fun t => S.nu t t) (Ioo 0 1)
  let W := sourceOutgoingWeight S
  let F := sourceBetaMajorantMeasurable S
  let J : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal |(fderiv ℝ (sourcePhiBetaNuMap S) p).det|
  let K : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal |(fderiv ℝ (sourceNuPhiMap S) p).det|
  have hT : MeasurableSet T := by
    change MeasurableSet (openCoordTriangle 0 1)
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior.measurableSet
  obtain ⟨hW, hWs, hX⟩ := sourceOutgoingWeight_fibers H
  have hF : Measurable F := sourceBetaMajorantMeasurable_measurable S
  have hK : AEMeasurable K (volume.restrict T) :=
    (sourceNuPhiDensity_measurable S).aemeasurable
  have hpoint : ∀ p ∈ T,
      J p ≤ 3 * (W p * F p.1) +
        (72 * ENNReal.ofReal (sourceD S).toReal) * K p := by
    intro p hp
    exact source_beta_area_density_le H hr hcenter hboot hp
  have hD : ENNReal.ofReal (sourceD S).toReal = sourceD S :=
    ENNReal.ofReal_toReal (sourceD_ne_top_unit H)
  have hFint : (∫⁻ u in Ioo (0 : ℝ) 1, F u) ≤ V + A := by
    rw [sourceBetaMajorantMeasurable_integral H,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6), hD]
    simp only [ENNReal.ofReal_ofNat]
    change V + A ≤ V + A
    exact le_rfl
  have hKint : (∫⁻ p in T, K p) = A :=
    (smooth_analytic_area (sourceNuPhiMap S) hT).symm
  have hraw := scalar_area_weighted_bound_outgoing W J K F
    3 (72 * ENNReal.ofReal (sourceD S).toReal)
    (sourceX S) V A hW hF hK hWs hX
    hpoint hFint hKint
  rw [hD] at hraw
  have hA : smoothAnalyticArea (sourcePhiBetaNuMap S) T =
      ∫⁻ p in T, J p := smooth_analytic_area _ hT
  rw [hA]
  calc
    (∫⁻ p in T, J p) ≤
        3 * (sourceX S * (V + A)) +
          (72 * sourceD S) * A := hraw
    _ ≤ 72 * (sourceX S * (V + A)) +
          (72 * sourceD S) * A := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ≥0∞) ≤ 72) bot_le)
        le_rfl
    _ = 72 * sourceX S * V +
          72 * (sourceX S + sourceD S) * A := by ring

end ChristodoulouBV

end
