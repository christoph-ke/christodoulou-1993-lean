module

public import ChristodoulouBV.AreaEstimates.OutgoingAreaDensity
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# The two Jacobian area estimates before rho integration

The incoming logarithmic residual has the corrected `- f*` sign from the
sign correction of (4.11b)–(4.13b) and its extension to the area estimates;
see ERRATA.md, ERR-23.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace ChristodoulouBV

/-- Equation (4.21), with universal constants `108`, `108`, and `39`.
The last term is the rho area that is estimated in (4.23). -/
theorem eq4_21 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    smoothAnalyticArea (sourceLamPhiMap S) (openCoordTriangle 0 1) ≤
      108 * sourceY S * sourceD S ^ 2 +
        108 * sourceY S *
          smoothAnalyticArea (sourcePhiBetaNuMap S) (openCoordTriangle 0 1) +
        39 * sourceD S *
          (∫⁻ p in openCoordTriangle 0 1, sourceRhoDensity S p) := by
  let T := openCoordTriangle 0 1
  let W := sourceIncomingWeight S
  let F := sourceOutgoingLogMajorant S
  let J : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal |(fderiv ℝ (sourceLamPhiMap S) p).det|
  let K := sourceRhoDensity S
  let A := smoothAnalyticArea (sourcePhiBetaNuMap S) T
  let R := ∫⁻ p in T, K p
  have hT : MeasurableSet T := by
    change MeasurableSet (openCoordTriangle 0 1)
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior.measurableSet
  obtain ⟨hW, hWs, hY⟩ := sourceIncomingWeight_fibers H
  have hF := sourceOutgoingLogMajorant_aemeasurable H hr hcenter hboot
  have hpoint : ∀ p ∈ T,
      J p ≤ 1 * (W p * F p.2) +
        (39 * ENNReal.ofReal (sourceD S).toReal) * K p := by
    intro p hp
    simpa only [one_mul] using
      sourceLamPhi_area_density_le H hr hcenter hboot hp
  have hD : ENNReal.ofReal (sourceD S).toReal = sourceD S :=
    ENNReal.ofReal_toReal (sourceD_ne_top_unit H)
  have hD2 : ENNReal.ofReal (108 * (sourceD S).toReal ^ 2) =
      108 * sourceD S ^ 2 := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 108),
      ENNReal.ofReal_pow ENNReal.toReal_nonneg, hD]
    norm_num
  have hFint : (∫⁻ v in Ioo (0 : ℝ) 1, F v) ≤
      108 * sourceD S ^ 2 + A := by
    simpa only [F, A, T, hD2] using eq4_19c H hr hcenter hboot
  have hd : 39 * ENNReal.ofReal (sourceD S).toReal ≠ ∞ := by
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hraw := outgoing_area_weighted_incoming W J K F
    1 (39 * ENNReal.ofReal (sourceD S).toReal)
    (sourceY S) (108 * sourceD S ^ 2 + A) R
    hW hF hd hWs hY hpoint hFint rfl
  rw [hD] at hraw
  have hA : smoothAnalyticArea (sourceLamPhiMap S) T =
      ∫⁻ p in T, J p := smooth_analytic_area _ hT
  rw [hA]
  calc
    (∫⁻ p in T, J p) ≤
        1 * (sourceY S * (108 * sourceD S ^ 2 + A)) +
          (39 * sourceD S) * R := hraw
    _ = 108 * sourceY S * sourceD S ^ 2 +
          sourceY S * A + 39 * sourceD S * R := by ring
    _ ≤ 108 * sourceY S * sourceD S ^ 2 +
          108 * sourceY S * A + 39 * sourceD S * R := by
      gcongr
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right
          (by norm_num : (1 : ℝ≥0∞) ≤ 108) (bot_le : (0 : ℝ≥0∞) ≤ sourceY S)

/-- Corrected equation (4.26). The log residual used in the proof is
`∂u log|ν| − μν/((1−μ)r) − f*`, following the sign correction in
(4.11b)–(4.13b) and its extension to the area estimates; see ERRATA.md, ERR-23.
The universal constants are `1` and `39`. -/
theorem eq4_26 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 1) ≤
      sourceX S *
        (eVariationOn (fun t => Real.log (-S.nu t t)) (Ioo 0 1) +
          smoothAnalyticArea (sourcePhiAlphaLamMap S) (openCoordTriangle 0 1)) +
        39 * sourceD S *
          (∫⁻ p in openCoordTriangle 0 1, sourceRhoDensity S p) := by
  let T := openCoordTriangle 0 1
  let W := sourceOutgoingWeight S
  let F := sourceIncomingLogMajorant S
  let J : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal |(fderiv ℝ (sourceNuPhiMap S) p).det|
  let K := sourceRhoDensity S
  let A := smoothAnalyticArea (sourcePhiAlphaLamMap S) T
  let V := eVariationOn (fun t => Real.log (-S.nu t t)) (Ioo 0 1)
  let R := ∫⁻ p in T, K p
  have hT : MeasurableSet T := by
    change MeasurableSet (openCoordTriangle 0 1)
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior.measurableSet
  obtain ⟨hW, hWs, hX⟩ := sourceOutgoingWeight_fibers H
  have hF := sourceIncomingLogMajorant_aemeasurable S
  have hpoint : ∀ p ∈ T,
      J p ≤ 1 * (W p * F p.1) +
        (39 * ENNReal.ofReal (sourceD S).toReal) * K p := by
    intro p hp
    simpa only [one_mul] using
      sourceNuPhi_area_density_le_corrected H hr hcenter hboot hp
  have hD : ENNReal.ofReal (sourceD S).toReal = sourceD S :=
    ENNReal.ofReal_toReal (sourceD_ne_top_unit H)
  have hFint : (∫⁻ u in Ioo (0 : ℝ) 1, F u) ≤ V + A := by
    simpa only [F, V, A, T] using eq4_25c H hr hcenter hboot
  have hd : 39 * ENNReal.ofReal (sourceD S).toReal ≠ ∞ := by
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hraw := outgoing_area_weighted_outgoing W J K F
    1 (39 * ENNReal.ofReal (sourceD S).toReal)
    (sourceX S) (V + A) R
    hW hF hd hWs hX hpoint hFint rfl
  rw [hD] at hraw
  have hA : smoothAnalyticArea (sourceNuPhiMap S) T =
      ∫⁻ p in T, J p := smooth_analytic_area _ hT
  rw [hA]
  simpa only [one_mul, mul_assoc] using hraw

end ChristodoulouBV

end
