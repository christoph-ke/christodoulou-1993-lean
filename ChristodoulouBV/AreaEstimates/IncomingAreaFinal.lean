module

public import ChristodoulouBV.AreaEstimates.IncomingAreaRhoArea
import Mathlib.Tactic

/-!
# The incoming Jacobian area estimate

Substitution of the conjugate half-area rho bound (4.28) into the
sign-corrected estimate (4.26) gives (4.29).
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace ChristodoulouBV

/-- Equation (4.29), with the universal constant `39`. This uses the
corrected incoming log residual in (4.26), following the sign correction
in (4.11b)–(4.13b) and its extension to the area estimates;
see ERRATA.md, ERR-23. -/
theorem eq4_29 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 1) ≤
      39 * sourceX S *
          eVariationOn (fun t => Real.log (-S.nu t t)) (Ioo 0 1) +
        39 * (sourceD S + sourceX S) *
          smoothAnalyticArea (sourcePhiAlphaLamMap S)
            (openCoordTriangle 0 1) := by
  let A := smoothAnalyticArea (sourcePhiAlphaLamMap S)
    (openCoordTriangle 0 1)
  let V := eVariationOn (fun t => Real.log (-S.nu t t)) (Ioo 0 1)
  let R := ∫⁻ p in openCoordTriangle 0 1, sourceRhoDensity S p
  have h26 := eq4_26 H hr hcenter hboot
  have h28 : R ≤ (1 / 2 : ℝ≥0∞) * A := eq4_28 H hr hcenter hboot
  have hhalf : (1 / 2 : ℝ≥0∞) * A ≤ A := by
    calc
      (1 / 2 : ℝ≥0∞) * A ≤ 1 * A :=
        mul_le_mul_of_nonneg_right (by norm_num) bot_le
      _ = A := one_mul A
  have hR : R ≤ A := h28.trans hhalf
  have hterm : 39 * sourceD S * R ≤ 39 * sourceD S * A :=
    mul_le_mul_of_nonneg_left hR bot_le
  have hV : sourceX S * V ≤ 39 * sourceX S * V := by
    calc
      sourceX S * V = 1 * sourceX S * V := by rw [one_mul]
      _ ≤ 39 * sourceX S * V := by gcongr; norm_num
  have hA : (sourceX S + 39 * sourceD S) * A ≤
      39 * (sourceD S + sourceX S) * A := by
    have hc : sourceX S + 39 * sourceD S ≤
        39 * (sourceD S + sourceX S) := by
      calc
        sourceX S + 39 * sourceD S ≤
            39 * sourceX S + 39 * sourceD S := by
          exact add_le_add (by
            calc
              sourceX S = 1 * sourceX S := by rw [one_mul]
              _ ≤ 39 * sourceX S :=
                mul_le_mul_of_nonneg_right (by norm_num) bot_le)
            (le_refl _)
        _ = 39 * (sourceD S + sourceX S) := by ring
    exact mul_le_mul_of_nonneg_right hc bot_le
  calc
    smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 1) ≤
        sourceX S * (V + A) + 39 * sourceD S * R := h26
    _ ≤ sourceX S * (V + A) + 39 * sourceD S * A :=
      add_le_add (le_refl _) hterm
    _ = sourceX S * V +
          (sourceX S + 39 * sourceD S) * A := by ring
    _ ≤ 39 * sourceX S * V +
          39 * (sourceD S + sourceX S) * A :=
      add_le_add hV hA

end ChristodoulouBV

end
