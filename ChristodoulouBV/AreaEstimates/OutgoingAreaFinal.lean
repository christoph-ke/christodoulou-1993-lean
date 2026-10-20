module

public import ChristodoulouBV.AreaEstimates.OutgoingAreaRhoArea
import Mathlib.Tactic

/-!
# The outgoing Jacobian area estimate

Substitution of the exact half-area rho bound (4.23) in (4.21) gives
Christodoulou's outgoing estimate (4.24).
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace ChristodoulouBV

/-- Equation (4.24), with universal constant `108`. -/
theorem eq4_24 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    smoothAnalyticArea (sourceLamPhiMap S) (openCoordTriangle 0 1) ≤
      108 * sourceY S * sourceD S ^ 2 +
        108 * (sourceD S + sourceY S) *
          smoothAnalyticArea (sourcePhiBetaNuMap S)
            (openCoordTriangle 0 1) := by
  let A := smoothAnalyticArea (sourcePhiBetaNuMap S)
    (openCoordTriangle 0 1)
  let R := ∫⁻ p in openCoordTriangle 0 1, sourceRhoDensity S p
  have h21 := eq4_21 H hr hcenter hboot
  have h23 : R ≤ (1 / 2 : ℝ≥0∞) * A := eq4_23 H hr hcenter hboot
  have hhalf : (1 / 2 : ℝ≥0∞) * A ≤ A := by
    calc
      (1 / 2 : ℝ≥0∞) * A ≤ 1 * A :=
        mul_le_mul_of_nonneg_right (by norm_num) bot_le
      _ = A := one_mul A
  have hR : R ≤ A := h23.trans hhalf
  have hterm : 39 * sourceD S * R ≤ 108 * sourceD S * A := by
    calc
      39 * sourceD S * R ≤ 39 * sourceD S * A :=
        mul_le_mul_of_nonneg_left hR bot_le
      _ ≤ 108 * sourceD S * A := by
        gcongr
        norm_num
  calc
    smoothAnalyticArea (sourceLamPhiMap S) (openCoordTriangle 0 1) ≤
        108 * sourceY S * sourceD S ^ 2 +
          108 * sourceY S * A + 39 * sourceD S * R := h21
    _ ≤ 108 * sourceY S * sourceD S ^ 2 +
          108 * sourceY S * A + 108 * sourceD S * A := by
      exact add_le_add_right hterm _
    _ = 108 * sourceY S * sourceD S ^ 2 +
          108 * (sourceD S + sourceY S) * A := by ring

end ChristodoulouBV

end
