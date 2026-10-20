module

public import ChristodoulouBV.AreaEstimates.SmallDataAbsorption
import Mathlib.Tactic

/-!
# The four small-data analytic areas

The scalar-quotient areas from (4.33) are substituted into the outgoing
and incoming geometric area inequalities.
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

private theorem geometric_area_algebra
    {D Y Z A B L N : ℝ≥0∞} (hY : Y ≤ Z)
    (hA : A ≤ 30000000000 * (D * Z))
    (hB : B ≤ 30000000000 * (D * Z))
    (hL : L ≤ 108 * Y * D ^ 2 + 108 * (D + Y) * B)
    (hN : N ≤ 5000 * D ^ 2 * Z + 5000 * Z * B +
      5000 * (D + Z) * A) :
    L ≤ 1000000000000000 * (D * Z) * (D + Z) ∧
      N ≤ 1000000000000000 * (D * Z) * (D + Z) := by
  have hD2Z : D ^ 2 * Z ≤ D * Z * (D + Z) := by
    calc
      D ^ 2 * Z = D * Z * D := by ring
      _ ≤ D * Z * (D + Z) := by
        gcongr
        exact le_add_right le_rfl
  have hYD2 : Y * D ^ 2 ≤ D * Z * (D + Z) := by
    calc
      Y * D ^ 2 ≤ Z * D ^ 2 := by gcongr
      _ = D ^ 2 * Z := by ring
      _ ≤ D * Z * (D + Z) := hD2Z
  have hDB : (D + Y) * B ≤ 30000000000 * (D * Z) * (D + Z) := by
    calc
      (D + Y) * B ≤ (D + Z) * (30000000000 * (D * Z)) := by gcongr
      _ = 30000000000 * (D * Z) * (D + Z) := by ring
  have hZB : Z * B ≤ 30000000000 * (D * Z) * (D + Z) := by
    calc
      Z * B ≤ Z * (30000000000 * (D * Z)) := by gcongr
      _ = 30000000000 * (D * Z) * Z := by ring
      _ ≤ 30000000000 * (D * Z) * (D + Z) := by
        gcongr
        exact le_add_left le_rfl
  have hEA : (D + Z) * A ≤ 30000000000 * (D * Z) * (D + Z) := by
    calc
      (D + Z) * A ≤ (D + Z) * (30000000000 * (D * Z)) := by gcongr
      _ = 30000000000 * (D * Z) * (D + Z) := by ring
  constructor
  · calc
      L ≤ 108 * Y * D ^ 2 + 108 * (D + Y) * B := hL
      _ ≤ 108 * (D * Z * (D + Z)) +
            108 * (30000000000 * (D * Z) * (D + Z)) := by
              apply add_le_add
              · calc
                  108 * Y * D ^ 2 = 108 * (Y * D ^ 2) := by ring
                  _ ≤ 108 * (D * Z * (D + Z)) := by gcongr
              · calc
                  108 * (D + Y) * B = 108 * ((D + Y) * B) := by ring
                  _ ≤ 108 * (30000000000 * (D * Z) * (D + Z)) := by gcongr
      _ = 3240000000108 * (D * Z) * (D + Z) := by ring
      _ ≤ 1000000000000000 * (D * Z) * (D + Z) := by
        gcongr
        norm_num
  · calc
      N ≤ 5000 * D ^ 2 * Z + 5000 * Z * B +
            5000 * (D + Z) * A := hN
      _ ≤ 5000 * (D * Z * (D + Z)) +
            5000 * (30000000000 * (D * Z) * (D + Z)) +
            5000 * (30000000000 * (D * Z) * (D + Z)) := by
              apply add_le_add
              · apply add_le_add
                · calc
                    5000 * D ^ 2 * Z = 5000 * (D ^ 2 * Z) := by ring
                    _ ≤ 5000 * (D * Z * (D + Z)) := by gcongr
                · calc
                    5000 * Z * B = 5000 * (Z * B) := by ring
                    _ ≤ 5000 * (30000000000 * (D * Z) * (D + Z)) := by gcongr
              · calc
                  5000 * (D + Z) * A = 5000 * ((D + Z) * A) := by ring
                  _ ≤ 5000 * (30000000000 * (D * Z) * (D + Z)) := by gcongr
      _ = 300000000005000 * (D * Z) * (D + Z) := by ring
      _ ≤ 1000000000000000 * (D * Z) * (D + Z) := by
        gcongr
        norm_num

/-- Equation (4.34): the two geometric analytic areas are `O(DZ(D+Z))`. -/
theorem eq4_34 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    (hD : sourceD S ≤ s4Epsilon0) (hZ : sourceZ S ≤ s4Epsilon0) :
    smoothAnalyticArea (sourceLamPhiMap S) (openCoordTriangle 0 1) ≤
        1000000000000000 * (sourceD S * sourceZ S) *
          (sourceD S + sourceZ S) ∧
      smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 1) ≤
        1000000000000000 * (sourceD S * sourceZ S) *
          (sourceD S + sourceZ S) := by
  obtain ⟨hA, hB⟩ := eq4_33 H hr hcenter hboot hD hZ
  exact geometric_area_algebra (le_max_right _ _) hA hB
    (eq4_24 H hr hcenter hboot)
    (eq4_30 H hr hcenter hboot hD hZ)

end ChristodoulouBV

end
