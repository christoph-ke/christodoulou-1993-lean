module

public import ChristodoulouBV.AreaEstimates.SmallDataFinite
import Mathlib.Tactic

/-!
# First coupled small-data area inequality

Equation (4.32a) follows directly from the established analytic inequalities
(4.16) and (4.24). This step needs only `D,Z ≤ 1`.
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

private theorem first_area_algebra
    {D Y Z A L B : ℝ≥0∞}
    (hD : D ≤ 1) (hYZ : Y ≤ Z) (hZ : Z ≤ 1)
    (hA : A ≤ 45 * (D * Y) + 45 * (Y + D) * L)
    (hL : L ≤ 108 * Y * D ^ 2 + 108 * (D + Y) * B) :
    A ≤ 10000 * (D * Z) + 10000 * (D + Z) ^ 2 * B := by
  have hY : Y ≤ 1 := hYZ.trans hZ
  have hsum : Y + D ≤ 2 := by
    calc
      Y + D ≤ 1 + 1 := add_le_add hY hD
      _ = 2 := by norm_num
  have hDsquared : D ^ 2 ≤ D := by
    calc
      D ^ 2 = D * D := pow_two D
      _ ≤ D * 1 := mul_le_mul_of_nonneg_left hD bot_le
      _ = D := mul_one D
  have hsmall : (Y + D) * Y * D ^ 2 ≤ 2 * (D * Z) := by
    calc
      (Y + D) * Y * D ^ 2 ≤ 2 * Z * D := by
        gcongr
      _ = 2 * (D * Z) := by ring
  have hsumZ : Y + D ≤ D + Z := by
    calc
      Y + D ≤ Z + D := add_le_add hYZ le_rfl
      _ = D + Z := add_comm Z D
  have hB : (Y + D) * (D + Y) * B ≤ (D + Z) ^ 2 * B := by
    calc
      (Y + D) * (D + Y) * B ≤ (D + Z) * (D + Z) * B := by
        gcongr
      _ = (D + Z) ^ 2 * B := by rw [pow_two]
  calc
    A ≤ 45 * (D * Y) + 45 * (Y + D) * L := hA
    _ ≤ 45 * (D * Y) +
        45 * (Y + D) * (108 * Y * D ^ 2 + 108 * (D + Y) * B) := by
      gcongr
    _ = 45 * (D * Y) +
        4860 * ((Y + D) * Y * D ^ 2) +
        4860 * ((Y + D) * (D + Y) * B) := by ring
    _ ≤ 45 * (D * Z) + 4860 * (2 * (D * Z)) +
        4860 * ((D + Z) ^ 2 * B) := by
      gcongr
    _ = 9765 * (D * Z) + 4860 * ((D + Z) ^ 2 * B) := by ring
    _ ≤ 10000 * (D * Z) + 10000 * (D + Z) ^ 2 * B := by
      have h1 : 9765 * (D * Z) ≤ 10000 * (D * Z) :=
        mul_le_mul_of_nonneg_right (by norm_num) bot_le
      have h2 : 4860 * ((D + Z) ^ 2 * B) ≤
          10000 * ((D + Z) ^ 2 * B) :=
        mul_le_mul_of_nonneg_right (by norm_num) bot_le
      calc
        9765 * (D * Z) + 4860 * ((D + Z) ^ 2 * B) ≤
            10000 * (D * Z) + 10000 * ((D + Z) ^ 2 * B) :=
          add_le_add h1 h2
        _ = _ := by ring

/-- Equation (4.32a), with explicit universal coefficient `10000`. -/
theorem eq4_32a {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    (hD : sourceD S ≤ 1) (hZ : sourceZ S ≤ 1) :
    smoothAnalyticArea (sourcePhiAlphaLamMap S) (openCoordTriangle 0 1) ≤
      10000 * (sourceD S * sourceZ S) +
        10000 * (sourceD S + sourceZ S) ^ 2 *
          smoothAnalyticArea (sourcePhiBetaNuMap S) (openCoordTriangle 0 1) := by
  exact first_area_algebra hD (le_max_right _ _) hZ
    (eq4_16 H hr hcenter hboot) (eq4_24 H hr hcenter hboot)

end ChristodoulouBV

end
