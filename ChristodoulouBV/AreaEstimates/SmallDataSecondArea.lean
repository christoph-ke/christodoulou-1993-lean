module

public import ChristodoulouBV.AreaEstimates.SmallDataSecondCoupled
import Mathlib.Tactic

/-!
# The second coupled area inequality

Substituting (4.24) and (4.30) into (4.31) leaves a second finite area
self-term.  The same universal threshold absorbs it.
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

/-- The second area self-coefficient is at most one half under the same
universal threshold. -/
theorem s4_second_coefficient_le_half {D Z : ℝ≥0∞}
    (hD : D ≤ s4Epsilon0) (hZ : Z ≤ s4Epsilon0) :
    1021600000 * Z * (D + Z) ≤ 1 / 2 := by
  have hsum : D + Z ≤ 2 * s4Epsilon0 := by
    calc
      D + Z ≤ s4Epsilon0 + s4Epsilon0 := add_le_add hD hZ
      _ = 2 * s4Epsilon0 := by ring
  calc
    1021600000 * Z * (D + Z) ≤
        1021600000 * s4Epsilon0 * (2 * s4Epsilon0) := by gcongr
    _ ≤ 1 / 2 := by
      unfold s4Epsilon0
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

private theorem second_area_substitution
    {D Y Z A B L N : ℝ≥0∞}
    (hD : D ≤ 1) (hZ : Z ≤ 1) (hY : Y ≤ Z)
    (hB : B ≤ 200000 * (D * Z) + 200000 * Z * L +
      200000 * (D + Z) * N)
    (hL : L ≤ 108 * Y * D ^ 2 + 108 * (D + Y) * B)
    (hN : N ≤ 5000 * D ^ 2 * Z + 5000 * Z * B +
      5000 * (D + Z) * A) :
    B ≤ (3000000000 * (D * Z) + 1000000000 * (D + Z) ^ 2 * A) +
      1021600000 * Z * (D + Z) * B := by
  have hD2 : D ^ 2 ≤ D := by
    calc
      D ^ 2 = D * D := pow_two D
      _ ≤ D * 1 := mul_le_mul_of_nonneg_left hD bot_le
      _ = D := mul_one D
  have hsum : D + Z ≤ 2 := by
    calc
      D + Z ≤ 1 + 1 := add_le_add hD hZ
      _ = 2 := by norm_num
  have h1 : Z * Y * D ^ 2 ≤ D * Z := by
    calc
      Z * Y * D ^ 2 ≤ Z * Z * D := by gcongr
      _ ≤ Z * 1 * D := by gcongr
      _ = D * Z := by ring
  have h2 : (D + Z) * D ^ 2 * Z ≤ 2 * (D * Z) := by
    calc
      (D + Z) * D ^ 2 * Z ≤ 2 * D * Z := by gcongr
      _ = 2 * (D * Z) := by ring
  have h3 : Z * (D + Y) * B ≤ Z * (D + Z) * B := by gcongr
  calc
    B ≤ 200000 * (D * Z) + 200000 * Z * L +
        200000 * (D + Z) * N := hB
    _ ≤ 200000 * (D * Z) +
          200000 * Z * (108 * Y * D ^ 2 + 108 * (D + Y) * B) +
          200000 * (D + Z) *
            (5000 * D ^ 2 * Z + 5000 * Z * B +
              5000 * (D + Z) * A) := by gcongr
    _ = 200000 * (D * Z) + 21600000 * (Z * Y * D ^ 2) +
          21600000 * (Z * (D + Y) * B) +
          1000000000 * ((D + Z) * D ^ 2 * Z) +
          1000000000 * ((D + Z) * Z * B) +
          1000000000 * (D + Z) ^ 2 * A := by ring
    _ ≤ 200000 * (D * Z) + 21600000 * (D * Z) +
          21600000 * (Z * (D + Z) * B) +
          1000000000 * (2 * (D * Z)) +
          1000000000 * ((D + Z) * Z * B) +
          1000000000 * (D + Z) ^ 2 * A := by
      gcongr
    _ = 2021800000 * (D * Z) + 1000000000 * (D + Z) ^ 2 * A +
          1021600000 * Z * (D + Z) * B := by ring
    _ ≤ (3000000000 * (D * Z) + 1000000000 * (D + Z) ^ 2 * A) +
          1021600000 * Z * (D + Z) * B := by
      have hcoef : 2021800000 * (D * Z) ≤ 3000000000 * (D * Z) := by
        gcongr
        norm_num
      calc
        2021800000 * (D * Z) + 1000000000 * (D + Z) ^ 2 * A +
            1021600000 * Z * (D + Z) * B =
            2021800000 * (D * Z) +
              (1000000000 * (D + Z) ^ 2 * A +
                1021600000 * Z * (D + Z) * B) := by ring
        _ ≤ 3000000000 * (D * Z) +
              (1000000000 * (D + Z) ^ 2 * A +
                1021600000 * Z * (D + Z) * B) :=
          add_le_add_left hcoef _
        _ = _ := by ring

private theorem absorb_second_half {D Z B R : ℝ≥0∞}
    (hD : D ≤ s4Epsilon0) (hZ : Z ≤ s4Epsilon0)
    (hB : B ≠ ∞)
    (h : B ≤ R + 1021600000 * Z * (D + Z) * B) :
    B ≤ 2 * R := by
  have hcoeff : 1021600000 * Z * (D + Z) * B ≤ (1 / 2) * B := by
    calc
      1021600000 * Z * (D + Z) * B =
          (1021600000 * Z * (D + Z)) * B := by ring
      _ ≤ (1 / 2) * B :=
        mul_le_mul_of_nonneg_right (s4_second_coefficient_le_half hD hZ) bot_le
  have hraw : B ≤ R + (1 / 2) * B :=
    h.trans (add_le_add_right hcoeff R)
  have hhalfB : (1 / 2 : ℝ≥0∞) * B ≤ B := by
    calc
      (1 / 2 : ℝ≥0∞) * B ≤ 1 * B := by gcongr; norm_num
      _ = B := one_mul B
  have hhalfFinite : (1 / 2 : ℝ≥0∞) * B ≠ ∞ :=
    ne_top_of_le_ne_top hB hhalfB
  have hhalf : (1 / 2 : ℝ≥0∞) + (1 / 2) = 1 := by
    rw [div_eq_mul_inv, one_mul, ← two_mul,
      ENNReal.mul_inv_cancel (by norm_num) (by finiteness)]
  have hsplit : B = (1 / 2 : ℝ≥0∞) * B + (1 / 2) * B := by
    calc
      B = 1 * B := (one_mul B).symm
      _ = ((1 / 2 : ℝ≥0∞) + (1 / 2)) * B := by rw [hhalf]
      _ = _ := add_mul _ _ _
  have hshift : (1 / 2 : ℝ≥0∞) * B + (1 / 2) * B ≤
      R + (1 / 2) * B := by
    simpa only [← hsplit] using hraw
  have hhalfLe : (1 / 2 : ℝ≥0∞) * B ≤ R :=
    ENNReal.le_of_add_le_add_right hhalfFinite hshift
  have htwohalf : (2 : ℝ≥0∞) * (1 / 2) = 1 := by
    simpa only [two_mul] using hhalf
  calc
    B = 2 * ((1 / 2 : ℝ≥0∞) * B) := by
      rw [← mul_assoc, htwohalf, one_mul]
    _ ≤ 2 * R := by gcongr

/-- Equation (4.32b), with universal coefficient `10000000000` and the
same fixed threshold as (4.31). -/
theorem eq4_32b {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    (hD : sourceD S ≤ s4Epsilon0) (hZ : sourceZ S ≤ s4Epsilon0) :
    smoothAnalyticArea (sourcePhiBetaNuMap S) (openCoordTriangle 0 1) ≤
      10000000000 * (sourceD S * sourceZ S) +
        10000000000 * (sourceD S + sourceZ S) ^ 2 *
          smoothAnalyticArea (sourcePhiAlphaLamMap S)
            (openCoordTriangle 0 1) := by
  let D := sourceD S
  let Z := sourceZ S
  let A := smoothAnalyticArea (sourcePhiAlphaLamMap S) (openCoordTriangle 0 1)
  let B := smoothAnalyticArea (sourcePhiBetaNuMap S) (openCoordTriangle 0 1)
  let L := smoothAnalyticArea (sourceLamPhiMap S) (openCoordTriangle 0 1)
  let N := smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 1)
  have hY : sourceY S ≤ Z := by
    change sourceY S ≤ sourceZ S
    exact le_max_right _ _
  have hD1 : D ≤ 1 := hD.trans s4Epsilon0_le_one
  have hZ1 : Z ≤ 1 := hZ.trans s4Epsilon0_le_one
  have h31 : B ≤ 200000 * (D * Z) + 200000 * Z * L +
      200000 * (D + Z) * N := eq4_31 H hr hcenter hboot hD hZ
  have h24 : L ≤ 108 * sourceY S * D ^ 2 +
      108 * (D + sourceY S) * B := eq4_24 H hr hcenter hboot
  have h30 : N ≤ 5000 * D ^ 2 * Z + 5000 * Z * B +
      5000 * (D + Z) * A := eq4_30 H hr hcenter hboot hD hZ
  have hBfinite : B ≠ ∞ := (s4_four_areas_ne_top H hboot).2.1
  have hraw := second_area_substitution hD1 hZ1 hY h31 h24 h30
  have hAbs := absorb_second_half hD hZ hBfinite hraw
  change B ≤ 10000000000 * (D * Z) + 10000000000 * (D + Z) ^ 2 * A
  calc
    B ≤ 2 * (3000000000 * (D * Z) +
        1000000000 * (D + Z) ^ 2 * A) := hAbs
    _ = 6000000000 * (D * Z) + 2000000000 * (D + Z) ^ 2 * A := by ring
    _ ≤ 10000000000 * (D * Z) + 10000000000 * (D + Z) ^ 2 * A := by
      gcongr <;> norm_num

end ChristodoulouBV

end
