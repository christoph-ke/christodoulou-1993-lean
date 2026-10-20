module

public import ChristodoulouBV.AreaEstimates.SmallDataSecondArea
import Mathlib.Tactic

/-!
# Absorption of the two coupled scalar-quotient areas

The area quantities are finite for C¹ solutions on the compact unit
triangle.  Both coefficients are controlled by the one fixed threshold.
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

/-- The larger of the two coupled coefficients is at most one quarter. -/
theorem s4_coupled_coefficient_le_quarter {D Z : ℝ≥0∞}
    (hD : D ≤ s4Epsilon0) (hZ : Z ≤ s4Epsilon0) :
    10000000000 * (D + Z) ^ 2 ≤ 1 / 4 := by
  have hsum : D + Z ≤ 2 * s4Epsilon0 := by
    calc
      D + Z ≤ s4Epsilon0 + s4Epsilon0 := add_le_add hD hZ
      _ = 2 * s4Epsilon0 := by ring
  calc
    10000000000 * (D + Z) ^ 2 ≤
        10000000000 * (2 * s4Epsilon0) ^ 2 := by gcongr
    _ ≤ 1 / 4 := by
      unfold s4Epsilon0
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_div,
        ENNReal.toReal_pow]

/-- The second universal restriction absorbs both coupled finite areas. -/
theorem s4_smallness {D Z A B : ℝ≥0∞}
    (hD : D ≤ s4Epsilon0) (hZ : Z ≤ s4Epsilon0)
    (hAfinite : A ≠ ∞) (hBfinite : B ≠ ∞)
    (hA : A ≤ 10000 * (D * Z) + 10000 * (D + Z) ^ 2 * B)
    (hB : B ≤ 10000000000 * (D * Z) +
      10000000000 * (D + Z) ^ 2 * A) :
    A ≤ 30000000000 * (D * Z) ∧
      B ≤ 30000000000 * (D * Z) := by
  have hbig := s4_coupled_coefficient_le_quarter hD hZ
  have hsmall : 10000 * (D + Z) ^ 2 ≤ 1 / 4 := by
    calc
      10000 * (D + Z) ^ 2 ≤ 10000000000 * (D + Z) ^ 2 := by
        gcongr
        norm_num
      _ ≤ 1 / 4 := hbig
  have hA' : A ≤ 10000 * (D * Z) + (1 / 4) * B := by
    calc
      A ≤ 10000 * (D * Z) + 10000 * (D + Z) ^ 2 * B := hA
      _ ≤ 10000 * (D * Z) + (1 / 4) * B := by
        gcongr
  have hB' : B ≤ 10000000000 * (D * Z) + (1 / 4) * A := by
    calc
      B ≤ 10000000000 * (D * Z) + 10000000000 * (D + Z) ^ 2 * A := hB
      _ ≤ 10000000000 * (D * Z) + (1 / 4) * A := by
        gcongr
  let T := A + B
  let R := 10000010000 * (D * Z)
  have hTfinite : T ≠ ∞ := by
    dsimp [T]
    finiteness
  have hquarter : (1 / 4 : ℝ≥0∞) ≤ 1 / 2 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]
  have hT : T ≤ R + (1 / 2) * T := by
    calc
      T = A + B := rfl
      _ ≤ (10000 * (D * Z) + (1 / 4) * B) +
            (10000000000 * (D * Z) + (1 / 4) * A) :=
        add_le_add hA' hB'
      _ = R + (1 / 4) * T := by dsimp [R, T]; ring
      _ ≤ R + (1 / 2) * T := by gcongr
  have hhalfT : (1 / 2 : ℝ≥0∞) * T ≤ T := by
    calc
      (1 / 2 : ℝ≥0∞) * T ≤ 1 * T := by gcongr; norm_num
      _ = T := one_mul T
  have hhalfFinite : (1 / 2 : ℝ≥0∞) * T ≠ ∞ :=
    ne_top_of_le_ne_top hTfinite hhalfT
  have hhalf : (1 / 2 : ℝ≥0∞) + (1 / 2) = 1 := by
    rw [div_eq_mul_inv, one_mul, ← two_mul,
      ENNReal.mul_inv_cancel (by norm_num) (by finiteness)]
  have hsplit : T = (1 / 2 : ℝ≥0∞) * T + (1 / 2) * T := by
    calc
      T = 1 * T := (one_mul T).symm
      _ = ((1 / 2 : ℝ≥0∞) + (1 / 2)) * T := by rw [hhalf]
      _ = _ := add_mul _ _ _
  have hshift : (1 / 2 : ℝ≥0∞) * T + (1 / 2) * T ≤
      R + (1 / 2) * T := by
    simpa only [← hsplit] using hT
  have hhalfLe : (1 / 2 : ℝ≥0∞) * T ≤ R :=
    ENNReal.le_of_add_le_add_right hhalfFinite hshift
  have htwohalf : (2 : ℝ≥0∞) * (1 / 2) = 1 := by
    simpa only [two_mul] using hhalf
  have hTbound : T ≤ 2 * R := by
    calc
      T = 2 * ((1 / 2 : ℝ≥0∞) * T) := by
        rw [← mul_assoc, htwohalf, one_mul]
      _ ≤ 2 * R := by gcongr
  have hAbound : A ≤ T := le_add_right le_rfl
  have hBbound : B ≤ T := le_add_left le_rfl
  have hcoef : 2 * R ≤ 30000000000 * (D * Z) := by
    dsimp [R]
    calc
      2 * (10000010000 * (D * Z)) = 20000020000 * (D * Z) := by ring
      _ ≤ 30000000000 * (D * Z) := by gcongr; norm_num
  exact ⟨hAbound.trans (hTbound.trans hcoef),
    hBbound.trans (hTbound.trans hcoef)⟩

/-- Equation (4.33): both scalar-quotient analytic areas are `O(DZ)`. -/
theorem eq4_33 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    (hD : sourceD S ≤ s4Epsilon0) (hZ : sourceZ S ≤ s4Epsilon0) :
    smoothAnalyticArea (sourcePhiAlphaLamMap S) (openCoordTriangle 0 1) ≤
        30000000000 * (sourceD S * sourceZ S) ∧
      smoothAnalyticArea (sourcePhiBetaNuMap S) (openCoordTriangle 0 1) ≤
        30000000000 * (sourceD S * sourceZ S) := by
  obtain ⟨hAfinite, hBfinite, _, _⟩ := s4_four_areas_ne_top H hboot
  exact s4_smallness hD hZ hAfinite hBfinite
    (eq4_32a H hr hcenter hboot
      (hD.trans s4Epsilon0_le_one) (hZ.trans s4Epsilon0_le_one))
    (eq4_32b H hr hcenter hboot hD hZ)

end ChristodoulouBV

end
