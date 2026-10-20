module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsSourceQuotient
import Mathlib.Tactic

/-!
# Reciprocal bounds for a small quadratic coefficient

If `1-m` has a common positive lower bound, its reciprocal is bounded.
The value and first-jet differences retain the quadratic and linear gap
factors of `m`.
-/

public section

namespace intervalIntegral

/-- A positive lower bound for `1-m` controls its reciprocal. -/
theorem inv_one_sub_le {ε m : ℝ} (hε : 0 < ε)
    (hm : ε ≤ 1 - m) : |(1 - m)⁻¹| ≤ ε⁻¹ := by
  have hpos : 0 < 1 - m := hε.trans_le hm
  rw [abs_of_pos (inv_pos.mpr hpos)]
  exact (inv_le_inv₀ hpos hε).2 hm

/-- The first-jet expression of `(1-m)⁻¹` inherits a linear gap bound. -/
theorem abs_inverseOneSubJet_le_of_gap_bounds
    {ε d M₁ m mi : ℝ}
    (hε : 0 < ε) (hd : 0 ≤ d) (hM₁ : 0 ≤ M₁)
    (hm : ε ≤ 1 - m) (hmi : |mi| ≤ M₁ * d) :
    |mi / (1 - m) ^ 2| ≤ (M₁ / ε ^ 2) * d := by
  have hpos : 0 < 1 - m := hε.trans_le hm
  have hbound : 0 ≤ M₁ * d := mul_nonneg hM₁ hd
  rw [abs_div, abs_of_pos (pow_pos hpos 2)]
  calc
    _ ≤ (M₁ * d) / ε ^ 2 := by gcongr
    _ = (M₁ / ε ^ 2) * d := by ring

/-- The reciprocal difference retains the quadratic gap factor of `m`. -/
theorem abs_inv_one_sub_sub_le_of_quadratic_gap_bounds
    {ε d D MΔ₀ m₁ m₂ : ℝ}
    (hε : 0 < ε)
    (hm₁ : ε ≤ 1 - m₁) (hm₂ : ε ≤ 1 - m₂)
    (hmdiff : |m₁ - m₂| ≤ MΔ₀ * d ^ 2 * D) :
    |(1 - m₁)⁻¹ - (1 - m₂)⁻¹| ≤
      (MΔ₀ / ε ^ 2) * d ^ 2 * D := by
  have hden : |(1 - m₁) - (1 - m₂)| ≤ MΔ₀ * d ^ 2 * D := by
    have hid : (1 - m₁) - (1 - m₂) = -(m₁ - m₂) := by ring
    rw [hid, abs_neg]
    exact hmdiff
  have h := abs_div_sub_div_le hε hm₁ hm₂
    (x₁ := (1 : ℝ)) (x₂ := 1)
    (X := 0) (Y := MΔ₀ * d ^ 2 * D) (Z := 1)
    (by simp) hden (by simp)
  have h' : |(1 - m₁)⁻¹ - (1 - m₂)⁻¹| ≤
      0 / ε + 1 * (MΔ₀ * d ^ 2 * D) / ε ^ 2 := by
    simpa only [one_div] using h
  calc
    _ ≤ 0 / ε + 1 * (MΔ₀ * d ^ 2 * D) / ε ^ 2 := h'
    _ = (MΔ₀ / ε ^ 2) * d ^ 2 * D := by ring

/-- The difference of first-jet expressions for `(1-m)⁻¹` has the two
expected terms: changed numerator and changed reciprocal square. -/
theorem abs_inverseOneSubJet_sub_le_of_gap_bounds
    {ε d D M₁ MΔ₀ MΔ₁ m₁ m₂ mi₁ mi₂ : ℝ}
    (hε : 0 < ε) (hd : 0 ≤ d) (hdle : d ≤ 1)
    (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁) (hMΔ₀ : 0 ≤ MΔ₀)
    (hm₁ : ε ≤ 1 - m₁) (hm₂ : ε ≤ 1 - m₂)
    (hmdiff : |m₁ - m₂| ≤ MΔ₀ * d ^ 2 * D)
    (hmi₂ : |mi₂| ≤ M₁ * d)
    (hmidiff : |mi₁ - mi₂| ≤ MΔ₁ * d * D) :
    |mi₁ / (1 - m₁) ^ 2 - mi₂ / (1 - m₂) ^ 2| ≤
      (MΔ₁ / ε ^ 2 + 2 * M₁ * MΔ₀ / ε ^ 3) * d * D := by
  have hpos : 0 < 1 - m₁ := hε.trans_le hm₁
  have hden : |(1 - m₁) - (1 - m₂)| ≤ MΔ₀ * d ^ 2 * D := by
    have hid : (1 - m₁) - (1 - m₂) = -(m₁ - m₂) := by ring
    rw [hid, abs_neg]
    exact hmdiff
  have hsq := abs_inv_sq_sub_inv_sq_le hε hm₁ hm₂ hden
  have hsq₁ : |((1 - m₁) ^ 2)⁻¹| ≤ (ε ^ 2)⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr (pow_pos hpos 2))]
    exact (inv_le_inv₀ (pow_pos hpos 2) (pow_pos hε 2)).2 (by gcongr)
  have hid : mi₁ / (1 - m₁) ^ 2 - mi₂ / (1 - m₂) ^ 2 =
      (mi₁ - mi₂) * ((1 - m₁) ^ 2)⁻¹ +
        mi₂ * (((1 - m₁) ^ 2)⁻¹ - ((1 - m₂) ^ 2)⁻¹) := by
    simp only [div_eq_mul_inv]; ring
  rw [hid]
  have hfirst : |(mi₁ - mi₂) * ((1 - m₁) ^ 2)⁻¹| ≤
      (MΔ₁ * d * D) * (ε ^ 2)⁻¹ := by
    rw [abs_mul]
    exact mul_le_mul hmidiff hsq₁ (abs_nonneg _) ((abs_nonneg _).trans hmidiff)
  have hsecond : |mi₂ * (((1 - m₁) ^ 2)⁻¹ - ((1 - m₂) ^ 2)⁻¹)| ≤
      (M₁ * d) * (2 * (MΔ₀ * d ^ 2 * D) / ε ^ 3) := by
    rw [abs_mul]
    exact mul_le_mul hmi₂ hsq (abs_nonneg _) (mul_nonneg hM₁ hd)
  have hdsq : d ^ 2 ≤ 1 := by nlinarith only [hd, hdle]
  have hlast : (M₁ * d) * (2 * (MΔ₀ * d ^ 2 * D) / ε ^ 3) ≤
      (2 * M₁ * MΔ₀ / ε ^ 3) * d * D := by
    have hcoef : 0 ≤ (2 * M₁ * MΔ₀ / ε ^ 3) * d * D := by positivity
    calc
      _ = ((2 * M₁ * MΔ₀ / ε ^ 3) * d * D) * d ^ 2 := by ring
      _ ≤ ((2 * M₁ * MΔ₀ / ε ^ 3) * d * D) * 1 :=
        mul_le_mul_of_nonneg_left hdsq hcoef
      _ = _ := by ring
  calc
    _ ≤ |(mi₁ - mi₂) * ((1 - m₁) ^ 2)⁻¹| +
        |mi₂ * (((1 - m₁) ^ 2)⁻¹ - ((1 - m₂) ^ 2)⁻¹)| := abs_add_le _ _
    _ ≤ (MΔ₁ * d * D) * (ε ^ 2)⁻¹ +
        (M₁ * d) * (2 * (MΔ₀ * d ^ 2 * D) / ε ^ 3) :=
      add_le_add hfirst hsecond
    _ ≤ (MΔ₁ * d * D) * (ε ^ 2)⁻¹ +
        (2 * M₁ * MΔ₀ / ε ^ 3) * d * D := by gcongr
    _ = _ := by field_simp [hε.ne']

end intervalIntegral

end
