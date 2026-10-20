module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Algebra of the terminal lambda derivative equation

The outgoing mass equation eliminates the derivative of the mass ratio from
the derivative of `μ / ((1-μ) r)`. This identity is used in the terminal trace estimate
before applying any field bounds.
-/

public section

namespace ChristodoulouBV.Uniqueness

/-- Substitute the outgoing mass-ratio equation into the derivative of the
mixed coefficient `μ / ((1-μ) r)`. -/
theorem mass_ratio_coefficient_derivative_identity
    {r lam μ f q μv : ℝ}
    (hr : r ≠ 0) (hq : q ≠ 0)
    (hμv : μv = q * lam * f ^ 2 / r - μ * lam / r) :
    μv / (q ^ 2 * r) - μ * lam / (q * r ^ 2) =
      lam * f ^ 2 / (q * r ^ 2) -
        μ * lam * (1 / q ^ 2 + 1 / q) / r ^ 2 := by
  rw [hμv]
  field_simp [hr, hq]
  ring

/-- The improved cubic mass and linear scalar estimates bound the derivative
of the mixed coefficient in equation (8), assuming `λ ≤ 1/2`. -/
theorem mass_ratio_coefficient_derivative_abs_le
    {r lam μ f q q₀ B : ℝ}
    (hr : 0 < r) (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 2)
    (hμ0 : 0 ≤ μ) (hq₀ : 0 < q₀) (hq : q₀ ≤ q)
    (hB : 0 ≤ B)
    (hμ : μ ≤ B ^ 2 * r ^ 2 / 12)
    (hf : |f| ≤ B * r / 2) :
    |lam * f ^ 2 / (q * r ^ 2) -
        μ * lam * (1 / q ^ 2 + 1 / q) / r ^ 2| ≤
      B ^ 2 / (8 * q₀) +
        B ^ 2 * (1 / q₀ ^ 2 + 1 / q₀) / 24 := by
  have hqpos : 0 < q := hq₀.trans_le hq
  have hqinv : 1 / q ≤ 1 / q₀ := one_div_le_one_div_of_le hq₀ hq
  have hqinv0 : 0 ≤ 1 / q := by positivity
  have hqinv00 : 0 ≤ 1 / q₀ := by positivity
  have hqsum : 1 / q ^ 2 + 1 / q ≤
      1 / q₀ ^ 2 + 1 / q₀ := by
    have hsq : (1 / q) ^ 2 ≤ (1 / q₀) ^ 2 := by gcongr
    have hq2 : 1 / q ^ 2 = (1 / q) ^ 2 := by ring
    have hq02 : 1 / q₀ ^ 2 = (1 / q₀) ^ 2 := by ring
    rw [hq2, hq02]
    exact add_le_add hsq hqinv
  have hqsum0 : 0 ≤ 1 / q ^ 2 + 1 / q := by positivity
  have hf2 : f ^ 2 ≤ B ^ 2 * r ^ 2 / 4 := by
    have hsq := (sq_le_sq₀ (abs_nonneg _)
      (div_nonneg (mul_nonneg hB hr.le) (by norm_num : (0 : ℝ) ≤ 2))).2 hf
    rw [sq_abs] at hsq
    nlinarith only [hsq]
  have hlamf : lam * f ^ 2 ≤ B ^ 2 * r ^ 2 / 8 := by
    calc
      lam * f ^ 2 ≤ (1 / 2 : ℝ) * f ^ 2 :=
        mul_le_mul_of_nonneg_right hlam (sq_nonneg _)
      _ ≤ (1 / 2 : ℝ) * (B ^ 2 * r ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left hf2 (by norm_num)
      _ = B ^ 2 * r ^ 2 / 8 := by ring
  have hlamfdiv : lam * f ^ 2 / r ^ 2 ≤ B ^ 2 / 8 := by
    apply (div_le_iff₀ (sq_pos_of_pos hr)).2
    nlinarith only [hlamf]
  have hmulam : μ * lam ≤ B ^ 2 * r ^ 2 / 24 := by
    calc
      μ * lam ≤ (B ^ 2 * r ^ 2 / 12) * lam :=
        mul_le_mul_of_nonneg_right hμ hlam0
      _ ≤ (B ^ 2 * r ^ 2 / 12) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hlam (by positivity)
      _ = B ^ 2 * r ^ 2 / 24 := by ring
  have hmulamdiv : μ * lam / r ^ 2 ≤ B ^ 2 / 24 := by
    apply (div_le_iff₀ (sq_pos_of_pos hr)).2
    nlinarith only [hmulam]
  have hfirst : lam * f ^ 2 / (q * r ^ 2) ≤ B ^ 2 / (8 * q₀) := by
    have heq : lam * f ^ 2 / (q * r ^ 2) =
        (lam * f ^ 2 / r ^ 2) * (1 / q) := by ring
    rw [heq]
    calc
      (lam * f ^ 2 / r ^ 2) * (1 / q) ≤
          (B ^ 2 / 8) * (1 / q) :=
        mul_le_mul_of_nonneg_right hlamfdiv hqinv0
      _ ≤ (B ^ 2 / 8) * (1 / q₀) :=
        mul_le_mul_of_nonneg_left hqinv (by positivity)
      _ = B ^ 2 / (8 * q₀) := by ring
  have hsecond : μ * lam * (1 / q ^ 2 + 1 / q) / r ^ 2 ≤
      B ^ 2 * (1 / q₀ ^ 2 + 1 / q₀) / 24 := by
    have heq : μ * lam * (1 / q ^ 2 + 1 / q) / r ^ 2 =
        (μ * lam / r ^ 2) * (1 / q ^ 2 + 1 / q) := by ring
    rw [heq]
    calc
      (μ * lam / r ^ 2) * (1 / q ^ 2 + 1 / q) ≤
          (B ^ 2 / 24) * (1 / q ^ 2 + 1 / q) :=
        mul_le_mul_of_nonneg_right hmulamdiv hqsum0
      _ ≤ (B ^ 2 / 24) * (1 / q₀ ^ 2 + 1 / q₀) :=
        mul_le_mul_of_nonneg_left hqsum (by positivity)
      _ = B ^ 2 * (1 / q₀ ^ 2 + 1 / q₀) / 24 := by ring
  have hfirst0 : 0 ≤ lam * f ^ 2 / (q * r ^ 2) := by positivity
  have hsecond0 : 0 ≤ μ * lam * (1 / q ^ 2 + 1 / q) / r ^ 2 := by positivity
  calc
    |lam * f ^ 2 / (q * r ^ 2) -
        μ * lam * (1 / q ^ 2 + 1 / q) / r ^ 2| ≤
      |lam * f ^ 2 / (q * r ^ 2)| +
        |μ * lam * (1 / q ^ 2 + 1 / q) / r ^ 2| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            abs_add_le (lam * f ^ 2 / (q * r ^ 2))
              (-(μ * lam * (1 / q ^ 2 + 1 / q) / r ^ 2))
    _ = lam * f ^ 2 / (q * r ^ 2) +
        μ * lam * (1 / q ^ 2 + 1 / q) / r ^ 2 := by
      rw [abs_of_nonneg hfirst0, abs_of_nonneg hsecond0]
    _ ≤ B ^ 2 / (8 * q₀) +
        B ^ 2 * (1 / q₀ ^ 2 + 1 / q₀) / 24 :=
      add_le_add hfirst hsecond

end ChristodoulouBV.Uniqueness

end
