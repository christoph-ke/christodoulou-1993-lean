module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsProducts
import Mathlib.Tactic

/-!
# Three-factor product bounds for removable coefficients

The bounds retain the contribution of each changed factor. They apply to
ordinary scalar values or to one coordinate of a product-rule first jet.
-/

public section

namespace intervalIntegral

/-- A two-input estimate for a product of three real factors. -/
theorem abs_triple_mul_sub_le
    {a₁ a₂ b₁ b₂ c₁ c₂ A B C Ad Bd Cd : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAd : 0 ≤ Ad) (hBd : 0 ≤ Bd)
    (ha₂ : |a₂| ≤ A) (hb₁ : |b₁| ≤ B) (hb₂ : |b₂| ≤ B)
    (hc₁ : |c₁| ≤ C)
    (had : |a₁ - a₂| ≤ Ad) (hbd : |b₁ - b₂| ≤ Bd)
    (hcd : |c₁ - c₂| ≤ Cd) :
    |a₁ * b₁ * c₁ - a₂ * b₂ * c₂| ≤
      Ad * B * C + A * Bd * C + A * B * Cd := by
  have hid : a₁ * b₁ * c₁ - a₂ * b₂ * c₂ =
      (a₁ - a₂) * b₁ * c₁ + a₂ * (b₁ - b₂) * c₁ +
        a₂ * b₂ * (c₁ - c₂) := by ring
  rw [hid]
  have h₁ : |(a₁ - a₂) * b₁ * c₁| ≤ Ad * B * C := by
    repeat rw [abs_mul]
    exact mul_le_mul (mul_le_mul had hb₁ (abs_nonneg _) hAd) hc₁
      (abs_nonneg _) (mul_nonneg hAd hB)
  have h₂ : |a₂ * (b₁ - b₂) * c₁| ≤ A * Bd * C := by
    repeat rw [abs_mul]
    exact mul_le_mul (mul_le_mul ha₂ hbd (abs_nonneg _) hA) hc₁
      (abs_nonneg _) (mul_nonneg hA hBd)
  have h₃ : |a₂ * b₂ * (c₁ - c₂)| ≤ A * B * Cd := by
    repeat rw [abs_mul]
    exact mul_le_mul (mul_le_mul ha₂ hb₂ (abs_nonneg _) hA) hcd
      (abs_nonneg _) (mul_nonneg hA hB)
  calc
    _ ≤ |(a₁ - a₂) * b₁ * c₁ + a₂ * (b₁ - b₂) * c₁| +
        |a₂ * b₂ * (c₁ - c₂)| := abs_add_le _ _
    _ ≤ (|(a₁ - a₂) * b₁ * c₁| +
        |a₂ * (b₁ - b₂) * c₁|) +
        |a₂ * b₂ * (c₁ - c₂)| := by gcongr; exact abs_add_le _ _
    _ ≤ (Ad * B * C + A * Bd * C) + A * B * Cd := by
      exact add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by ring

/-- The three-factor product-rule jet is bounded by the sum of the three
individual derivative contributions. -/
theorem abs_tripleProductJet_le
    {a b c ai bi ci A Ai B Bi C Ci : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAi : 0 ≤ Ai) (hBi : 0 ≤ Bi)
    (ha : |a| ≤ A) (hai : |ai| ≤ Ai)
    (hb : |b| ≤ B) (hbi : |bi| ≤ Bi)
    (hc : |c| ≤ C) (hci : |ci| ≤ Ci) :
    |ai * b * c + a * bi * c + a * b * ci| ≤
      Ai * B * C + A * Bi * C + A * B * Ci := by
  have h₁ : |ai * b * c| ≤ Ai * B * C := by
    repeat rw [abs_mul]
    exact mul_le_mul (mul_le_mul hai hb (abs_nonneg _) hAi) hc
      (abs_nonneg _) (mul_nonneg hAi hB)
  have h₂ : |a * bi * c| ≤ A * Bi * C := by
    repeat rw [abs_mul]
    exact mul_le_mul (mul_le_mul ha hbi (abs_nonneg _) hA) hc
      (abs_nonneg _) (mul_nonneg hA hBi)
  have h₃ : |a * b * ci| ≤ A * B * Ci := by
    repeat rw [abs_mul]
    exact mul_le_mul (mul_le_mul ha hb (abs_nonneg _) hA) hci
      (abs_nonneg _) (mul_nonneg hA hB)
  calc
    _ ≤ |ai * b * c + a * bi * c| + |a * b * ci| := abs_add_le _ _
    _ ≤ (|ai * b * c| + |a * bi * c|) + |a * b * ci| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ (Ai * B * C + A * Bi * C) + A * B * Ci :=
      add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by ring

end intervalIntegral

end
