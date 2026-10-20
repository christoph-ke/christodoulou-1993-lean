module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraKernel
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Two-input differences for quadratic product jets

The scalar product rule is estimated without reference to a particular
weighted mean. This isolates the exact coefficient needed for quadratic
Volterra products.
-/

public section

namespace intervalIntegral

private theorem quadraticProductJet_algebra
    {w₁ w₂ w₁' w₂' H₁ H₂ H₁' H₂' B C L M Hc N D d : ℝ}
    (ht₁ : |(w₁' - w₂') * H₁ ^ 2| ≤ B ^ 2 * d * D)
    (ht₂ : |w₂' * (H₁ - H₂) * (H₁ + H₂)| ≤ 2 * L * B * M * d * D)
    (ht₃ : |2 * (w₁ - w₂) * H₁ * H₁'| ≤ 2 * B * Hc * d * D)
    (ht₄ : |2 * w₂ * (H₁ - H₂) * H₁'| ≤ 2 * C * M * Hc * d * D)
    (ht₅ : |2 * w₂ * H₂ * (H₁' - H₂')| ≤ 2 * C * B * N * d * D) :
    |(w₁' * H₁ ^ 2 + 2 * w₁ * H₁ * H₁') -
      (w₂' * H₂ ^ 2 + 2 * w₂ * H₂ * H₂')| ≤
      (B ^ 2 + 2 * L * B * M +
        2 * (B * Hc + C * M * Hc + C * B * N)) * d * D := by
  have hid : (w₁' * H₁ ^ 2 + 2 * w₁ * H₁ * H₁') -
      (w₂' * H₂ ^ 2 + 2 * w₂ * H₂ * H₂') =
      (w₁' - w₂') * H₁ ^ 2 + w₂' * (H₁ - H₂) * (H₁ + H₂) +
        2 * (w₁ - w₂) * H₁ * H₁' + 2 * w₂ * (H₁ - H₂) * H₁' +
        2 * w₂ * H₂ * (H₁' - H₂') := by ring
  rw [hid]
  have htri :
      |(w₁' - w₂') * H₁ ^ 2 + w₂' * (H₁ - H₂) * (H₁ + H₂) +
        2 * (w₁ - w₂) * H₁ * H₁' + 2 * w₂ * (H₁ - H₂) * H₁' +
        2 * w₂ * H₂ * (H₁' - H₂')| ≤
      |(w₁' - w₂') * H₁ ^ 2| + |w₂' * (H₁ - H₂) * (H₁ + H₂)| +
        |2 * (w₁ - w₂) * H₁ * H₁'| + |2 * w₂ * (H₁ - H₂) * H₁'| +
        |2 * w₂ * H₂ * (H₁' - H₂')| := by
    calc
      _ ≤ |(w₁' - w₂') * H₁ ^ 2 + w₂' * (H₁ - H₂) * (H₁ + H₂) +
          2 * (w₁ - w₂) * H₁ * H₁' + 2 * w₂ * (H₁ - H₂) * H₁'| +
          |2 * w₂ * H₂ * (H₁' - H₂')| := abs_add_le _ _
      _ ≤ (|(w₁' - w₂') * H₁ ^ 2 + w₂' * (H₁ - H₂) * (H₁ + H₂) +
          2 * (w₁ - w₂) * H₁ * H₁'| + |2 * w₂ * (H₁ - H₂) * H₁'|) +
          |2 * w₂ * H₂ * (H₁' - H₂')| := by gcongr; exact abs_add_le _ _
      _ ≤ ((|(w₁' - w₂') * H₁ ^ 2 + w₂' * (H₁ - H₂) * (H₁ + H₂)| +
          |2 * (w₁ - w₂) * H₁ * H₁'|) + |2 * w₂ * (H₁ - H₂) * H₁'|) +
          |2 * w₂ * H₂ * (H₁' - H₂')| := by gcongr; exact abs_add_le _ _
      _ ≤ (((|(w₁' - w₂') * H₁ ^ 2| + |w₂' * (H₁ - H₂) * (H₁ + H₂)|) +
          |2 * (w₁ - w₂) * H₁ * H₁'|) + |2 * w₂ * (H₁ - H₂) * H₁'|) +
          |2 * w₂ * H₂ * (H₁' - H₂')| := by gcongr; exact abs_add_le _ _
      _ = _ := by ring
  exact htri.trans (by nlinarith [ht₁, ht₂, ht₃, ht₄, ht₅])

/-- An algebraic two-input first-jet estimate for a quadratic product. The
coefficient retains the factor from each term of the product rule. -/
theorem abs_quadraticProductJet_sub_le
    {w₁ w₂ w₁' w₂' H₁ H₂ H₁' H₂' B C L M Hc N D d : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hd : 0 ≤ d) (hdle : d ≤ 1)
    (hw₂ : |w₂| ≤ C) (hwdiff : |w₁ - w₂| ≤ D)
    (hw₂' : |w₂'| ≤ L) (hw'diff : |w₁' - w₂'| ≤ D)
    (hH₁ : |H₁| ≤ B * d) (hH₂ : |H₂| ≤ B * d)
    (hHdiff : |H₁ - H₂| ≤ M * d * D)
    (hH₁' : |H₁'| ≤ Hc) (hH'diff : |H₁' - H₂'| ≤ N * D) :
    |(w₁' * H₁ ^ 2 + 2 * w₁ * H₁ * H₁') -
      (w₂' * H₂ ^ 2 + 2 * w₂ * H₂ * H₂')| ≤
      (B ^ 2 + 2 * L * B * M +
        2 * (B * Hc + C * M * Hc + C * B * N)) * d * D := by
  have hBd : 0 ≤ B * d := mul_nonneg hB hd
  have hMdD : 0 ≤ M * d * D := mul_nonneg (mul_nonneg hM hd) hD
  have hsq : H₁ ^ 2 ≤ B ^ 2 * d ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg H₁) hBd).2 hH₁
    nlinarith [sq_abs H₁]
  have hsq' : H₁ ^ 2 ≤ B ^ 2 * d := by
    have hdd : d ^ 2 ≤ d := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hdd (sq_nonneg B)]
  have hsum : |H₁ + H₂| ≤ 2 * B * d := by
    have h := (abs_add_le H₁ H₂).trans (add_le_add hH₁ hH₂)
    nlinarith
  have ht₁ : |(w₁' - w₂') * H₁ ^ 2| ≤ B ^ 2 * d * D := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg H₁)]
    have h := mul_le_mul hw'diff hsq' (sq_nonneg H₁) hD
    nlinarith
  have ht₂ : |w₂' * (H₁ - H₂) * (H₁ + H₂)| ≤
      2 * L * B * M * d * D := by
    rw [abs_mul, abs_mul]
    have hds := mul_le_mul hHdiff hsum (abs_nonneg _) hMdD
    have hds' : |H₁ - H₂| * |H₁ + H₂| ≤ 2 * B * M * d * D := by
      have hdd : d ^ 2 ≤ d := by nlinarith
      have hcoef : 0 ≤ 2 * B * M * D := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hdd hcoef]
    have h := mul_le_mul hw₂' hds' (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hL
    nlinarith
  have ht₃ : |2 * (w₁ - w₂) * H₁ * H₁'| ≤
      2 * B * Hc * d * D := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hwh := mul_le_mul hwdiff hH₁ (abs_nonneg H₁) hD
    have hwh' : |w₁ - w₂| * |H₁| ≤ D * (B * d) := hwh
    have h := mul_le_mul hwh' hH₁' (abs_nonneg H₁')
      (mul_nonneg hD hBd)
    nlinarith
  have ht₄ : |2 * w₂ * (H₁ - H₂) * H₁'| ≤
      2 * C * M * Hc * d * D := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hwh := mul_le_mul hw₂ hHdiff (abs_nonneg _) hC
    have h := mul_le_mul hwh hH₁' (abs_nonneg H₁')
      (mul_nonneg hC hMdD)
    nlinarith
  have ht₅ : |2 * w₂ * H₂ * (H₁' - H₂')| ≤
      2 * C * B * N * d * D := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hwh := mul_le_mul hw₂ hH₂ (abs_nonneg H₂) hC
    have h := mul_le_mul hwh hH'diff (abs_nonneg _)
      (mul_nonneg hC hBd)
    nlinarith
  exact quadraticProductJet_algebra ht₁ ht₂ ht₃ ht₄ ht₅

/-- The exact two-input derivative difference for quadratic weighted-mean
kernels, given pointwise box and mean-error estimates. -/
theorem abs_fderivWithin_weightedDiagonalQuadraticKernel_sub_le_of_bounds
    {a b : ℝ} (hab : a < b)
    {w₁ w₂ f₁ f₂ : ℝ × ℝ → ℝ}
    {Gw₁ Gw₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hjetw₁ : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt w₁ (Gw₁ p) (closedCoordTriangle a b) p)
    (hjetw₂ : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt w₂ (Gw₂ p) (closedCoordTriangle a b) p)
    (hC1₁ : ContDiffOn ℝ 1 (weightedDiagonalError w₁ f₁)
      (closedCoordTriangle a b))
    (hC1₂ : ContDiffOn ℝ 1 (weightedDiagonalError w₂ f₂)
      (closedCoordTriangle a b))
    {B C L M Hc N D : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hD : 0 ≤ D)
    {p e : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hdle : p.2 - p.1 ≤ 1)
    (hw₂ : |w₂ p| ≤ C) (hwdiff : |w₁ p - w₂ p| ≤ D)
    (hGw₂ : |Gw₂ p e| ≤ L)
    (hGwdiff : |Gw₁ p e - Gw₂ p e| ≤ D)
    (hH₁ : |weightedDiagonalError w₁ f₁ p| ≤ B * (p.2 - p.1))
    (hH₂ : |weightedDiagonalError w₂ f₂ p| ≤ B * (p.2 - p.1))
    (hHdiff : |weightedDiagonalError w₁ f₁ p -
      weightedDiagonalError w₂ f₂ p| ≤ M * (p.2 - p.1) * D)
    (hGH₁ : |(fderivWithin ℝ (weightedDiagonalError w₁ f₁)
      (closedCoordTriangle a b) p) e| ≤ Hc)
    (hGHdiff : |(fderivWithin ℝ (weightedDiagonalError w₁ f₁)
      (closedCoordTriangle a b) p) e -
      (fderivWithin ℝ (weightedDiagonalError w₂ f₂)
      (closedCoordTriangle a b) p) e| ≤ N * D) :
    |(fderivWithin ℝ (weightedDiagonalQuadraticKernel w₁ f₁)
      (closedCoordTriangle a b) p) e -
      (fderivWithin ℝ (weightedDiagonalQuadraticKernel w₂ f₂)
      (closedCoordTriangle a b) p) e| ≤
      (B ^ 2 + 2 * L * B * M +
        2 * (B * Hc + C * M * Hc + C * B * N)) * (p.2 - p.1) * D := by
  rw [fderivWithin_weightedDiagonalQuadraticKernel_apply hab hjetw₁ hC1₁ hp,
    fderivWithin_weightedDiagonalQuadraticKernel_apply hab hjetw₂ hC1₂ hp]
  change a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b at hp
  exact abs_quadraticProductJet_sub_le hB hC hL hM hD
    (sub_nonneg.mpr hp.2.1) hdle hw₂ hwdiff hGw₂ hGwdiff
    hH₁ hH₂ hHdiff hGH₁ hGHdiff

end intervalIntegral

end
