module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsSourceBounds
import Mathlib.Tactic

/-!
# Quotient bounds for quadratic source coefficients

The denominator stays uniformly positive, while the numerator vanishes
quadratically and its first jet vanishes linearly. The scalar estimates
retain the five quotient-rule difference terms.
-/

public section

namespace intervalIntegral

/-- A uniformly positive denominator preserves the quadratic value bound. -/
theorem abs_div_le_of_quadratic_gap_bound
    {c d P₀ lam P : ℝ} (hc : 0 < c)
    (hlam : c ≤ lam) (hP : |P| ≤ P₀ * d ^ 2) :
    |P / lam| ≤ (P₀ / c) * d ^ 2 := by
  have hlampos : 0 < lam := hc.trans_le hlam
  have hP₀ : 0 ≤ P₀ * d ^ 2 := (abs_nonneg _).trans hP
  rw [abs_div, abs_of_pos hlampos]
  calc
    _ ≤ (P₀ * d ^ 2) / c := by gcongr
    _ = (P₀ / c) * d ^ 2 := by ring

/-- The two-input value bound for quadratic numerators over a uniformly
positive denominator. -/
theorem abs_div_sub_div_le_of_quadratic_gap_bounds
    {c d D P₀ PΔ₀ lam₁ lam₂ P₁ P₂ : ℝ}
    (hc : 0 < c)
    (hlam₁ : c ≤ lam₁) (hlam₂ : c ≤ lam₂)
    (hlamdiff : |lam₁ - lam₂| ≤ D)
    (hP₂ : |P₂| ≤ P₀ * d ^ 2)
    (hPdiff : |P₁ - P₂| ≤ PΔ₀ * d ^ 2 * D) :
    |P₁ / lam₁ - P₂ / lam₂| ≤
      (PΔ₀ / c + P₀ / c ^ 2) * d ^ 2 * D := by
  have h := abs_div_sub_div_le hc hlam₁ hlam₂ hPdiff hlamdiff hP₂
  calc
    _ ≤ (PΔ₀ * d ^ 2 * D) / c +
        (P₀ * d ^ 2) * D / c ^ 2 := h
    _ = (PΔ₀ / c + P₀ / c ^ 2) * d ^ 2 * D := by ring

/-- The quotient-rule first jet has a linear gap bound when its numerator
vanishes quadratically. -/
theorem abs_quotientJet_le_of_quadratic_gap_bounds
    {c d P₀ P₁ L lam P Pi Li : ℝ}
    (hc : 0 < c) (hd : 0 ≤ d) (hdle : d ≤ 1)
    (hP₀ : 0 ≤ P₀)
    (hlam : c ≤ lam)
    (hP : |P| ≤ P₀ * d ^ 2)
    (hPi : |Pi| ≤ P₁ * d)
    (hLi : |Li| ≤ L) :
    |Pi / lam - P * Li / lam ^ 2| ≤
      (P₁ / c + P₀ * L / c ^ 2) * d := by
  have hPd : |P| ≤ P₀ * d := by
    have hdsq : d ^ 2 ≤ d := by nlinarith only [hd, hdle]
    exact hP.trans (mul_le_mul_of_nonneg_left hdsq hP₀)
  have h := abs_quotientJet_le_of_bounds hc (by norm_num : (0 : ℝ) < 1)
    (by simpa using hlam) (by simpa using hPd)
    (by simpa using hPi) hLi
  convert h using 1
  ring

/-- The five-term two-input derivative coefficient for a quadratic numerator
over a uniformly positive denominator. -/
theorem abs_quotientJet_sub_le_of_quadratic_gap_bounds
    {c d D P₀ P₁ PΔ₀ PΔ₁ L LΔ : ℝ}
    {lam₁ lam₂ P₁v P₂v Pi₁ Pi₂ Li₁ Li₂ : ℝ}
    (hc : 0 < c) (hd : 0 ≤ d) (hdle : d ≤ 1)
    (hD : 0 ≤ D) (hP₀ : 0 ≤ P₀) (hP₁ : 0 ≤ P₁)
    (hPΔ₀ : 0 ≤ PΔ₀) (hPΔ₁ : 0 ≤ PΔ₁)
    (hL : 0 ≤ L) (hLΔ : 0 ≤ LΔ)
    (hlam₁ : c ≤ lam₁) (hlam₂ : c ≤ lam₂)
    (hlamdiff : |lam₁ - lam₂| ≤ D)
    (hP₂ : |P₂v| ≤ P₀ * d ^ 2)
    (hPdiff : |P₁v - P₂v| ≤ PΔ₀ * d ^ 2 * D)
    (hPi₂ : |Pi₂| ≤ P₁ * d)
    (hPidiff : |Pi₁ - Pi₂| ≤ PΔ₁ * d * D)
    (hLi₁ : |Li₁| ≤ L) (hLi₂ : |Li₂| ≤ L)
    (hLidiff : |Li₁ - Li₂| ≤ LΔ * D) :
    |(Pi₁ / lam₁ - P₁v * Li₁ / lam₁ ^ 2) -
      (Pi₂ / lam₂ - P₂v * Li₂ / lam₂ ^ 2)| ≤
      (PΔ₁ / c + P₁ / c ^ 2 + PΔ₀ * L / c ^ 2 +
        P₀ * LΔ / c ^ 2 + 2 * P₀ * L / c ^ 3) * d * D := by
  have hdsq : d ^ 2 ≤ d := by nlinarith only [hd, hdle]
  have hP₂' : |P₂v| ≤ (P₀ * d) :=
    hP₂.trans (mul_le_mul_of_nonneg_left hdsq hP₀)
  have hPdiff' : |P₁v - P₂v| ≤ (PΔ₀ * d) * D := by
    have hcoef : 0 ≤ PΔ₀ * D := mul_nonneg hPΔ₀ hD
    nlinarith only [hPdiff, mul_le_mul_of_nonneg_left hdsq hcoef]
  have h := abs_quotientJet_sub_le hc
    (mul_nonneg hP₀ hd) (mul_nonneg hP₁ hd)
    (mul_nonneg hPΔ₀ hd) (mul_nonneg hPΔ₁ hd)
    hL hLΔ hD hlam₁ hlam₂ hlamdiff hP₂' hPdiff'
    hPi₂ hPidiff hLi₁ hLi₂ hLidiff
  convert h using 1
  ring

end intervalIntegral

end
