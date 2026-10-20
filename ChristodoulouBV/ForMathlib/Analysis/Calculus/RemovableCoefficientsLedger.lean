module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsProductBounds
import Mathlib.Tactic

/-!
# Gap-scaled two-input product ledgers

These purely scalar estimates assemble the value and first-jet bounds for a
product with one linearly vanishing factor and one derivative that vanishes
linearly. They preserve the nine product-rule difference contributions.
-/

public section

namespace intervalIntegral

/-- The two-input value bound for three factors when the first factor
vanishes linearly and the third-factor difference vanishes quadratically. -/
theorem abs_triple_mul_sub_le_of_gap_bounds
    {d D A₀ AΔ₀ W₀ WΔ₀ Z₀ ZΔ₀ : ℝ}
    {a₁ a₂ w₁ w₂ z₁ z₂ : ℝ}
    (hd : 0 ≤ d) (hdle : d ≤ 1) (hD : 0 ≤ D)
    (hA₀ : 0 ≤ A₀) (hAΔ₀ : 0 ≤ AΔ₀)
    (hW₀ : 0 ≤ W₀) (hWΔ₀ : 0 ≤ WΔ₀)
    (hZΔ₀ : 0 ≤ ZΔ₀)
    (ha₂ : |a₂| ≤ A₀ * d)
    (had : |a₁ - a₂| ≤ AΔ₀ * d * D)
    (hw₁ : |w₁| ≤ W₀) (hw₂ : |w₂| ≤ W₀)
    (hwd : |w₁ - w₂| ≤ WΔ₀ * D)
    (hz₁ : |z₁| ≤ Z₀)
    (hzd : |z₁ - z₂| ≤ ZΔ₀ * d ^ 2 * D) :
    |a₁ * w₁ * z₁ - a₂ * w₂ * z₂| ≤
      (AΔ₀ * W₀ * Z₀ + A₀ * WΔ₀ * Z₀ +
        A₀ * W₀ * ZΔ₀) * d * D := by
  have h := abs_triple_mul_sub_le
    (mul_nonneg hA₀ hd) hW₀
    (mul_nonneg (mul_nonneg hAΔ₀ hd) hD)
    (mul_nonneg hWΔ₀ hD)
    ha₂ hw₁ hw₂ hz₁ had hwd hzd
  have hdsq : d ^ 2 ≤ 1 := by nlinarith only [hd, hdle]
  have hlast : A₀ * d * W₀ * (ZΔ₀ * d ^ 2 * D) ≤
      A₀ * W₀ * ZΔ₀ * d * D := by
    have hcoef : 0 ≤ A₀ * W₀ * ZΔ₀ * d * D := by positivity
    nlinarith only [mul_le_mul_of_nonneg_left hdsq hcoef]
  calc
    _ ≤ AΔ₀ * d * D * W₀ * Z₀ +
        A₀ * d * (WΔ₀ * D) * Z₀ +
        A₀ * d * W₀ * (ZΔ₀ * d ^ 2 * D) := h
    _ ≤ AΔ₀ * d * D * W₀ * Z₀ +
        A₀ * d * (WΔ₀ * D) * Z₀ +
        A₀ * W₀ * ZΔ₀ * d * D := by gcongr
    _ = _ := by ring

/-- The exact nine-term two-input derivative coefficient for a product
`a*w*z`, after discarding gap factors bounded by one. -/
theorem abs_tripleProductJet_sub_le_of_gap_bounds
    {d D A₀ A₁ AΔ₀ AΔ₁ W₀ W₁ WΔ₀ WΔ₁ Z₀ Z₁ ZΔ₀ ZΔ₁ : ℝ}
    {a₁ a₂ ai₁ ai₂ w₁ w₂ wi₁ wi₂ z₁ z₂ zi₁ zi₂ : ℝ}
    (hd : 0 ≤ d) (hdle : d ≤ 1) (hD : 0 ≤ D)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAΔ₀ : 0 ≤ AΔ₀) (hAΔ₁ : 0 ≤ AΔ₁)
    (hW₀ : 0 ≤ W₀) (hW₁ : 0 ≤ W₁)
    (hWΔ₀ : 0 ≤ WΔ₀) (hWΔ₁ : 0 ≤ WΔ₁)
    (hZ₁ : 0 ≤ Z₁)
    (hZΔ₀ : 0 ≤ ZΔ₀) (hZΔ₁ : 0 ≤ ZΔ₁)
    (ha₂ : |a₂| ≤ A₀ * d)
    (had : |a₁ - a₂| ≤ AΔ₀ * d * D)
    (hai₂ : |ai₂| ≤ A₁)
    (haid : |ai₁ - ai₂| ≤ AΔ₁ * D)
    (hw₁ : |w₁| ≤ W₀) (hw₂ : |w₂| ≤ W₀)
    (hwd : |w₁ - w₂| ≤ WΔ₀ * D)
    (hwi₁ : |wi₁| ≤ W₁) (hwi₂ : |wi₂| ≤ W₁)
    (hwid : |wi₁ - wi₂| ≤ WΔ₁ * D)
    (hz₁ : |z₁| ≤ Z₀)
    (hzd : |z₁ - z₂| ≤ ZΔ₀ * d ^ 2 * D)
    (hzi₁ : |zi₁| ≤ Z₁ * d)
    (hzid : |zi₁ - zi₂| ≤ ZΔ₁ * d * D) :
    |(ai₁ * w₁ * z₁ + a₁ * wi₁ * z₁ + a₁ * w₁ * zi₁) -
      (ai₂ * w₂ * z₂ + a₂ * wi₂ * z₂ + a₂ * w₂ * zi₂)| ≤
      (AΔ₁ * W₀ * Z₀ + A₁ * WΔ₀ * Z₀ + A₁ * W₀ * ZΔ₀ +
        AΔ₀ * W₁ * Z₀ + A₀ * WΔ₁ * Z₀ + A₀ * W₁ * ZΔ₀ +
        AΔ₀ * W₀ * Z₁ + A₀ * WΔ₀ * Z₁ + A₀ * W₀ * ZΔ₁) * D := by
  have hdsq : d ^ 2 ≤ 1 := by nlinarith only [hd, hdle]
  have ha₂' : |a₂| ≤ A₀ :=
    ha₂.trans (by nlinarith only [mul_le_mul_of_nonneg_left hdle hA₀])
  have had' : |a₁ - a₂| ≤ AΔ₀ * D := by
    have hcoef : 0 ≤ AΔ₀ * D := mul_nonneg hAΔ₀ hD
    nlinarith only [had, mul_le_mul_of_nonneg_left hdle hcoef]
  have hzd' : |z₁ - z₂| ≤ ZΔ₀ * D := by
    have hcoef : 0 ≤ ZΔ₀ * D := mul_nonneg hZΔ₀ hD
    nlinarith only [hzd, mul_le_mul_of_nonneg_left hdsq hcoef]
  have hzi₁' : |zi₁| ≤ Z₁ :=
    hzi₁.trans (by nlinarith only [mul_le_mul_of_nonneg_left hdle hZ₁])
  have hzid' : |zi₁ - zi₂| ≤ ZΔ₁ * D := by
    have hcoef : 0 ≤ ZΔ₁ * D := mul_nonneg hZΔ₁ hD
    nlinarith only [hzid, mul_le_mul_of_nonneg_left hdle hcoef]
  have h₁ := abs_triple_mul_sub_le hA₁ hW₀
    (mul_nonneg hAΔ₁ hD) (mul_nonneg hWΔ₀ hD)
    hai₂ hw₁ hw₂ hz₁ haid hwd hzd'
  have h₂ := abs_triple_mul_sub_le hA₀ hW₁
    (mul_nonneg hAΔ₀ hD) (mul_nonneg hWΔ₁ hD)
    ha₂' hwi₁ hwi₂ hz₁ had' hwid hzd'
  have h₃ := abs_triple_mul_sub_le hA₀ hW₀
    (mul_nonneg hAΔ₀ hD) (mul_nonneg hWΔ₀ hD)
    ha₂' hw₁ hw₂ hzi₁' had' hwd hzid'
  have hid : (ai₁ * w₁ * z₁ + a₁ * wi₁ * z₁ + a₁ * w₁ * zi₁) -
      (ai₂ * w₂ * z₂ + a₂ * wi₂ * z₂ + a₂ * w₂ * zi₂) =
      (ai₁ * w₁ * z₁ - ai₂ * w₂ * z₂) +
        (a₁ * wi₁ * z₁ - a₂ * wi₂ * z₂) +
        (a₁ * w₁ * zi₁ - a₂ * w₂ * zi₂) := by ring
  rw [hid]
  have htri : |(ai₁ * w₁ * z₁ - ai₂ * w₂ * z₂) +
      (a₁ * wi₁ * z₁ - a₂ * wi₂ * z₂) +
      (a₁ * w₁ * zi₁ - a₂ * w₂ * zi₂)| ≤
      |ai₁ * w₁ * z₁ - ai₂ * w₂ * z₂| +
        |a₁ * wi₁ * z₁ - a₂ * wi₂ * z₂| +
        |a₁ * w₁ * zi₁ - a₂ * w₂ * zi₂| := by
    calc
      _ ≤ |(ai₁ * w₁ * z₁ - ai₂ * w₂ * z₂) +
          (a₁ * wi₁ * z₁ - a₂ * wi₂ * z₂)| +
          |a₁ * w₁ * zi₁ - a₂ * w₂ * zi₂| := abs_add_le _ _
      _ ≤ (|ai₁ * w₁ * z₁ - ai₂ * w₂ * z₂| +
          |a₁ * wi₁ * z₁ - a₂ * wi₂ * z₂|) +
          |a₁ * w₁ * zi₁ - a₂ * w₂ * zi₂| := by
            gcongr
            exact abs_add_le _ _
  calc
    _ ≤ |ai₁ * w₁ * z₁ - ai₂ * w₂ * z₂| +
        |a₁ * wi₁ * z₁ - a₂ * wi₂ * z₂| +
        |a₁ * w₁ * zi₁ - a₂ * w₂ * zi₂| := htri
    _ ≤ (AΔ₁ * D * W₀ * Z₀ + A₁ * (WΔ₀ * D) * Z₀ +
          A₁ * W₀ * (ZΔ₀ * D)) +
        (AΔ₀ * D * W₁ * Z₀ + A₀ * (WΔ₁ * D) * Z₀ +
          A₀ * W₁ * (ZΔ₀ * D)) +
        (AΔ₀ * D * W₀ * Z₁ + A₀ * (WΔ₀ * D) * Z₁ +
          A₀ * W₀ * (ZΔ₁ * D)) := by
            exact add_le_add (add_le_add h₁ h₂) h₃
    _ = _ := by ring

end intervalIntegral

end
