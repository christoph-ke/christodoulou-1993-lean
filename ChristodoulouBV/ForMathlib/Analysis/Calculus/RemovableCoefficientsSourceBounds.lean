module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsLedger
import Mathlib.Tactic

/-!
# Two-factor source product bounds

These scalar bounds combine two factors vanishing linearly at a diagonal.
Their product vanishes quadratically, and the first jet vanishes linearly.
-/

public section

namespace intervalIntegral

/-- Two linearly vanishing factors give the expected quadratic two-input
product difference coefficient. -/
theorem abs_mul_sub_mul_le_of_linear_gap_bounds
    {d D K₀ KΔ₀ H₀ HΔ₀ k₁ k₂ h₁ h₂ : ℝ}
    (hd : 0 ≤ d) (hD : 0 ≤ D)
    (hK₀ : 0 ≤ K₀) (hKΔ₀ : 0 ≤ KΔ₀)
    (hk₂ : |k₂| ≤ K₀ * d)
    (hkd : |k₁ - k₂| ≤ KΔ₀ * d * D)
    (hh₁ : |h₁| ≤ H₀ * d)
    (hhd : |h₁ - h₂| ≤ HΔ₀ * d * D) :
    |k₁ * h₁ - k₂ * h₂| ≤
      (KΔ₀ * H₀ + K₀ * HΔ₀) * d ^ 2 * D := by
  have hid : k₁ * h₁ - k₂ * h₂ =
      (k₁ - k₂) * h₁ + k₂ * (h₁ - h₂) := by ring
  rw [hid]
  have h₁' : |(k₁ - k₂) * h₁| ≤
      (KΔ₀ * d * D) * (H₀ * d) := by
    rw [abs_mul]
    exact mul_le_mul hkd hh₁ (abs_nonneg _) (by positivity)
  have h₂' : |k₂ * (h₁ - h₂)| ≤
      (K₀ * d) * (HΔ₀ * d * D) := by
    rw [abs_mul]
    exact mul_le_mul hk₂ hhd (abs_nonneg _) (by positivity)
  calc
    _ ≤ |(k₁ - k₂) * h₁| + |k₂ * (h₁ - h₂)| := abs_add_le _ _
    _ ≤ (KΔ₀ * d * D) * (H₀ * d) +
        (K₀ * d) * (HΔ₀ * d * D) := add_le_add h₁' h₂'
    _ = _ := by ring

/-- The four-term two-input derivative coefficient of a product of linearly
vanishing factors. -/
theorem abs_productJet_sub_le_of_linear_gap_bounds
    {d D K₀ K₁ KΔ₀ KΔ₁ H₀ H₁ HΔ₀ HΔ₁ : ℝ}
    {k₁ k₂ ki₁ ki₂ h₁ h₂ hi₁ hi₂ : ℝ}
    (hd : 0 ≤ d) (hD : 0 ≤ D)
    (hK₀ : 0 ≤ K₀) (hKΔ₀ : 0 ≤ KΔ₀)
    (hk₂ : |k₂| ≤ K₀ * d)
    (hkd : |k₁ - k₂| ≤ KΔ₀ * d * D)
    (hki₂ : |ki₂| ≤ K₁)
    (hkid : |ki₁ - ki₂| ≤ KΔ₁ * D)
    (hh₁ : |h₁| ≤ H₀ * d)
    (hhd : |h₁ - h₂| ≤ HΔ₀ * d * D)
    (hhi₁ : |hi₁| ≤ H₁)
    (hhid : |hi₁ - hi₂| ≤ HΔ₁ * D) :
    |(ki₁ * h₁ + k₁ * hi₁) - (ki₂ * h₂ + k₂ * hi₂)| ≤
      (KΔ₁ * H₀ + K₁ * HΔ₀ + KΔ₀ * H₁ + K₀ * HΔ₁) * d * D := by
  have hid : (ki₁ * h₁ + k₁ * hi₁) - (ki₂ * h₂ + k₂ * hi₂) =
      (ki₁ - ki₂) * h₁ + ki₂ * (h₁ - h₂) +
        (k₁ - k₂) * hi₁ + k₂ * (hi₁ - hi₂) := by ring
  rw [hid]
  have h₁' : |(ki₁ - ki₂) * h₁| ≤
      (KΔ₁ * D) * (H₀ * d) := by
    rw [abs_mul]
    exact mul_le_mul hkid hh₁ (abs_nonneg _) ((abs_nonneg _).trans hkid)
  have h₂' : |ki₂ * (h₁ - h₂)| ≤
      K₁ * (HΔ₀ * d * D) := by
    rw [abs_mul]
    exact mul_le_mul hki₂ hhd (abs_nonneg _) (abs_nonneg _ |>.trans hki₂)
  have h₃' : |(k₁ - k₂) * hi₁| ≤
      (KΔ₀ * d * D) * H₁ := by
    rw [abs_mul]
    exact mul_le_mul hkd hhi₁ (abs_nonneg _) (by positivity)
  have h₄' : |k₂ * (hi₁ - hi₂)| ≤
      (K₀ * d) * (HΔ₁ * D) := by
    rw [abs_mul]
    exact mul_le_mul hk₂ hhid (abs_nonneg _) (by positivity)
  have htri : |(ki₁ - ki₂) * h₁ + ki₂ * (h₁ - h₂) +
      (k₁ - k₂) * hi₁ + k₂ * (hi₁ - hi₂)| ≤
      |(ki₁ - ki₂) * h₁| + |ki₂ * (h₁ - h₂)| +
        |(k₁ - k₂) * hi₁| + |k₂ * (hi₁ - hi₂)| := by
    calc
      _ ≤ |(ki₁ - ki₂) * h₁ + ki₂ * (h₁ - h₂) +
          (k₁ - k₂) * hi₁| + |k₂ * (hi₁ - hi₂)| := abs_add_le _ _
      _ ≤ (|(ki₁ - ki₂) * h₁ + ki₂ * (h₁ - h₂)| +
          |(k₁ - k₂) * hi₁|) + |k₂ * (hi₁ - hi₂)| := by
            gcongr; exact abs_add_le _ _
      _ ≤ ((|(ki₁ - ki₂) * h₁| + |ki₂ * (h₁ - h₂)|) +
          |(k₁ - k₂) * hi₁|) + |k₂ * (hi₁ - hi₂)| := by
            gcongr; exact abs_add_le _ _
  calc
    _ ≤ |(ki₁ - ki₂) * h₁| + |ki₂ * (h₁ - h₂)| +
        |(k₁ - k₂) * hi₁| + |k₂ * (hi₁ - hi₂)| := htri
    _ ≤ (KΔ₁ * D) * (H₀ * d) + K₁ * (HΔ₀ * d * D) +
        (KΔ₀ * d * D) * H₁ + (K₀ * d) * (HΔ₁ * D) := by
          exact add_le_add (add_le_add (add_le_add h₁' h₂') h₃') h₄'
    _ = _ := by ring

end intervalIntegral

end
