module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraKernelEstimates
import Mathlib.Tactic

/-!
# Quotients with cubic diagonal vanishing

These scalar estimates apply when a numerator and its first derivative vanish
to orders three and two, while the denominator vanishes linearly. They are
independent of the source of the functions involved.
-/

public section

namespace intervalIntegral

/-- A cubically vanishing numerator divided by a linearly positive denominator
vanishes quadratically. -/
theorem abs_div_le_of_cubic_gap_bound
    {c d j₀ r j : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hr : c * d ≤ r) (hj : |j| ≤ j₀ * d ^ 3) :
    |j / r| ≤ (j₀ / c) * d ^ 2 := by
  have hrpos : 0 < r := (mul_pos hc hd).trans_le hr
  have hj₀ : 0 ≤ j₀ * d ^ 3 := (abs_nonneg _).trans hj
  rw [abs_div, abs_of_pos hrpos]
  calc
    _ ≤ (j₀ * d ^ 3) / (c * d) := by gcongr
    _ = (j₀ / c) * d ^ 2 := by field_simp [hc.ne', hd.ne']

/-- The two-input value estimate for cubically vanishing numerators and
linearly positive denominators. -/
theorem abs_div_sub_div_le_of_cubic_gap_bounds
    {c d j₀ jΔ₀ D r₁ r₂ j₁ j₂ : ℝ}
    (hc : 0 < c) (hd : 0 < d)
    (hr₁ : c * d ≤ r₁) (hr₂ : c * d ≤ r₂)
    (hrdiff : |r₁ - r₂| ≤ d * D)
    (hj₂ : |j₂| ≤ j₀ * d ^ 3)
    (hjdiff : |j₁ - j₂| ≤ jΔ₀ * d ^ 3 * D) :
    |j₁ / r₁ - j₂ / r₂| ≤
      (jΔ₀ / c + j₀ / c ^ 2) * d ^ 2 * D := by
  have h := abs_div_sub_div_le (mul_pos hc hd) hr₁ hr₂ hjdiff hrdiff hj₂
  calc
    _ ≤ (jΔ₀ * d ^ 3 * D) / (c * d) +
        (j₀ * d ^ 3) * (d * D) / (c * d) ^ 2 := h
    _ = (jΔ₀ / c + j₀ / c ^ 2) * d ^ 2 * D := by
      field_simp [hc.ne', hd.ne']

/-- The ordinary quotient-rule expression for a cubically vanishing
numerator has a first-order bound. -/
theorem abs_quotientJet_le_of_cubic_gap_bounds
    {c d j₀ j₁ R r j ji ri : ℝ}
    (hc : 0 < c) (hd : 0 < d)
    (hr : c * d ≤ r)
    (hj : |j| ≤ j₀ * d ^ 3)
    (hji : |ji| ≤ j₁ * d ^ 2)
    (hri : |ri| ≤ R) :
    |ji / r - j * ri / r ^ 2| ≤
      (j₁ / c + j₀ * R / c ^ 2) * d := by
  have hρ : c ≤ r / d := (le_div_iff₀ hd).2 (by nlinarith only [hr])
  have hJ : |j / d ^ 3| ≤ j₀ := by
    rw [abs_div, abs_of_pos (pow_pos hd 3)]
    exact (div_le_iff₀ (pow_pos hd 3)).2 (by nlinarith only [hj])
  have hP : |ji / d ^ 2| ≤ j₁ := by
    rw [abs_div, abs_of_pos (pow_pos hd 2)]
    exact (div_le_iff₀ (pow_pos hd 2)).2 (by nlinarith only [hji])
  have h := abs_quotientJet_le_of_bounds hc (show 0 < (1 : ℝ) by norm_num)
    (by simpa using hρ) (by simpa using hJ) (by simpa using hP) hri
  have hrne : r ≠ 0 := ne_of_gt ((mul_pos hc hd).trans_le hr)
  have hid : (ji / d ^ 2) / (r / d) -
      (j / d ^ 3) * ri / (r / d) ^ 2 =
      (ji / r - j * ri / r ^ 2) / d := by
    field_simp [hd.ne', hrne]
  rw [hid] at h
  rw [abs_div, abs_of_pos hd] at h
  exact (div_le_iff₀ hd).1 h

/-- Two quotient-rule expressions for cubic numerators differ by at most a
first-order factor times the normalized five-term quotient coefficient. -/
theorem abs_quotientJet_sub_le_of_cubic_gap_bounds
    {c d j₀ j₁ jΔ₀ jΔ₁ R RΔ D : ℝ}
    {r₁ r₂ J₁ J₂ P₁ P₂ S₁ S₂ : ℝ}
    (hc : 0 < c) (hd : 0 < d)
    (hj₀ : 0 ≤ j₀) (hj₁ : 0 ≤ j₁)
    (hjΔ₀ : 0 ≤ jΔ₀) (hjΔ₁ : 0 ≤ jΔ₁)
    (hR : 0 ≤ R) (hRΔ : 0 ≤ RΔ) (hD : 0 ≤ D)
    (hr₁ : c * d ≤ r₁) (hr₂ : c * d ≤ r₂)
    (hrdiff : |r₁ - r₂| ≤ d * D)
    (hJ₂ : |J₂| ≤ j₀ * d ^ 3)
    (hJdiff : |J₁ - J₂| ≤ jΔ₀ * d ^ 3 * D)
    (hP₂ : |P₂| ≤ j₁ * d ^ 2)
    (hPdiff : |P₁ - P₂| ≤ jΔ₁ * d ^ 2 * D)
    (hS₁ : |S₁| ≤ R) (hS₂ : |S₂| ≤ R)
    (hSdiff : |S₁ - S₂| ≤ RΔ * D) :
    |(P₁ / r₁ - J₁ * S₁ / r₁ ^ 2) -
      (P₂ / r₂ - J₂ * S₂ / r₂ ^ 2)| ≤
      (jΔ₁ / c + j₁ / c ^ 2 + jΔ₀ * R / c ^ 2 +
        j₀ * RΔ / c ^ 2 + 2 * j₀ * R / c ^ 3) * d * D := by
  have hρ₁ : c ≤ r₁ / d := (le_div_iff₀ hd).2 (by nlinarith only [hr₁])
  have hρ₂ : c ≤ r₂ / d := (le_div_iff₀ hd).2 (by nlinarith only [hr₂])
  have hρdiff : |r₁ / d - r₂ / d| ≤ D := by
    rw [← sub_div, abs_div, abs_of_pos hd]
    exact (div_le_iff₀ hd).2 (by simpa only [mul_comm] using hrdiff)
  have hJ₂' : |J₂ / d ^ 3| ≤ j₀ := by
    rw [abs_div, abs_of_pos (pow_pos hd 3)]
    exact (div_le_iff₀ (pow_pos hd 3)).2 (by nlinarith only [hJ₂])
  have hJdiff' : |J₁ / d ^ 3 - J₂ / d ^ 3| ≤ jΔ₀ * D := by
    rw [← sub_div, abs_div, abs_of_pos (pow_pos hd 3)]
    exact (div_le_iff₀ (pow_pos hd 3)).2 (by nlinarith only [hJdiff])
  have hP₂' : |P₂ / d ^ 2| ≤ j₁ := by
    rw [abs_div, abs_of_pos (pow_pos hd 2)]
    exact (div_le_iff₀ (pow_pos hd 2)).2 (by nlinarith only [hP₂])
  have hPdiff' : |P₁ / d ^ 2 - P₂ / d ^ 2| ≤ jΔ₁ * D := by
    rw [← sub_div, abs_div, abs_of_pos (pow_pos hd 2)]
    exact (div_le_iff₀ (pow_pos hd 2)).2 (by nlinarith only [hPdiff])
  have h := abs_quotientJet_sub_le hc hj₀ hj₁ hjΔ₀ hjΔ₁ hR hRΔ hD
    hρ₁ hρ₂ hρdiff hJ₂' hJdiff' hP₂' hPdiff' hS₁ hS₂ hSdiff
  have hnorm : ∀ r J P S : ℝ, r ≠ 0 →
      (P / d ^ 2) / (r / d) - (J / d ^ 3) * S / (r / d) ^ 2 =
        (P / r - J * S / r ^ 2) / d := by
    intro r J P S hr
    field_simp [hd.ne', hr]
  rw [hnorm r₁ J₁ P₁ S₁ (ne_of_gt ((mul_pos hc hd).trans_le hr₁)),
    hnorm r₂ J₂ P₂ S₂ (ne_of_gt ((mul_pos hc hd).trans_le hr₂))] at h
  rw [← sub_div, abs_div, abs_of_pos hd] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using (div_le_iff₀ hd).1 h

end intervalIntegral

end
