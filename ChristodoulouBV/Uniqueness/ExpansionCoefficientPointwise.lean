module

public import ChristodoulouBV.Uniqueness.ExpansionCoefficientDifference

/-!
# Pointwise expansion coefficient estimates

The same algebra applies to the outgoing and incoming coefficients. The
absolute value estimate keeps the mass and radius errors separate so each
can be integrated with its appropriate comparison norm.
-/

@[expose] public section

namespace ChristodoulouBV.Uniqueness

private theorem coefficient_difference_abs_le
    {K A dx x dr r dm μ g : ℝ}
    (hA : 0 ≤ A) (hr : 0 < r) (hμ : 0 ≤ μ) (hg : 0 < g)
    (hK : K = A * (dx - x * dr / r) +
      (2 * dm / r - μ * dr / r) / g * x / r) :
    |K| ≤ A * (|dx| + |x * dr / r|) +
      (2 * |dm| / r + μ * |dr| / r) / g * |x / r| := by
  have hsplit : |2 * dm / r - μ * dr / r| ≤
      2 * |dm| / r + μ * |dr| / r := by
    calc
      |2 * dm / r - μ * dr / r| ≤
          |2 * dm / r| + |μ * dr / r| := abs_sub _ _
      _ = _ := by
        rw [abs_div, abs_div, abs_mul, abs_mul, abs_of_pos hr,
          abs_of_nonneg hμ, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hK]
  calc
    |A * (dx - x * dr / r) +
        (2 * dm / r - μ * dr / r) / g * x / r| ≤
      |A * (dx - x * dr / r)| +
        |(2 * dm / r - μ * dr / r) / g * x / r| := abs_add_le _ _
    _ = A * |dx - x * dr / r| +
        (|2 * dm / r - μ * dr / r| / g) * |x / r| := by
      have halg : (2 * dm / r - μ * dr / r) / g * x / r =
          ((2 * dm / r - μ * dr / r) / g) * (x / r) := by ring
      rw [halg, abs_mul, abs_mul, abs_of_nonneg hA,
        abs_div, abs_of_pos hg]
    _ ≤ A * (|dx| + |x * dr / r|) +
        (2 * |dm| / r + μ * |dr| / r) / g * |x / r| := by
      gcongr
      exact abs_sub _ _

/-- The outgoing logarithmic coefficient difference is bounded pointwise by
the expansion error, the radius error, and the weighted mass error. -/
theorem ComparisonData.nuCoeff_difference_abs_le (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    |IsBVSolution.nuCoeff D.S₁ u v -
      IsBVSolution.nuCoeff D.S₂ u v| ≤
    (IsBVSolution.mu D.S₂ u v /
      ((1 - IsBVSolution.mu D.S₂ u v) * D.S₂.r u v)) *
      (|D.S₁.lam u v - D.S₂.lam u v| +
        |D.S₁.lam u v * (D.S₁.r u v - D.S₂.r u v) /
          D.S₁.r u v|) +
    (2 * |D.S₁.m u v - D.S₂.m u v| / D.S₁.r u v +
        IsBVSolution.mu D.S₂ u v *
          |D.S₁.r u v - D.S₂.r u v| / D.S₁.r u v) /
      ((1 - IsBVSolution.mu D.S₁ u v) *
        (1 - IsBVSolution.mu D.S₂ u v)) *
      |D.S₁.lam u v / D.S₁.r u v| := by
  have hp := D.hT huv
  have hr₁ := D.h₁.solution.radius_pos (u, v) hp.1
  have hr₂ := D.h₂.solution.radius_pos (u, v) hp.2
  have hμ := (D.h₂.mass_ratio_bounds hp.2).1
  change 0 ≤ IsBVSolution.mu D.S₂ u v at hμ
  have hg₁ : 0 < 1 - IsBVSolution.mu D.S₁ u v := by
    have hh := (D.h₁.mass_ratio_bounds hp.1).2
    change IsBVSolution.mu D.S₁ u v < 1 at hh
    linarith
  have hg₂ : 0 < 1 - IsBVSolution.mu D.S₂ u v := by
    have hh := (D.h₂.mass_ratio_bounds hp.2).2
    change IsBVSolution.mu D.S₂ u v < 1 at hh
    linarith
  have hA : 0 ≤ IsBVSolution.mu D.S₂ u v /
      ((1 - IsBVSolution.mu D.S₂ u v) * D.S₂.r u v) :=
    div_nonneg hμ (mul_pos hg₂ hr₂).le
  exact coefficient_difference_abs_le hA hr₁ hμ (mul_pos hg₁ hg₂)
    (D.nuCoeff_difference_mass_radius huv)

/-- The incoming coefficient difference has the same mass and radius split;
the absolute second coefficient is used for its unsigned integral bound. -/
theorem ComparisonData.incomingCoeff_difference_abs_le (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    |IsBVSolution.incomingCoeff D.S₁ u v -
      IsBVSolution.incomingCoeff D.S₂ u v| ≤
    (IsBVSolution.mu D.S₂ u v /
      ((1 - IsBVSolution.mu D.S₂ u v) * D.S₂.r u v)) *
      (|D.S₁.nu u v - D.S₂.nu u v| +
        |D.S₁.nu u v * (D.S₁.r u v - D.S₂.r u v) /
          D.S₁.r u v|) +
    (2 * |D.S₁.m u v - D.S₂.m u v| / D.S₁.r u v +
        IsBVSolution.mu D.S₂ u v *
          |D.S₁.r u v - D.S₂.r u v| / D.S₁.r u v) /
      ((1 - IsBVSolution.mu D.S₁ u v) *
        (1 - IsBVSolution.mu D.S₂ u v)) *
      |D.S₁.nu u v / D.S₁.r u v| := by
  have hp := D.hT huv
  have hr₁ := D.h₁.solution.radius_pos (u, v) hp.1
  have hr₂ := D.h₂.solution.radius_pos (u, v) hp.2
  have hμ := (D.h₂.mass_ratio_bounds hp.2).1
  change 0 ≤ IsBVSolution.mu D.S₂ u v at hμ
  have hg₁ : 0 < 1 - IsBVSolution.mu D.S₁ u v := by
    have hh := (D.h₁.mass_ratio_bounds hp.1).2
    change IsBVSolution.mu D.S₁ u v < 1 at hh
    linarith
  have hg₂ : 0 < 1 - IsBVSolution.mu D.S₂ u v := by
    have hh := (D.h₂.mass_ratio_bounds hp.2).2
    change IsBVSolution.mu D.S₂ u v < 1 at hh
    linarith
  have hA : 0 ≤ IsBVSolution.mu D.S₂ u v /
      ((1 - IsBVSolution.mu D.S₂ u v) * D.S₂.r u v) :=
    div_nonneg hμ (mul_pos hg₂ hr₂).le
  exact coefficient_difference_abs_le hA hr₁ hμ (mul_pos hg₁ hg₂)
    (D.incomingCoeff_difference_mass_radius huv)

end ChristodoulouBV.Uniqueness

end
