module

public import ChristodoulouBV.Uniqueness.ExpansionTransport

/-!
# Algebra for differences of expansion coefficients

The mass-ratio difference is split into its weighted mass and radius parts
before it is inserted into the characteristic coefficient identities.
-/

@[expose] public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The absolute mass-ratio difference splits into a mass difference and a
radius difference, with the second solution's nonnegative mass ratio. -/
theorem ComparisonData.mu_diff_abs_le (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    |IsBVSolution.mu D.S₁ u v - IsBVSolution.mu D.S₂ u v| ≤
      2 * |D.S₁.m u v - D.S₂.m u v| / D.S₁.r u v +
      IsBVSolution.mu D.S₂ u v *
        |D.S₁.r u v - D.S₂.r u v| / D.S₁.r u v := by
  have hp := D.hT huv
  have hr := D.h₁.solution.radius_pos (u, v) hp.1
  have hmu := (D.h₂.mass_ratio_bounds hp.2).1
  change 0 ≤ IsBVSolution.mu D.S₂ u v at hmu
  rw [D.mu_diff_identity huv]
  calc
    |2 * (D.S₁.m u v - D.S₂.m u v) / D.S₁.r u v -
        IsBVSolution.mu D.S₂ u v *
          (D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v| ≤
        |2 * (D.S₁.m u v - D.S₂.m u v) / D.S₁.r u v| +
        |IsBVSolution.mu D.S₂ u v *
          (D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v| := abs_sub _ _
    _ = _ := by
      rw [abs_div, abs_div, abs_mul, abs_mul, abs_of_pos hr,
        abs_of_nonneg hmu, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

/-- The outgoing expansion difference at a good point is bounded by its
finite good-ray norm. -/
theorem ComparisonData.lam_diff_le_L_good (D : ComparisonData)
    {V u v : ℝ} (hV : V ≤ D.b)
    (huv : (u, v) ∈ triangle D.a V) (hvG : v ∈ D.goodV) :
    |D.S₁.lam u v - D.S₂.lam u v| ≤ D.L V := by
  obtain ⟨K₁, hK₁, _⟩ := D.h₁.exists_uniform_radius_upper
  obtain ⟨K₂, hK₂, _⟩ := D.h₂.exists_uniform_radius_upper
  let M := max (K₁ + K₂) 0
  have hM : 0 ≤ M := le_max_right _ _
  have hbound : ∀ x y, (x, y) ∈ triangle D.a V →
      y ∈ D.goodV → |D.S₁.lam x y - D.S₂.lam x y| ≤ M := by
    intro x y hxy _
    have hp := D.hT ((mem_triangle).2
      ⟨hxy.1, hxy.2.1, hxy.2.2.trans_le hV⟩)
    have hpos₁ := D.h₁.solution.lam_pos (x, y) hp.1
    have hpos₂ := D.h₂.solution.lam_pos (x, y) hp.2
    have hsum : |D.S₁.lam x y - D.S₂.lam x y| ≤ K₁ + K₂ := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [hK₁ (x, y) hp.1, hK₂ (x, y) hp.2]
    exact hsum.trans (le_max_left _ _)
  exact D.le_goodVNorm hM hbound huv hvG

/-- The incoming expansion difference at a good point is bounded by its
finite good-ray norm. -/
theorem ComparisonData.nu_diff_le_N_good (D : ComparisonData)
    {V u v : ℝ} (hV : V ≤ D.b)
    (huv : (u, v) ∈ triangle D.a V) (hvG : v ∈ D.goodV) :
    |D.S₁.nu u v - D.S₂.nu u v| ≤ D.N V := by
  obtain ⟨K₁, hK₁⟩ := D.h₁.nu_bounded_below
  obtain ⟨K₂, hK₂⟩ := D.h₂.nu_bounded_below
  obtain ⟨c₁, hc₁, hlam₁⟩ := D.h₁.lam_bounded_below
  obtain ⟨c₂, hc₂, hlam₂⟩ := D.h₂.lam_bounded_below
  let M := max (K₁ + K₂) 0
  have hM : 0 ≤ M := le_max_right _ _
  have hbound : ∀ x y, (x, y) ∈ triangle D.a V →
      y ∈ D.goodV → |D.S₁.nu x y - D.S₂.nu x y| ≤ M := by
    intro x y hxy _
    have hp := D.hT ((mem_triangle).2
      ⟨hxy.1, hxy.2.1, hxy.2.2.trans_le hV⟩)
    have hn₁ := D.h₁.nu_le_neg_lower hc₁ hlam₁ hp.1
    have hn₂ := D.h₂.nu_le_neg_lower hc₂ hlam₂ hp.2
    have hsum : |D.S₁.nu x y - D.S₂.nu x y| ≤ K₁ + K₂ := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [hK₁ (x, y) hp.1, hK₂ (x, y) hp.2]
    exact hsum.trans (le_max_left _ _)
  exact D.le_goodVNorm hM hbound huv hvG

/-- The outgoing coefficient difference with the mass-ratio difference
expanded into its mass and radius contributions. -/
theorem ComparisonData.nuCoeff_difference_mass_radius (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    IsBVSolution.nuCoeff D.S₁ u v -
      IsBVSolution.nuCoeff D.S₂ u v =
    (IsBVSolution.mu D.S₂ u v /
      ((1 - IsBVSolution.mu D.S₂ u v) * D.S₂.r u v)) *
        ((D.S₁.lam u v - D.S₂.lam u v) -
          D.S₁.lam u v * (D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v) +
    (2 * (D.S₁.m u v - D.S₂.m u v) / D.S₁.r u v -
        IsBVSolution.mu D.S₂ u v *
          (D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v) /
      ((1 - IsBVSolution.mu D.S₁ u v) *
        (1 - IsBVSolution.mu D.S₂ u v)) *
      D.S₁.lam u v / D.S₁.r u v := by
  rw [D.nuCoeff_difference_identity huv, D.mu_diff_identity huv]

/-- The incoming coefficient difference with the same exact mass and radius
split. Its second solution coefficient has the sign used by (3.12). -/
theorem ComparisonData.incomingCoeff_difference_mass_radius (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    IsBVSolution.incomingCoeff D.S₁ u v -
      IsBVSolution.incomingCoeff D.S₂ u v =
    (IsBVSolution.mu D.S₂ u v /
      ((1 - IsBVSolution.mu D.S₂ u v) * D.S₂.r u v)) *
        ((D.S₁.nu u v - D.S₂.nu u v) -
          D.S₁.nu u v * (D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v) +
    (2 * (D.S₁.m u v - D.S₂.m u v) / D.S₁.r u v -
        IsBVSolution.mu D.S₂ u v *
          (D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v) /
      ((1 - IsBVSolution.mu D.S₁ u v) *
        (1 - IsBVSolution.mu D.S₂ u v)) *
      D.S₁.nu u v / D.S₁.r u v := by
  rw [D.incomingCoeff_difference_identity huv, D.mu_diff_identity huv]

end ChristodoulouBV.Uniqueness

end
