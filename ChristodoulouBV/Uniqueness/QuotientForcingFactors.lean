module

public import ChristodoulouBV.Uniqueness.QuotientMassWeights

/-!
# Factored scalar quotient forcing

The four source terms also factor through the signed mixed coefficient. This
form is used for integration against the integrated coefficient bounds.
-/

@[expose] public section

namespace ChristodoulouBV.Uniqueness

private theorem quotient_forcing_factor
    {k₁ k₂ x₁ x₂ y₁ y₂ : ℝ} (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) :
    -(k₁ * x₁) * y₁ / x₁ ^ 2 +
      (k₂ * x₂) * y₂ / x₂ ^ 2 =
      -k₁ * (y₁ / x₁ - y₂ / x₂) -
        (k₁ - k₂) * (y₂ / x₂) := by
  field_simp [hx₁, hx₂]
  ring

/-- Incoming quotient forcing factors into a self-coefficient times the
quotient difference and a coefficient difference times the second quotient. -/
theorem ComparisonData.alpha_ratio_forcing_factor (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    alphaRatioForcing D u v =
      -IsBVSolution.incomingCoeff D.S₁ u v *
        (D.S₁.theta u v / D.S₁.lam u v -
          D.S₂.theta u v / D.S₂.lam u v) -
        (IsBVSolution.incomingCoeff D.S₁ u v -
          IsBVSolution.incomingCoeff D.S₂ u v) *
          (D.S₂.theta u v / D.S₂.lam u v) := by
  have hp := D.hT huv
  have hl₁ := (D.h₁.solution.lam_pos (u, v) hp.1).ne'
  have hl₂ := (D.h₂.solution.lam_pos (u, v) hp.2).ne'
  have hrc₁ : IsBVSolution.radiusCoeff D.S₁ u v =
      IsBVSolution.incomingCoeff D.S₁ u v * D.S₁.lam u v := by
    unfold IsBVSolution.radiusCoeff IsBVSolution.incomingCoeff
    ring
  have hrc₂ : IsBVSolution.radiusCoeff D.S₂ u v =
      IsBVSolution.incomingCoeff D.S₂ u v * D.S₂.lam u v := by
    unfold IsBVSolution.radiusCoeff IsBVSolution.incomingCoeff
    ring
  rw [← D.alpha_ratio_forcing_algebra huv, hrc₁, hrc₂]
  exact quotient_forcing_factor hl₁ hl₂

/-- Outgoing quotient forcing has the analogous factorization through the
nonnegative outgoing expansion coefficient. -/
theorem ComparisonData.beta_ratio_forcing_factor (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    betaRatioForcing D u v =
      -IsBVSolution.nuCoeff D.S₁ u v *
        (D.S₁.zeta u v / D.S₁.nu u v -
          D.S₂.zeta u v / D.S₂.nu u v) -
        (IsBVSolution.nuCoeff D.S₁ u v -
          IsBVSolution.nuCoeff D.S₂ u v) *
          (D.S₂.zeta u v / D.S₂.nu u v) := by
  have hp := D.hT huv
  obtain ⟨c₁, hc₁, hlam₁⟩ := D.h₁.lam_bounded_below
  obtain ⟨c₂, hc₂, hlam₂⟩ := D.h₂.lam_bounded_below
  have hn₁ : D.S₁.nu u v ≠ 0 :=
    ne_of_lt ((D.h₁.nu_le_neg_lower hc₁ hlam₁ hp.1).trans_lt
      (neg_lt_zero.mpr hc₁))
  have hn₂ : D.S₂.nu u v ≠ 0 :=
    ne_of_lt ((D.h₂.nu_le_neg_lower hc₂ hlam₂ hp.2).trans_lt
      (neg_lt_zero.mpr hc₂))
  have hrc₁ := D.h₁.radius_coeff_eq_nu_coeff_mul_nu
    D.h₁.solution.development hp.1
  have hrc₂ := D.h₂.radius_coeff_eq_nu_coeff_mul_nu
    D.h₂.solution.development hp.2
  rw [← D.beta_ratio_forcing_algebra huv, hrc₁, hrc₂]
  exact quotient_forcing_factor hn₁ hn₂

end ChristodoulouBV.Uniqueness

end
