module

public import ChristodoulouBV.Frozen.IsBVSolution
public import ChristodoulouBV.Uniqueness.TargetContinuation

/-!
# Theorem 3.1: uniqueness

The proof is `ChristodoulouBV.Uniqueness.global_propagation`.
The domains and fields are implicit, and the three hypotheses are
auto-parameters, matching the frozen uniqueness statement
`ChristodoulouBV.theorem3_1_unique`.
-/

public section

namespace ChristodoulouBV.Provider

/-- Theorem 3.1 (uniqueness half), in the form of the frozen uniqueness statement. -/
theorem theorem3_1_unique
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁ := by assumption)
    (h₂ : IsBVSolution U₂ S₂ := by assumption)
    (hdata : ∀ v, (0, v) ∈ U₁ ∩ U₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v := by assumption) :
    ∀ p ∈ U₁ ∩ U₂,
      S₁.r p.1 p.2 = S₂.r p.1 p.2 ∧
      S₁.phi p.1 p.2 = S₂.phi p.1 p.2 ∧
      S₁.m p.1 p.2 = S₂.m p.1 p.2 :=
  Uniqueness.global_propagation U₁ U₂ S₁ S₂ h₁ h₂ hdata

end ChristodoulouBV.Provider

end
