module

public import ChristodoulouBV.Uniqueness.UnionBV

/-!
# Provider for the extension half of Theorem 3.1

The witness is the canonical seven-field gluing. Its restriction to either
source agrees pointwise in the three primary fields.
-/

public section

namespace ChristodoulouBV.Provider

/-- Theorem 3.1 (extension half), with the exact frozen existential and
three-field restriction statement. The data are implicit and the three
hypotheses are auto-parameters, so the frozen anchor is sealed by `by exact`. -/
theorem theorem3_1_extend
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁ := by assumption) (h₂ : IsBVSolution U₂ S₂ := by assumption)
    (hdata : ∀ v, (0, v) ∈ U₁ ∩ U₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v := by assumption) :
    ∃ S : Fields, IsBVSolution (U₁ ∪ U₂) S ∧
      (∀ p ∈ U₁, S.r p.1 p.2 = S₁.r p.1 p.2 ∧
        S.phi p.1 p.2 = S₁.phi p.1 p.2 ∧
        S.m p.1 p.2 = S₁.m p.1 p.2) ∧
      (∀ p ∈ U₂, S.r p.1 p.2 = S₂.r p.1 p.2 ∧
        S.phi p.1 p.2 = S₂.phi p.1 p.2 ∧
        S.m p.1 p.2 = S₂.m p.1 p.2) := by
  refine ⟨Uniqueness.gluedFields U₁ S₁ S₂,
    Uniqueness.glued_isBVSolution h₁ h₂ hdata, ?_, ?_⟩
  · intro p hp
    obtain ⟨hr, hphi, hm, _, _⟩ :=
      Uniqueness.gluedFields_eq_first (S₂ := S₂) hp
    exact ⟨hr, hphi, hm⟩
  · intro p hp
    obtain ⟨hr, hphi, hm, _, _⟩ :=
      Uniqueness.gluedFields_eq_second h₁ h₂ hdata hp
    exact ⟨hr, hphi, hm⟩

end ChristodoulouBV.Provider

end
