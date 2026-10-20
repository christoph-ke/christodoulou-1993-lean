module

public import ChristodoulouBV.Uniqueness.UnionRepresentativesTerminal

/-!
# Incoming representatives on the union

The incoming radius and scalar-radius densities are determined pointwise on
source overlaps. We select their common values on the union.
-/

@[expose] public section

namespace ChristodoulouBV.Uniqueness

/-- Select the incoming radius density from the first source wherever it is
available, and from the second source elsewhere. -/
noncomputable def commonNu (U₁ : Set (ℝ × ℝ)) (S₁ S₂ : Fields) :
    ℝ → ℝ → ℝ := by
  classical
  exact fun u v => if (u, v) ∈ U₁ then S₁.nu u v else S₂.nu u v

/-- Select the incoming scalar-radius density using the same convention. -/
noncomputable def commonBeta (U₁ : Set (ℝ × ℝ)) (S₁ S₂ : Fields) :
    ℝ → ℝ → ℝ := by
  classical
  exact fun u v => if (u, v) ∈ U₁ then S₁.beta u v else S₂.beta u v

/-- The selected incoming densities equal the first source at every point of
its domain. -/
theorem common_nu_beta_eq_first {U₁ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    {u v : ℝ} (hp : (u, v) ∈ U₁) :
    commonNu U₁ S₁ S₂ u v = S₁.nu u v ∧
      commonBeta U₁ S₁ S₂ u v = S₁.beta u v := by
  classical
  simp [commonNu, commonBeta, hp]

/-- The selected incoming densities also equal the second source throughout
its domain, including the overlap. -/
theorem common_nu_beta_eq_second
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {u v : ℝ} (hp : (u, v) ∈ U₂) :
    commonNu U₁ S₁ S₂ u v = S₂.nu u v ∧
      commonBeta U₁ S₁ S₂ u v = S₂.beta u v := by
  classical
  by_cases hmem : (u, v) ∈ U₁
  · have hnu := source_nu_eq_on_overlap h₁ h₂ hdata
      (show (u, v) ∈ U₁ ∩ U₂ from ⟨hmem, hp⟩)
    have hbeta := source_beta_eq_on_overlap h₁ h₂ hdata
      (show (u, v) ∈ U₁ ∩ U₂ from ⟨hmem, hp⟩)
    simpa [commonNu, commonBeta, hmem] using And.intro hnu hbeta
  · simp [commonNu, commonBeta, hmem]

end ChristodoulouBV.Uniqueness

end
