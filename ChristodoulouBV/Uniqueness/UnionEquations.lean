module

public import ChristodoulouBV.Uniqueness.UnionEquationsAxis

/-!
# The selected fields solve the reduced equations on the union

Every closed characteristic primitive, both axis limits, and all pointwise
sign and conformal clauses follow from the source solutions. Mixed terminal
incoming segments use the uniform mass-gap and density bounds proved above.
-/

@[expose] public section

namespace ChristodoulouBV.Uniqueness

/-- The canonical seven-field representative is a solution on the union of
two BV developments with matching initial data. -/
theorem glued_isSolution
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w) :
    IsSolution (U₁ ∪ U₂) (gluedFields U₁ S₁ S₂) := by
  refine {
    development := h₁.solution.development.union h₂.solution.development
    radius_out := ?_
    radius_in := ?_
    scalar_radius_out := ?_
    scalar_radius_in := ?_
    mass_out := ?_
    mass_in := ?_
    lam_in := ?_
    nu_out := ?_
    alpha_in := ?_
    beta_out := ?_
    radius_axis := ?_
    mass_axis := ?_
    radius_pos := ?_
    lam_pos := ?_
    conformal := ?_ }
  · intro u a b hab hseg
    exact (gluedFields_radius_scalar_out h₁ h₂ hdata hab hseg).1
  · intro v a b hab hseg
    exact (gluedFields_radius_scalar_in h₁ h₂ hdata hab hseg).1
  · intro u a b hab hseg
    exact (gluedFields_radius_scalar_out h₁ h₂ hdata hab hseg).2
  · intro v a b hab hseg
    exact (gluedFields_radius_scalar_in h₁ h₂ hdata hab hseg).2
  · intro u a b hab hseg
    exact (gluedFields_mass_nu_beta_out h₁ h₂ hdata hab hseg).1
  · intro v a b hab hseg
    exact gluedFields_mass_in h₁ h₂ hdata hab hseg
  · intro v a b hab hseg
    exact (gluedFields_lam_alpha_in h₁ h₂ hdata hab hseg).1
  · intro u a b hab hseg
    exact (gluedFields_mass_nu_beta_out h₁ h₂ hdata hab hseg).2.1
  · intro v a b hab hseg
    exact (gluedFields_lam_alpha_in h₁ h₂ hdata hab hseg).2
  · intro u a b hab hseg
    exact (gluedFields_mass_nu_beta_out h₁ h₂ hdata hab hseg).2.2
  · intro a _ha
    exact (gluedFields_radius_mass_axis h₁ h₂ hdata a).1
  · intro a _ha
    exact (gluedFields_radius_mass_axis h₁ h₂ hdata a).2
  · intro p hp
    exact (gluedFields_radius_pos_mass_gap_pos h₁ h₂ hdata hp).1
  · intro p hp
    exact gluedFields_lam_pos h₁ h₂ hdata hp
  · intro p hp
    exact gluedFields_conformal h₁ h₂ hdata hp

end ChristodoulouBV.Uniqueness

end
