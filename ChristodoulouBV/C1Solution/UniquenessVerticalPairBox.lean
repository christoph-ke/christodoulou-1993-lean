module

public import ChristodoulouBV.C1Solution.UniquenessQuotientKernelJet
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Common vertical-only boxes for canonical C¹ solutions

Compactness supplies one set of radius, outgoing-value, and vertical-jet
bounds for both solutions, with no restriction on triangle width.
-/

public section

namespace ChristodoulouBV.C1Solution

/-- Two arbitrary frozen C¹ solutions have shared positive and finite
constants for all vertical source-factor, quadratic-kernel, and mass-jet inputs on a smaller closed triangle. -/
theorem exists_common_vertical_kernel_box_bounds
    {b₁ b₂ T : ℝ} (hT : 0 < T) (hT₁ : T < b₁) (hT₂ : T < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      (∀ p ∈ closedCoordTriangle 0 T,
        c ≤ S₁.lam p.1 p.2 ∧ S₁.lam p.1 p.2 ≤ C ∧
        c ≤ S₂.lam p.1 p.2 ∧ S₂.lam p.1 p.2 ≤ C ∧
        |S₁.nu p.1 p.2| ≤ C ∧ |S₂.nu p.1 p.2| ≤ C ∧
        |(fderivWithin ℝ (fun q : ℝ × ℝ => S₁.lam q.1 q.2)
          (closedCoordTriangle 0 T) p) (0, 1)| ≤ C ∧
        |(fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2)
          (closedCoordTriangle 0 T) p) (0, 1)| ≤ C ∧
        |(fderivWithin ℝ (outgoingQuotient S₁)
          (closedCoordTriangle 0 T) p) (0, 1)| ≤ C ∧
        |(fderivWithin ℝ (outgoingQuotient S₂)
          (closedCoordTriangle 0 T) p) (0, 1)| ≤ C) ∧
      (∀ p ∈ closedCoordTriangle 0 T,
        c * (p.2 - p.1) ≤ canonicalRadius S₁ p ∧
        c * (p.2 - p.1) ≤ canonicalRadius S₂ p) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ closedCoordTriangle 0 T,
        ε ≤ 1 - canonicalMassRatio b₁ S₁ p ∧
        ε ≤ 1 - canonicalMassRatio b₂ S₂ p := by
  obtain ⟨c, ε, hc, hε, hreg⟩ :=
    exists_common_regular_lower_bounds hT hT₁ hT₂ H₁ H₂
  obtain ⟨C, hC, hbound⟩ :=
    exists_common_outgoing_bound hT hT₁ hT₂ H₁ H₂
  refine ⟨c, C, hc, hC.le, ?_, ?_, ε, hε, ?_⟩
  · intro p hp
    obtain ⟨hlam₁, hlam₂, hnu₁, hnu₂, _, _, hlamv₁, hlamv₂, hhv₁, hhv₂⟩ :=
      hbound p hp
    obtain ⟨hcl₁, hcl₂, _, _, _, _⟩ := hreg p hp
    exact ⟨hcl₁, (le_abs_self _).trans hlam₁,
      hcl₂, (le_abs_self _).trans hlam₂,
      hnu₁, hnu₂, hlamv₁, hlamv₂, hhv₁, hhv₂⟩
  · intro p hp
    obtain ⟨_, _, hr₁, hr₂, _, _⟩ := hreg p hp
    exact ⟨hr₁, hr₂⟩
  · intro p hp
    obtain ⟨_, _, _, _, hgap₁, hgap₂⟩ := hreg p hp
    exact ⟨hgap₁, hgap₂⟩

end ChristodoulouBV.C1Solution

end
