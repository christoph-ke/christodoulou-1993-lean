module

public import ChristodoulouBV.C1Solution.UniquenessReciprocalDifferences
import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBoxFactors
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# The regular product in the mixed coefficient

The value comparison of `W = λν` uses only the outgoing `λ` difference and
the incoming `ν` difference.
-/

public section

namespace ChristodoulouBV.C1Solution

/-- On a common closed triangle, both regular products are bounded and
their value difference is controlled by `D(u) + N(u)`. -/
theorem canonical_lam_nu_product_value_bounds
    {b₁ b₂ T C V : ℝ}
    (hT : 0 < T) (hT₁ : T < b₁) (hT₂ : T < b₂)
    (hC : 0 ≤ C) (hV : 0 ≤ V)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hlam₁ : ∀ p ∈ closedCoordTriangle 0 T,
      |S₁.lam p.1 p.2| ≤ C)
    (hlam₂ : ∀ p ∈ closedCoordTriangle 0 T,
      |S₂.lam p.1 p.2| ≤ C)
    (hnu₁ : ∀ p ∈ closedCoordTriangle 0 T,
      |S₁.nu p.1 p.2| ≤ V)
    (hnu₂ : ∀ p ∈ closedCoordTriangle 0 T,
      |S₂.nu p.1 p.2| ≤ V)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ T) :
    |S₁.lam u v * S₁.nu u v| ≤ C * V ∧
    |S₂.lam u v * S₂.nu u v| ≤ C * V ∧
    |S₁.lam u v * S₁.nu u v -
      S₂.lam u v * S₂.nu u v| ≤
        (V + C) *
          (outgoingDifference T hT.le S₁ S₂ u +
            incomingDifference T hT.le S₁ S₂ u) := by
  have hp : (u, v) ∈ closedCoordTriangle 0 T := ⟨hu, huv, hv⟩
  let D := outgoingDifference T hT.le S₁ S₂ u
  let N := incomingDifference T hT.le S₁ S₂ u
  have hlamdiff := (outgoing_components_le_difference
    hT hT₁ hT₂ H₁ H₂ hu huv hv).1
  have hnudiff := incoming_component_le_difference
    hT hT₁ hT₂ H₁ H₂ hu huv hv
  have hD : 0 ≤ D := outgoing_difference_nonneg hT hT₁ hT₂ H₁ H₂
    ⟨hu, huv.trans hv⟩
  have hN : 0 ≤ N := (abs_nonneg _).trans hnudiff
  have hW₁ : |S₁.lam u v * S₁.nu u v| ≤ C * V := by
    rw [abs_mul]
    exact mul_le_mul (hlam₁ (u, v) hp) (hnu₁ (u, v) hp)
      (abs_nonneg _) hC
  have hW₂ : |S₂.lam u v * S₂.nu u v| ≤ C * V := by
    rw [abs_mul]
    exact mul_le_mul (hlam₂ (u, v) hp) (hnu₂ (u, v) hp)
      (abs_nonneg _) hC
  have hdiff := intervalIntegral.abs_mul_sub_mul_le_of_bounds
    hC hD (hlam₂ (u, v) hp) (hnu₁ (u, v) hp) hlamdiff hnudiff
  refine ⟨hW₁, hW₂, ?_⟩
  calc
    _ ≤ D * V + C * N := hdiff
    _ ≤ (V + C) * (D + N) := by nlinarith only [hC, hV, hD, hN]

end ChristodoulouBV.C1Solution

end
