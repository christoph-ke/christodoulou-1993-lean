module

public import ChristodoulouBV.Uniqueness.UniformThresholdQuotientPoints
public import ChristodoulouBV.Uniqueness.QuotientIntegral

/-!
# Package-uniform second solution quotient bounds
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The constant is selected from the numerical package before normalized comparison data. -/
theorem UniformThresholdBounds.quotient_second_uniform_bounds
    (P : UniformThresholdBounds) :
    ∃ Q : ℝ, 1 ≤ Q ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
      ((∀ x y, (x, y) ∈ triangle D.a D.b →
        ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
          (eVariationOn (S.phi x) (Ioc x y)).toReal ≤ P.gapThreshold ∧
          (eVariationOn (fun s => S.phi s y) (Ico x y)).toReal ≤ P.gapThreshold) →
        ∀ u v, (u, v) ∈ triangle D.a D.b →
          |D.S₂.theta u v / D.S₂.lam u v| ≤ Q ∧
          |D.S₂.zeta u v / D.S₂.nu u v| ≤ Q) := by
  obtain ⟨Q, hQ, hcoef⟩ := P.coefficient_bounds_normalized
  refine ⟨Q, by linarith, ?_⟩
  intro D ha hb hP hsmall u v huv
  rcases hcoef D ha hb hP
      (fun x y hxy S hS => (hsmall x y hxy S hS).1)
      u v huv D.S₂ (Or.inr rfl) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hθ, hζ,
      _, _, _, _, _, _, _⟩
  exact ⟨hθ, hζ⟩

end ChristodoulouBV.Uniqueness

end
