module

public import ChristodoulouBV.Uniqueness.QuotientIntermediate

/-!
# Stable scalar quotient transport

The full comparison triangle supplies the axis datum. Incoming and outgoing
quotient transport, weighted mass estimates, and finite dimensional
absorption give the stable final bounds.
-/

@[expose] public section

open Set MeasureTheory

namespace ChristodoulouBV.Uniqueness

/-- The stable quotient bridge for Christodoulou's estimates (3.20) and
(3.21). The threshold and constant are fixed before the variation size and
compact top. -/
theorem ComparisonData.quotient_norms_absorb
    (D : ComparisonData) (ha : D.a = 0) (hb : D.b = 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
        (∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε) →
        ∀ V, D.a < V → V < D.b →
          D.A V ≤ C * ε * D.B V ∧ D.B V ≤ C * D.A V := by
  exact D.stable_quotient_estimates ha hb

end ChristodoulouBV.Uniqueness

end
