module

public import ChristodoulouBV.Existence.RepresentativesData
public import ChristodoulouBV.Existence.RepresentativesBounds
public import ChristodoulouBV.Existence.RepresentativesVariation

/-!
# Simultaneous representatives for the BV existence witness

Use `d.incomingRightFields` for global BV existence and the quantitative witness. It retains all raw
outgoing datum values while choosing the common canonical right-u ν and β.
`representative_stability` proves all ten frozen primitives and the
geometric clauses. The quantitative bounds and incoming variation decay
refer to this same record. For right-continuous initial data it agrees
on the domain with the canonical record already used in the transport, basic BV, area, and Stieltjes estimates and
satisfies every extra canonical right-continuity clause.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Scalar absolute continuity and uniform scalar variation (frozen
item 3) are unchanged by the simultaneous incoming replacements. -/
theorem incoming_right_fields_item3
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u a b, a ≤ b → outSeg u a b ⊆ globalDomain →
      AbsolutelyContinuousOnInterval (d.incomingRightFields.phi u) a b) ∧
    (∀ v a b, a ≤ b → inSeg v a b ⊆ globalDomain →
      AbsolutelyContinuousOnInterval (fun u => d.incomingRightFields.phi u v) a b) ∧
    ∃ K : ℝ,
      (∀ u, eVariationOn (d.incomingRightFields.phi u)
        {v | (u, v) ∈ globalDomain} ≤ ENNReal.ofReal K) ∧
      ∀ v, eVariationOn (fun u => d.incomingRightFields.phi u v)
        {u | (u, v) ∈ globalDomain} ≤ ENNReal.ofReal K :=
  bv_item3 h hD d

/-- The same global BV witness has right-v λ, α, θ and right-u ν, β, ζ
whenever the prescribed initial datum is right continuous. -/
theorem representatives_right_continuous
    {alpha₀ : ℝ → ℝ} {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (hpoint : ∀ v, 0 < v → Tendsto (fun n => a₀ n v) atTop (𝓝 (alpha₀ v)))
    (hrc : ∀ v, 0 < v → ContinuousWithinAt alpha₀ (Ici v) v)
    (d : RadiusLimitData T) :
    RightBVFields globalDomain d.incomingRightFields ∧
      ∀ p ∈ globalDomain,
        ContinuousWithinAt (d.incomingRightFields.alpha p.1) (Ici p.2) p.2 ∧
        ContinuousWithinAt (fun u => d.incomingRightFields.beta u p.2) (Ici p.1) p.1 := by
  refine ⟨incoming_right_fields_rightBV_of_right_continuous h hD hpoint hrc d, ?_⟩
  intro p hp
  refine ⟨?_, (beta_right_rep h hD d p hp).2⟩
  exact ((right_scalar_derivatives_continuous h hD d p hp).1).congr_of_mem
    (fun v hv => (incoming_right_fields_eq_canonical_of_right_continuous
      h hD hpoint hrc d (p.1, v) ⟨hp.1, hp.2.trans_le hv⟩).1) le_rfl

end ChristodoulouBV

end
