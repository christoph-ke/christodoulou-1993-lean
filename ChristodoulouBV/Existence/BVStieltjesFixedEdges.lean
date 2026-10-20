module

public import ChristodoulouBV.Existence.BVStieltjesLogShrink
import Mathlib.Tactic

/-!
# All fixed-edge scalar and logarithmic residual tails

The two open tails of each of the four characteristic residuals vanish.
The fixed edges may be initial, terminal, or shifted off the initial edge.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The eight fixed-edge shrinking statements used in the BV corner
and shifted-triangle transports. All are pointwise canonical variations. -/
theorem s6_boundary_residual_shrink
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u a b : ℝ, 0 ≤ u → u < a → a < b →
      (Tendsto (fun x => eVariationOn (bvOutgoingScalarResidual d.scalarRightFields u b)
          (Ioo x b)) (𝓝[<] b) (𝓝 0) ∧
        Tendsto (fun x => eVariationOn (bvOutgoingScalarResidual d.scalarRightFields u b)
          (Ioo a x)) (𝓝[>] a) (𝓝 0)) ∧
      (Tendsto (fun x => eVariationOn (bvOutgoingLogResidual d.scalarRightFields u b)
          (Ioo x b)) (𝓝[<] b) (𝓝 0) ∧
        Tendsto (fun x => eVariationOn (bvOutgoingLogResidual d.scalarRightFields u b)
          (Ioo a x)) (𝓝[>] a) (𝓝 0))) ∧
    (∀ v a b : ℝ, 0 ≤ a → a < b → b < v →
      (Tendsto (fun x => eVariationOn (bvIncomingScalarResidual d.scalarRightFields v a)
          (Ioo x b)) (𝓝[<] b) (𝓝 0) ∧
        Tendsto (fun x => eVariationOn (bvIncomingScalarResidual d.scalarRightFields v a)
          (Ioo a x)) (𝓝[>] a) (𝓝 0)) ∧
      (Tendsto (fun x => eVariationOn (bvIncomingLogResidual d.scalarRightFields v a)
          (Ioo x b)) (𝓝[<] b) (𝓝 0) ∧
        Tendsto (fun x => eVariationOn (bvIncomingLogResidual d.scalarRightFields v a)
          (Ioo a x)) (𝓝[>] a) (𝓝 0))) := by
  constructor
  · intro u a b hu hua hab
    exact ⟨bv_fixed_edge_variation_shrink hab
        ((bv_outgoing_scalar_residual_bv h hD d hu hua hab.le).mono Ioo_subset_Icc_self),
      bv_fixed_edge_variation_shrink hab
        ((bv_outgoing_log_residual_bv h hD d hu hua hab.le).mono Ioo_subset_Icc_self)⟩
  · intro v a b ha hab hbv
    exact ⟨bv_fixed_edge_variation_shrink hab
        ((bv_incoming_scalar_residual_bv h hD d ha hab.le hbv).mono Ioo_subset_Icc_self),
      bv_fixed_edge_variation_shrink hab
        ((bv_incoming_log_residual_bv h hD d ha hab.le hbv).mono Ioo_subset_Icc_self)⟩

end ChristodoulouBV

end
