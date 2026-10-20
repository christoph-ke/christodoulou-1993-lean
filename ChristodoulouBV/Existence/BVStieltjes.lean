module

public import ChristodoulouBV.Existence.BVStieltjesInitial
public import ChristodoulouBV.Existence.BVStieltjesFixedEdges
public import ChristodoulouBV.Existence.BVStieltjesCorner

/-!
# Canonical BV Stieltjes transport

All four scalar and logarithmic transport inequalities use the actual
analytic carrier. The logarithmic carriers have the complementary section
orientation, retain their transverse endpoints, and use the corrected
incoming sign from the sign correction described in ERRATA.md,
ERR-23. All four corner residuals and all eight fixed-edge tails vanish without a mass-ratio-majorant hypothesis. The two coupled corner
limits have separate internal lemmas with the explicit mass-ratio majorants;
the unconditional source names (6.9) and (6.12) remain reserved.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace ChristodoulouBV

/-- The four BV Stieltjes transport inequalities for the canonical limit.
Every coefficient and carrier is the actual constructed object. -/
theorem bv_stieltjes_transport
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u a : ℝ, 0 < u → u < a →
      eVariationOn (bvOutgoingScalarResidual d.scalarRightFields u a) (Ioo u a) ≤
        eVariationOn (bvOutgoingScalarResidual d.scalarRightFields 0 a) (Ioo u a) +
          bvAnalyticArea h hD d .lamPhi (Ioo 0 u ×ˢ Ioo u a)) ∧
    (∀ u a : ℝ, 0 < u → u < a →
      eVariationOn (bvOutgoingLogResidual d.scalarRightFields u a) (Ioo u a) ≤
        eVariationOn (bvOutgoingLogResidual d.scalarRightFields 0 a) (Ioo u a) +
          bvAnalyticArea h hD d .phiBetaNu (Icc 0 u ×ˢ Ioo u a)) ∧
    (∀ a v b : ℝ, 0 < a → a < v → v < b →
      eVariationOn (bvIncomingScalarResidual d.scalarRightFields v a) (Ioo a v) ≤
        eVariationOn (bvIncomingScalarResidual d.scalarRightFields b a) (Ioo a v) +
          bvAnalyticArea h hD d .nuPhi (Ioo a v ×ˢ Ioo v b)) ∧
    (∀ a v b : ℝ, 0 < a → a < v → v < b →
      eVariationOn (bvIncomingLogResidual d.scalarRightFields v a) (Ioo a v) ≤
        eVariationOn (bvIncomingLogResidual d.scalarRightFields b a) (Ioo a v) +
          bvAnalyticArea h hD d .phiAlphaLam (Ioo a v ×ˢ Icc v b)) :=
  ⟨fun _ _ hu hua => bv_outgoing_scalar_transport h hD d le_rfl hu.le hua,
    fun _ _ hu hua => eq6_8a h hD d hu hua,
    fun _ _ _ ha hav hvb => eq6_10a h hD d ha hav hvb,
    fun _ _ _ ha hav hvb => eq6_11a h hD d ha hav hvb⟩

end ChristodoulouBV

end
