module

public import ChristodoulouBV.Existence.BVStieltjes
public import ChristodoulouBV.AreaEstimates.SourceInputsWeak

/-!
# Unconditional BV corner limits

The weak source mass-ratio estimates apply to the shared canonical limit
before its remaining BV axis clauses are assembled. Their constants `15`
and `24`, open scalar-variation intervals, and endpoint integrability
match the corner absorption inputs exactly. This closes (6.9) and (6.12)
at the existing universal threshold `epsilonChosen`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The outgoing logarithmic error is integrable through the axis and
bounded by `54 D` times the outgoing quotient variation. -/
theorem bv_outgoing_g_bound
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u a : ℝ} (hu : 0 ≤ u) (hua : u < a) :
    IntervalIntegrable (bvOutgoingLogCoefficient d.scalarRightFields u) volume u a ∧
      (∫ t in u..a, |bvOutgoingLogCoefficient d.scalarRightFields u t|) ≤
        (54 * D.toReal) * (eVariationOn (fun t => d.scalarRightFields.alpha u t /
          d.scalarRightFields.lam u t) (Ioo u a)).toReal := by
  have hg := bv_outgoing_g_bound_of_mass_ratio_majorant h hD d hu hua
    ⟨SourceInputsWeak.canonical_source_mass_ratio_out_interval_integrable h hD d hu hua,
      SourceInputsWeak.canonical_source_mass_ratio_out_majorant h hD d hu hua⟩
  have hfinite := ((bv_corner_variations_finite h hD d).1 u a hu).1
  have hratio := ENNReal.toReal_mono hfinite (bv_outgoing_ratio_variation h hD d hu hua)
  exact ⟨hg.1, hg.2.trans (mul_le_mul_of_nonneg_left hratio (by positivity))⟩

/-- The corrected incoming logarithmic error is integrable through the axis
and bounded by `63 D` times the incoming quotient variation. -/
theorem bv_incoming_g_bound
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a v : ℝ} (ha : 0 ≤ a) (hav : a < v) :
    IntervalIntegrable (fun t => bvIncomingLogCoefficient d.scalarRightFields t v)
        volume a v ∧
      (∫ t in a..v, |bvIncomingLogCoefficient d.scalarRightFields t v|) ≤
        (63 * D.toReal) * (eVariationOn (fun t => d.scalarRightFields.beta t v /
          d.scalarRightFields.nu t v) (Ioo a v)).toReal := by
  have hg := bv_incoming_g_bound_of_mass_ratio_majorant h hD d ha hav
    ⟨SourceInputsWeak.canonical_source_mass_ratio_in_interval_integrable h hD d ha hav,
      SourceInputsWeak.canonical_source_mass_ratio_in_majorant h hD d ha hav⟩
  have hfinite := ((bv_corner_variations_finite h hD d).2 a v ha hav).1
  have hratio := ENNReal.toReal_mono hfinite (bv_incoming_ratio_variation h hD d ha hav)
  exact ⟨hg.1, hg.2.trans (mul_le_mul_of_nonneg_left hratio (by positivity))⟩

/-- Equation (6.9): for every positive axis point, both outgoing corner
variations tend to zero as `u` approaches that point from below. -/
theorem eq6_9
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (hsmall : D < ENNReal.ofReal epsilonChosen)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun u => eVariationOn (fun t => d.scalarRightFields.alpha u t /
      d.scalarRightFields.lam u t) (Ioo u a)) (𝓝[<] a) (𝓝 0) ∧
    Tendsto (fun u => eVariationOn (fun t => Real.log (d.scalarRightFields.lam u t))
      (Ioo u a)) (𝓝[<] a) (𝓝 0) := by
  apply bv_outgoing_corner_of_mass_ratio_majorant h hD d hsmall _ ha
  intro u b hu hub
  exact ⟨SourceInputsWeak.canonical_source_mass_ratio_out_interval_integrable h hD d hu hub,
    SourceInputsWeak.canonical_source_mass_ratio_out_majorant h hD d hu hub⟩

/-- Equation (6.12): both incoming corner variations tend to zero as `v`
approaches each positive axis point from above. The negative expansion
`-ν` equals `|ν|` on the canonical domain. -/
theorem eq6_12
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (hsmall : D < ENNReal.ofReal epsilonChosen)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun v => eVariationOn (fun t => d.scalarRightFields.beta t v /
      d.scalarRightFields.nu t v) (Ioo a v)) (𝓝[>] a) (𝓝 0) ∧
    Tendsto (fun v => eVariationOn (fun t => Real.log (-d.scalarRightFields.nu t v))
      (Ioo a v)) (𝓝[>] a) (𝓝 0) := by
  apply bv_incoming_corner_of_mass_ratio_majorant h hD d hsmall _ ha
  intro u v hu huv
  exact ⟨SourceInputsWeak.canonical_source_mass_ratio_in_interval_integrable h hD d hu huv,
    SourceInputsWeak.canonical_source_mass_ratio_in_majorant h hD d hu huv⟩

end ChristodoulouBV

end
