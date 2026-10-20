module

public import ChristodoulouBV.Existence.RadiusLimit
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Tactic

/-!
# Scalar limits on the shared existence subsequence

The raw scalar derivatives retain arbitrary point values of the initial
datum. Their variation and amplitude bounds keep the smooth approximants' scalar offset.
Canonical right representatives are constructed separately.
-/

public section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace ChristodoulouBV

/-- The common raw scalar-derivative variation bound, including the
inverse scalar shift. Its coefficients are universal. -/
@[expose] noncomputable def scalarVariationBound (D : ℝ≥0∞) (C : ℝ) : ℝ≥0∞ :=
  s4UniversalC * D + ENNReal.ofReal C * (s4UniversalC * D ^ 2)

/-- The raw variation bound is finite for finite datum variation. -/
theorem scalarVariationBound_ne_top {D : ℝ≥0∞} (hD : D ≠ ∞) (C : ℝ) :
    scalarVariationBound D C ≠ ∞ := by
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top s4UniversalC_ne_top hD,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top s4UniversalC_ne_top (ENNReal.pow_ne_top hD))⟩

/-- Both raw scalar derivatives converge at every point of every section,
including the initial edge. Their BV bounds retain the scalar offset,
and the incoming bound includes its initial endpoint. -/
theorem alpha_beta_limit
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T) :
    (∀ p ∈ globalDomain,
      Tendsto (fun n => (T (d.subsequence n)).alpha p.1 p.2) atTop (𝓝 (d.alpha p.1 p.2)) ∧
      Tendsto (fun n => (T (d.subsequence n)).beta p.1 p.2) atTop (𝓝 (d.beta p.1 p.2))) ∧
    (∀ u, 0 ≤ u → eVariationOn (d.alpha u) (Ioi u) ≤ scalarVariationBound D C) ∧
    (∀ v, 0 < v → eVariationOn (fun u => d.beta u v) (Ico 0 v) ≤ scalarVariationBound D C) ∧
    ∀ p ∈ globalDomain,
      |d.alpha p.1 p.2| ≤ 2 * D.toReal + C / 2 ∧
      |d.beta p.1 p.2| ≤ 4 * D.toReal + 2 * C / 3 := by
  refine ⟨fun p hp => ⟨d.alpha_limit p hp, d.beta_limit p hp⟩, ?_, ?_, ?_⟩
  · intro u hu
    exact variation_bound_of_pointwise_limit
      (fun n => (h (d.subsequence n)).raw_variation_out u hu)
      (fun v hv => d.alpha_limit (u, v) ⟨hu, hv⟩)
  · intro v hv
    exact variation_bound_of_pointwise_limit
      (fun n => (h (d.subsequence n)).variation_beta_initial_edge hv)
      (fun u hu => d.beta_limit (u, v) hu)
  · intro p hp
    exact ⟨le_of_tendsto (d.alpha_limit p hp).abs
        (Eventually.of_forall (fun n => (h (d.subsequence n)).amplitudes.alpha p hp)),
      le_of_tendsto (d.beta_limit p hp).abs
        (Eventually.of_forall (fun n => (h (d.subsequence n)).amplitudes.beta p hp))⟩

/-- The quotient scalar is continuous on the entire off-axis carrier. -/
theorem RadiusLimitData.scalar_continuousOn
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T) :
    ContinuousOn (fun p => d.rawFields.phi p.1 p.2) globalDomain :=
  d.scalarRadius_continuous.continuousOn.div d.radius_continuous.continuousOn
    (fun _ hp => (d.radius_pos h hp).ne')

/-- The scalar converges locally uniformly after division by the positive
radius, on the same subsequence as all seven selected fields. -/
theorem RadiusLimitData.scalar_locally_uniform
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T) :
    TendstoLocallyUniformlyOn
      (fun n (p : ℝ × ℝ) => (T (d.subsequence n)).phi p.1 p.2)
      (fun p => d.rawFields.phi p.1 p.2) atTop globalDomain := by
  have hr0 := fun p hp => (d.radius_pos h (p := p) hp).ne'
  have hi := d.radius_limit.fun_inv₀ d.radius_continuous.continuousOn hr0
  have hm := d.scalarRadius_limit.fun_mul₀ hi d.scalarRadius_continuous.continuousOn
    (d.radius_continuous.continuousOn.inv₀ hr0)
  have hm' : TendstoLocallyUniformlyOn
      (fun n (p : ℝ × ℝ) => (T (d.subsequence n)).r p.1 p.2 *
        (T (d.subsequence n)).phi p.1 p.2 / (T (d.subsequence n)).r p.1 p.2)
      (fun p => d.rawFields.phi p.1 p.2) atTop globalDomain := by
    simpa only [RadiusLimitData.rawFields, div_eq_mul_inv] using hm
  apply hm'.congr
  intro n p hp
  have hr := (h (d.subsequence n)).solution.solution.radius_pos p hp
  exact mul_div_cancel_left₀ _ hr.ne'

/-- The original scalar bound passes to the limit with the smooth approximants' common
offset; no universal bound on the uncentered amplitude is asserted. -/
theorem RadiusLimitData.scalar_amplitude
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T)
    {p : ℝ × ℝ} (hp : p ∈ globalDomain) :
    |d.rawFields.phi p.1 p.2| ≤ 6 * D.toReal + C :=
  le_of_tendsto (d.scalar_locally_uniform h |>.tendsto_at hp).abs
    (Eventually.of_forall (fun n => (h (d.subsequence n)).amplitudes.phi p hp))

/-- Multiplying the quotient scalar by the radius recovers the selected
scalar radius at every domain point. -/
theorem RadiusLimitData.radius_mul_scalar
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (d : RadiusLimitData T)
    {p : ℝ × ℝ} (hp : p ∈ globalDomain) :
    d.radius p * d.rawFields.phi p.1 p.2 = d.scalarRadius p := by
  exact mul_div_cancel₀ _ (d.radius_pos h hp).ne'

/-- Literal initial data survive at every positive point, including all
prescribed jump values. The datum is never replaced by its right trace. -/
theorem data_trace_limit
    {alpha₀ : ℝ → ℝ} {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n))
    (hpoint : ∀ v, 0 < v → Tendsto (fun n => a n v) atTop (𝓝 (alpha₀ v)))
    (d : RadiusLimitData T) :
    ∀ v, 0 < v → d.rawFields.r 0 v = v / 2 ∧ d.rawFields.alpha 0 v = alpha₀ v := by
  intro v hv
  refine ⟨d.initial_radius h hv, tendsto_nhds_unique (d.alpha_limit (0, v) ⟨le_rfl, hv⟩) ?_⟩
  exact ((hpoint v hv).comp d.strictMono.tendsto_atTop).congr'
    (Eventually.of_forall (fun n => ((h (d.subsequence n)).initial_data v hv).2.symm))

end ChristodoulouBV

end
