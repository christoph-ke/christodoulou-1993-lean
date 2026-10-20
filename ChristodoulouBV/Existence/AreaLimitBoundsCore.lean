module

public import ChristodoulouBV.Existence.AnalyticAreaBV
public import ChristodoulouBV.Existence.AreaSectionLimit
import Mathlib.Tactic

/-!
# Weighted lower semicontinuity and uniform area bounds

All limits use the shared subsequence of `RadiusLimitData`. The pointwise
functional retains the prescribed Helly values. The measure carrier is
dominated by that functional on open cutoffs, as required by the author
ruling on the corrected variation-measure area carrier; see ERRATA.md.
Finiteness comes from the smooth area estimates, independently of the
lower-integral reading of Lemma 6.2.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

attribute [local instance] Measure.Subtype.measureSpace

namespace ChristodoulouBV

/-- The corrected two-dimensional pointwise Stieltjes functional,
including the outer transverse Jacobian. -/
@[expose] noncomputable def areaPointwiseFunctional (k : AreaSectionPair)
    (S : Fields) (a δ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (a - δ) * ∫⁻ y : Ioo (0 : ℝ) 1,
    areaSectionChartVariation k S a δ y

/-- The universal D-only bound for each pair, in printed pair order. -/
@[expose] noncomputable def areaPairBound (D : ℝ≥0∞) : AreaSectionPair → ℝ≥0∞
  | .phiAlphaLam | .phiBetaNu => s4UniversalC * D ^ 2
  | .lamPhi | .nuPhi => s4UniversalC * D ^ 3

/-- Each of the four universal bounds is finite at finite datum variation. -/
theorem area_pair_bound_ne_top {D : ℝ≥0∞} (hD : D ≠ ∞) (k : AreaSectionPair) :
    areaPairBound D k ≠ ∞ := by
  cases k <;> exact ENNReal.mul_ne_top s4UniversalC_ne_top (ENNReal.pow_ne_top hD)

/-- The four smooth global area estimates in the common ordered-pair API. -/
theorem SmoothSolutionBounds.area_pair_global_bound
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) (k : AreaSectionPair) :
    smoothAnalyticArea (areaPairMap k S) globalDomain ≤ areaPairBound D k := by
  cases k with
  | phiAlphaLam =>
    rw [area_pair_map_phi_alpha_lam]
    exact h.areas_global.1
  | lamPhi =>
    rw [area_pair_map_lam_phi]
    exact h.areas_global.2.2.1
  | phiBetaNu =>
    rw [area_pair_map_phi_beta_nu]
    exact h.areas_global.2.1
  | nuPhi =>
    rw [area_pair_map_nu_phi]
    exact h.areas_global.2.2.2

/-- Concrete measurable sections, finite section BV budgets and the
positive radius floor needed for all four weak area substitutions.
The signed coordinate factors are in `areaSectionChartVariation`. -/
theorem area_premises
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    Measurable (areaSectionChartVariation k d.rawFields a δ) ∧
      (∀ n, Measurable (areaSectionChartVariation k (T n) a δ)) ∧
      (∃ V : ℝ≥0∞, V ≠ ∞ ∧
        (∀ n y, areaSectionChartVariation k (T n) a δ y ≤ V) ∧
        ∀ y, areaSectionChartVariation k d.rawFields a δ y ≤ V) ∧
      (∀ p ∈ areaClosedCutoff δ a,
        δ / 3 ≤ d.rawFields.r p.1 p.2 ∧ 0 < d.rawFields.r p.1 p.2 ∧
        d.rawFields.lam p.1 p.2 ≠ 0 ∧ d.rawFields.nu p.1 p.2 ≠ 0 ∧
        Tendsto (fun n => areaSectionCoefficients (T (d.subsequence n)) p)
          atTop (𝓝 (areaSectionCoefficients d.rawFields p))) ∧
      (∀ u A B, A ≤ B → outSeg u A B ⊆ globalDomain →
        AbsolutelyContinuousOnInterval
          (fun v => d.rawFields.zeta u v / d.rawFields.r u v) A B ∧
        ∀ᵐ v ∂volume, v ∈ Icc A B →
          deriv (fun t => d.rawFields.zeta u t / d.rawFields.r u t) v =
            areaSectionP (areaSectionCoefficients d.rawFields (u, v))) ∧
      ∀ v A B, A ≤ B → inSeg v A B ⊆ globalDomain →
        AbsolutelyContinuousOnInterval
          (fun u => d.rawFields.theta u v / d.rawFields.r u v) A B ∧
        ∀ᵐ u ∂volume, u ∈ Icc A B →
          deriv (fun t => d.rawFields.theta t v / d.rawFields.r t v) u =
            areaSectionP (areaSectionCoefficients d.rawFields (u, v)) := by
  refine ⟨common_chart_section_measurability h hD d k hδ hδa,
    fun n => smooth_chart_section_measurability (h n) k hδ hδa, ?_, ?_,
    fun _ _ _ hab hs => raw_outgoing_mixed_scalar_density h hD d hab hs,
    fun _ _ _ hab hs => raw_incoming_mixed_scalar_density h hD d hab hs⟩
  · simpa only [area_section_chart_variation_eq k _ hδ hδa] using
      uniform_area_section_variation_bound_with_limit h hD d k hδ hδa
  · intro p hp
    have hg := (expansions_limit h d).2.2 p hp.1
    refine ⟨(s6_truncation h d k hδ hδa).1 p hp, d.radius_pos h hp.1,
      ?_, ?_, d.area_section_coefficients_limit h hp.1⟩
    · change d.lam p.1 p.2 ≠ 0
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) hg.1)
    · change d.nu p.1 p.2 ≠ 0
      linarith only [hg.2.2.1]

/-- Weak lower semicontinuity of each corrected weighted section.
This holds at every transverse parameter; only AC/a.e. derivative
identities of the actual fields are used in the area-section construction. -/
theorem area_lsc_weak
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n))
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) (y : Ioo (0 : ℝ) 1) :
    ENNReal.ofReal (a - δ) * areaSectionChartVariation k d.rawFields a δ y ≤
      liminf (fun n => ENNReal.ofReal (a - δ) *
        areaSectionChartVariation k (T (d.subsequence n)) a δ y) atTop := by
  calc
    _ ≤ ENNReal.ofReal (a - δ) *
        liminf (fun n => areaSectionChartVariation k (T (d.subsequence n)) a δ y)
          atTop := mul_le_mul' le_rfl (lemma61_applicability_chart h d k hδ hδa y)
    _ ≤ _ := by
      simpa only [liminf_const, Pi.mul_def] using
        (ENNReal.le_liminf_mul (f := atTop)
          (u := fun _ : ℕ => ENNReal.ofReal (a - δ))
          (v := fun n => areaSectionChartVariation k (T (d.subsequence n)) a δ y))

/-- Integrated weak lower semicontinuity, with the outer Jacobian retained. -/
theorem area_pointwise_functional_le_liminf
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n))
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    areaPointwiseFunctional k d.rawFields a δ ≤
      liminf (fun n => smoothAnalyticArea (areaPairMap k (T (d.subsequence n)))
        (areaOpenCutoff δ a)) atTop := by
  have hm := mul_le_mul' (le_refl (ENNReal.ofReal (a - δ)))
    (area_chart_section_lintegral_le_liminf h d k hδ hδa)
  have hi := ENNReal.le_liminf_mul (f := atTop)
    (u := fun _ : ℕ => ENNReal.ofReal (a - δ))
    (v := fun n => ∫⁻ y : Ioo (0 : ℝ) 1,
      areaSectionChartVariation k (T (d.subsequence n)) a δ y)
  simp only [liminf_const, Pi.mul_def,
    smooth_area_coordinate_formula (h _) k hδ hδa] at hi
  exact hm.trans hi

/-- The numbered pointwise inequality on the source's closed truncation.
The smooth open-cutoff area is bounded by its closed-cutoff area. -/
theorem area_pointwise_functional_le_liminf_closed
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n))
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    areaPointwiseFunctional k d.rawFields a δ ≤
      liminf (fun n => smoothAnalyticArea (areaPairMap k (T (d.subsequence n)))
        (areaClosedCutoff δ a)) atTop := by
  have hsub : areaOpenCutoff δ a ⊆ areaClosedCutoff δ a := fun _ hp =>
    ⟨areaOpenCutoff_subset_globalDomain hδ hp, hp.2.1.le, hp.2.2.le⟩
  exact (area_pointwise_functional_le_liminf h d k hδ hδa).trans
    (liminf_le_liminf (Eventually.of_forall fun _ => measure_mono hsub))

/-- The carrier on an open cutoff is bounded by the smooth liminf.
No domination on the corresponding closed cutoff is asserted. -/
theorem bv_analytic_area_open_le_liminf
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    bvAnalyticArea h hD d k (areaOpenCutoff δ a) ≤
      liminf (fun n => smoothAnalyticArea (areaPairMap k (T (d.subsequence n)))
        (areaOpenCutoff δ a)) atTop :=
  (area_coordinate_weights h hD d k hδ hδa).trans
    (area_pointwise_functional_le_liminf h d k hδ hδa)

/-- The smooth liminf has a universal bound independent of both cutoffs. -/
theorem smooth_area_liminf_le_pair_bound
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n))
    (d : RadiusLimitData T) (k : AreaSectionPair) {E : Set (ℝ × ℝ)}
    (hE : E ⊆ globalDomain) :
    liminf (fun n => smoothAnalyticArea (areaPairMap k (T (d.subsequence n))) E)
      atTop ≤ areaPairBound D k := by
  have hb := liminf_le_liminf (f := atTop) (Eventually.of_forall fun n =>
    (measure_mono hE).trans ((h (d.subsequence n)).area_pair_global_bound k))
  simpa only [liminf_const] using hb

/-- The pointwise functional has the universal D-only bound on every
truncation. In particular its finite integral is proved separately. -/
theorem area_pointwise_functional_bound
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n))
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    areaPointwiseFunctional k d.rawFields a δ ≤ areaPairBound D k :=
  (area_pointwise_functional_le_liminf h d k hδ hδa).trans
    (smooth_area_liminf_le_pair_bound h d k (areaOpenCutoff_subset_globalDomain hδ))

/-- The open-cutoff carrier has the universal bound uniform in `a,δ`. -/
theorem bv_analytic_area_open_bound
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    bvAnalyticArea h hD d k (areaOpenCutoff δ a) ≤ areaPairBound D k :=
  (area_coordinate_weights h hD d k hδ hδa).trans
    (area_pointwise_functional_bound h d k hδ hδa)

/-- Closed-cutoff bounds use the corrected enlargement in both parameters. -/
theorem bv_analytic_area_closed_bound
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    bvAnalyticArea h hD d k (areaClosedCutoff δ a) ≤ areaPairBound D k :=
  (bv_analytic_area_closed_le_open_enlarged h hD d k hδ).trans
    (bv_analytic_area_open_bound h hD d k (by linarith only [hδ])
      (by linarith only [hδ, hδa]))

end ChristodoulouBV

end
