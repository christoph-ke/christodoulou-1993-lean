module

public import ChristodoulouBV.Existence.AreaLimitBoundsTails
import Mathlib.Tactic

/-!
# The four area inequalities and their explicit finiteness proofs

The numbered (6.4) inequalities use the pointwise integration-by-parts
functional. Its domination of the countably additive carrier is used only
on open cutoffs. Closed-cutoff carrier bounds use the corrected enlargement
of both cutoffs. The two exhaustions and finite-measure tail continuity are
exported by the imported modules.

Every quantitative coefficient is the same universal `s4UniversalC` as in
the smooth estimates. The scalar offset never enters these area bounds.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Separate quantitative finiteness for the pointwise functional and
the closed-cutoff carrier. Lemma 6.2 supplies no finiteness conclusion. -/
theorem area_cutoff_finite_bounds
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    areaPointwiseFunctional k d.rawFields a δ ≤ areaPairBound D k ∧
      areaPointwiseFunctional k d.rawFields a δ ≠ ∞ ∧
      bvAnalyticArea h hD d k (areaClosedCutoff δ a) ≤ areaPairBound D k ∧
      bvAnalyticArea h hD d k (areaClosedCutoff δ a) ≠ ∞ := by
  have hp := area_pointwise_functional_bound h d k hδ hδa
  have hc := bv_analytic_area_closed_bound h hD d k hδ hδa
  have hf := area_pair_bound_ne_top hD k
  exact ⟨hp, ne_top_of_le_ne_top hf hp, hc, ne_top_of_le_ne_top hf hc⟩

/-- The pointwise analytic/Stieltjes counterpart of (6.4a), with both
coordinate factors and the original shared subsequence. -/
theorem eq6_4a
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n))
    (d : RadiusLimitData T) {a δ : ℝ} (hδ : 0 < δ) (hδa : δ < a) :
    areaPointwiseFunctional .phiAlphaLam d.rawFields a δ ≤
      liminf (fun n => smoothAnalyticArea (sourcePhiAlphaLamMap (T (d.subsequence n)))
        (areaClosedCutoff δ a)) atTop := by
  simpa only [area_pair_map_phi_alpha_lam] using
    area_pointwise_functional_le_liminf_closed h d .phiAlphaLam hδ hδa

/-- Explicit C·D² bounds and finiteness for (6.4a), for both the
pointwise functional and the closed-cutoff carrier, uniformly in `a,δ`. -/
theorem eq6_4a_finite
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a δ : ℝ} (hδ : 0 < δ) (hδa : δ < a) :
    areaPointwiseFunctional .phiAlphaLam d.rawFields a δ ≤ s4UniversalC * D ^ 2 ∧
      areaPointwiseFunctional .phiAlphaLam d.rawFields a δ ≠ ∞ ∧
      bvAnalyticArea h hD d .phiAlphaLam (areaClosedCutoff δ a) ≤ s4UniversalC * D ^ 2 ∧
      bvAnalyticArea h hD d .phiAlphaLam (areaClosedCutoff δ a) ≠ ∞ :=
  area_cutoff_finite_bounds h hD d .phiAlphaLam hδ hδa

/-- The pointwise analytic/Stieltjes counterpart of (6.4b), with both
coordinate factors and the original shared subsequence. -/
theorem eq6_4b
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n))
    (d : RadiusLimitData T) {a δ : ℝ} (hδ : 0 < δ) (hδa : δ < a) :
    areaPointwiseFunctional .lamPhi d.rawFields a δ ≤
      liminf (fun n => smoothAnalyticArea (sourceLamPhiMap (T (d.subsequence n)))
        (areaClosedCutoff δ a)) atTop := by
  simpa only [area_pair_map_lam_phi] using
    area_pointwise_functional_le_liminf_closed h d .lamPhi hδ hδa

/-- Explicit C·D³ bounds and finiteness for (6.4b), for both the
pointwise functional and the closed-cutoff carrier, uniformly in `a,δ`. -/
theorem eq6_4b_finite
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a δ : ℝ} (hδ : 0 < δ) (hδa : δ < a) :
    areaPointwiseFunctional .lamPhi d.rawFields a δ ≤ s4UniversalC * D ^ 3 ∧
      areaPointwiseFunctional .lamPhi d.rawFields a δ ≠ ∞ ∧
      bvAnalyticArea h hD d .lamPhi (areaClosedCutoff δ a) ≤ s4UniversalC * D ^ 3 ∧
      bvAnalyticArea h hD d .lamPhi (areaClosedCutoff δ a) ≠ ∞ :=
  area_cutoff_finite_bounds h hD d .lamPhi hδ hδa

/-- The pointwise analytic/Stieltjes counterpart of (6.4c), with both
coordinate factors and the original shared subsequence. -/
theorem eq6_4c
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n))
    (d : RadiusLimitData T) {a δ : ℝ} (hδ : 0 < δ) (hδa : δ < a) :
    areaPointwiseFunctional .phiBetaNu d.rawFields a δ ≤
      liminf (fun n => smoothAnalyticArea (sourcePhiBetaNuMap (T (d.subsequence n)))
        (areaClosedCutoff δ a)) atTop := by
  simpa only [area_pair_map_phi_beta_nu] using
    area_pointwise_functional_le_liminf_closed h d .phiBetaNu hδ hδa

/-- Explicit C·D² bounds and finiteness for (6.4c), for both the
pointwise functional and the closed-cutoff carrier, uniformly in `a,δ`. -/
theorem eq6_4c_finite
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a δ : ℝ} (hδ : 0 < δ) (hδa : δ < a) :
    areaPointwiseFunctional .phiBetaNu d.rawFields a δ ≤ s4UniversalC * D ^ 2 ∧
      areaPointwiseFunctional .phiBetaNu d.rawFields a δ ≠ ∞ ∧
      bvAnalyticArea h hD d .phiBetaNu (areaClosedCutoff δ a) ≤ s4UniversalC * D ^ 2 ∧
      bvAnalyticArea h hD d .phiBetaNu (areaClosedCutoff δ a) ≠ ∞ :=
  area_cutoff_finite_bounds h hD d .phiBetaNu hδ hδa

/-- The pointwise analytic/Stieltjes counterpart of (6.4d), with both
coordinate factors and the original shared subsequence. -/
theorem eq6_4d
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n))
    (d : RadiusLimitData T) {a δ : ℝ} (hδ : 0 < δ) (hδa : δ < a) :
    areaPointwiseFunctional .nuPhi d.rawFields a δ ≤
      liminf (fun n => smoothAnalyticArea (sourceNuPhiMap (T (d.subsequence n)))
        (areaClosedCutoff δ a)) atTop := by
  simpa only [area_pair_map_nu_phi] using
    area_pointwise_functional_le_liminf_closed h d .nuPhi hδ hδa

/-- Explicit C·D³ bounds and finiteness for (6.4d), for both the
pointwise functional and the closed-cutoff carrier, uniformly in `a,δ`. -/
theorem eq6_4d_finite
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a δ : ℝ} (hδ : 0 < δ) (hδa : δ < a) :
    areaPointwiseFunctional .nuPhi d.rawFields a δ ≤ s4UniversalC * D ^ 3 ∧
      areaPointwiseFunctional .nuPhi d.rawFields a δ ≠ ∞ ∧
      bvAnalyticArea h hD d .nuPhi (areaClosedCutoff δ a) ≤ s4UniversalC * D ^ 3 ∧
      bvAnalyticArea h hD d .nuPhi (areaClosedCutoff δ a) ≠ ∞ :=
  area_cutoff_finite_bounds h hD d .nuPhi hδ hδa

/-- The four global analytic-carrier bounds (6.6), with one universal
constant. Both cutoff exhaustions are proved in the imported API. -/
theorem eq6_6
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    bvAnalyticArea h hD d .phiAlphaLam globalDomain ≤ s4UniversalC * D ^ 2 ∧
      bvAnalyticArea h hD d .lamPhi globalDomain ≤ s4UniversalC * D ^ 3 ∧
      bvAnalyticArea h hD d .phiBetaNu globalDomain ≤ s4UniversalC * D ^ 2 ∧
      bvAnalyticArea h hD d .nuPhi globalDomain ≤ s4UniversalC * D ^ 3 :=
  ⟨bv_analytic_area_global_bound h hD d .phiAlphaLam,
    bv_analytic_area_global_bound h hD d .lamPhi,
    bv_analytic_area_global_bound h hD d .phiBetaNu,
    bv_analytic_area_global_bound h hD d .nuPhi⟩

/-- Explicit finiteness of all four global carriers in (6.6). -/
theorem eq6_6_finite
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    bvAnalyticArea h hD d .phiAlphaLam globalDomain ≠ ∞ ∧
      bvAnalyticArea h hD d .lamPhi globalDomain ≠ ∞ ∧
      bvAnalyticArea h hD d .phiBetaNu globalDomain ≠ ∞ ∧
      bvAnalyticArea h hD d .nuPhi globalDomain ≠ ∞ :=
  ⟨bv_analytic_area_global_finite h hD d .phiAlphaLam,
    bv_analytic_area_global_finite h hD d .lamPhi,
    bv_analytic_area_global_finite h hD d .phiBetaNu,
    bv_analytic_area_global_finite h hD d .nuPhi⟩

end ChristodoulouBV

end
