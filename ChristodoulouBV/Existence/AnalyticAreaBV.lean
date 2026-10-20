module

public import ChristodoulouBV.Existence.AnalyticAreaBVGlobal
public import ChristodoulouBV.Existence.AnalyticAreaBVCoordinates
public import ChristodoulouBV.Existence.AnalyticAreaBVSectionKernel
public import ChristodoulouBV.Existence.AnalyticAreaBVSmoothFunctional
public import ChristodoulouBV.Existence.AnalyticAreaBVChartCover
import Mathlib.Tactic

/-!
# Analytic area of the shared BV limit

The carrier is a transverse integral of section variation measures.
It is countably additive and obeys finite-measure continuity. On open
cutoffs it is bounded by the pointwise area-section functional, with the signed
inner coordinate weights and the outer factor `a-δ` retained.
The carrier agrees with smooth analytic area on the bounded C¹ fields
used in the approximation, and the smooth pointwise functional has an
exact absolute-Jacobian integral formula.

Closed-cutoff bounds use a larger open cutoff. The general nonsmooth
multiplicity image-area identity is not asserted here.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Function

attribute [local instance] Measure.Subtype.measureSpace

namespace ChristodoulouBV

/-- The corrected coordinate-weight bound for each of the four ordered
area pairs. The affine area primitive contains both signed inner density
factors; the transverse substitution supplies the outer `a-δ` factor. -/
theorem area_coordinate_weights
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    bvAnalyticArea h hD d k (areaOpenCutoff δ a) ≤
      ENNReal.ofReal (a - δ) * ∫⁻ y : Ioo (0 : ℝ) 1,
        areaSectionChartVariation k d.rawFields a δ y := by
  rw [bv_analytic_area h hD d k hδ hδa,
    areaBVPhysicalMeasure_eq_local h hD d k hδ hδa]
  simpa only [area_section_chart_variation_eq k d.rawFields hδ hδa] using
    areaBVLocalMeasure_univ_le h hD d k hδ hδa

/-- The analytic carrier is finite on every open off-axis cutoff.
This local finiteness is independent of the global small-data estimate. -/
theorem bv_analytic_area_open_finite
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    bvAnalyticArea h hD d k (areaOpenCutoff δ a) ≠ ∞ := by
  rw [bv_analytic_area h hD d k hδ hδa,
    areaBVPhysicalMeasure_eq_local h hD d k hδ hδa]
  exact measure_ne_top _ _

/-- Closed-cutoff estimates follow from monotonicity and a larger open
cutoff. The gap is halved to include the old gap boundary. -/
theorem bv_analytic_area_closed_le_open_enlarged
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ} (hδ : 0 < δ) :
    bvAnalyticArea h hD d k (areaClosedCutoff δ a) ≤
      bvAnalyticArea h hD d k (areaOpenCutoff (δ / 2) (a + 1)) :=
  measure_mono (areaClosedCutoff_subset_open_enlarged hδ)

/-- Countable additivity of the constructed analytic area carrier. -/
theorem bv_analytic_area_iUnion
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) (E : ℕ → Set (ℝ × ℝ))
    (hE : ∀ n, MeasurableSet (E n)) (hd : Pairwise (Disjoint on E)) :
    bvAnalyticArea h hD d k (⋃ n, E n) = ∑' n, bvAnalyticArea h hD d k (E n) :=
  measure_iUnion hd hE

/-- Finite-measure continuity on shrinking measurable domains. The
initial finiteness premise is essential, as recorded in ERR-03. -/
theorem bv_analytic_area_continuity
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) (E : ℕ → Set (ℝ × ℝ))
    (hE : ∀ n, MeasurableSet (E n)) (hm : Antitone E)
    (hfinite : bvAnalyticArea h hD d k (E 0) ≠ ∞) (he : (⋂ n, E n) = ∅) :
    Tendsto (fun n => bvAnalyticArea h hD d k (E n)) atTop (𝓝 0) := by
  have ht := tendsto_measure_iInter_atTop (μ := bvAnalyticArea h hD d k)
    (fun n => (hE n).nullMeasurableSet) hm ⟨0, hfinite⟩
  simpa only [he, measure_empty, Function.comp_def] using ht

end ChristodoulouBV

end
