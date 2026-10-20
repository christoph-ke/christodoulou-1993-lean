module

public import ChristodoulouBV.Existence.AnalyticAreaBVCompatibility
public import ChristodoulouBV.Existence.AnalyticAreaBVSmoothDensity
public import ChristodoulouBV.AreaEstimates.AnalyticArea
import Mathlib.Tactic

/-!
# Smooth Jacobian area in physical section coordinates

Tonelli's theorem is applied to the actual measurable cutoff indicator.
Both null orientations use physical transverse Lebesgue measure.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Tonelli in the physical section coordinates, in either null orientation. -/
theorem lintegral_area_physical_point (k : AreaSectionPair) (F : ℝ × ℝ → ℝ≥0∞)
    (hF : AEMeasurable F volume) :
    (∫⁻ p, F p) = ∫⁻ z, ∫⁻ t, F (areaPhysicalPoint k z t) := by
  rw [Measure.volume_eq_prod ℝ ℝ] at hF ⊢
  cases hki : k.incoming with
  | false =>
    simpa only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false] using lintegral_prod F hF
  | true =>
    simpa only [areaPhysicalPoint, hki, ite_true] using lintegral_prod_symm F hF

/-- Smooth analytic area on an interior cutoff is the transverse
integral of its absolute Jacobian density with the cutoff indicator. -/
theorem SmoothSolutionBounds.analytic_area_physical_formula
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) :
    smoothAnalyticArea (areaPairMap k S) (E ∩ areaInteriorCutoff δ a) =
      ∫⁻ z, ∫⁻ t, (E ∩ areaInteriorCutoff δ a).indicator
        (fun p => ENNReal.ofReal |(fderiv ℝ (areaPairMap k S) p).det|)
          (areaPhysicalPoint k z t) := by
  have hI := measurableSet_areaInteriorCutoff δ a
  have hsub : E ∩ areaInteriorCutoff δ a ⊆ areaSmoothDomain := by
    intro p hp
    exact ⟨hp.2.2, (areaOpenCutoff_subset_globalDomain hδ hp.2.1).2⟩
  have hC : ContDiffOn ℝ 1 (areaPairMap k S) areaSmoothDomain :=
    (h.area_pair_map_contDiffOn k).mono (fun p hp => ⟨hp.1.le, hp.2⟩)
  have hJ := jacobianDensity_aemeasurable_of_contDiffOn isOpen_areaSmoothDomain hC
  have hJ' := hJ.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hIndicator := (aemeasurable_indicator_iff (hE.inter hI)).mpr hJ'
  rw [smooth_analytic_area _ (hE.inter hI), ← lintegral_indicator (hE.inter hI)]
  exact lintegral_area_physical_point k _ hIndicator

end ChristodoulouBV

end
