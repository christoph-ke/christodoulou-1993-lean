module

public import ChristodoulouBV.ForMathlib.MeasureTheory.AreaFormula
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Smooth analytic area

The Jacobian density of a smooth planar map defines a countably additive measure.
Its integral agrees with the multiplicity area for `C¹` maps on open domains.
Continuity on decreasing sets requires finite initial area. The nonsmooth
image-area/Stieltjes identity asserted in §4 is a separate assertion not established here.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Function Topology

namespace ChristodoulouBV

/-- The analytic area measure of a smooth planar map, defined by its absolute
Jacobian density. This measure also makes sense for an arbitrary total map;
the `C¹` hypothesis is needed only for the multiplicity formula. -/
noncomputable def smoothAnalyticArea (F : ℝ × ℝ → ℝ × ℝ) :
    MeasureTheory.Measure (ℝ × ℝ) :=
  (volume : MeasureTheory.Measure (ℝ × ℝ)).withDensity
    (fun p => ENNReal.ofReal |(fderiv ℝ F p).det|)

/-- On a measurable set the smooth analytic area is the integral of the
absolute Jacobian. -/
theorem smooth_analytic_area (F : ℝ × ℝ → ℝ × ℝ)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) :
    smoothAnalyticArea F E =
      ∫⁻ p in E, ENNReal.ofReal |(fderiv ℝ F p).det| := by
  exact MeasureTheory.withDensity_apply _ hE

/-- Smooth analytic area agrees with the multiplicity-counting integral on a
measurable subset of an open `C¹` domain. -/
theorem smooth_analytic_area_eq_multiplicity
    (F : ℝ × ℝ → ℝ × ℝ) {U E : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hE : MeasurableSet E) (hEU : E ⊆ U)
    (hF : ContDiffOn ℝ 1 F U) :
    smoothAnalyticArea F E =
      ∫⁻ y, MeasureTheory.fiberMultiplicity F E y
        ∂((volume : Measure ℝ).prod volume) := by
  rw [smooth_analytic_area F hE]
  rw [← Measure.volume_eq_prod ℝ ℝ]
  exact (MeasureTheory.lintegral_fiberMultiplicity_real_prod hU hE hEU hF).symm

/-- The analytic area of a disjoint measurable union is the sum of the areas. -/
theorem smoothAnalyticArea_iUnion (F : ℝ × ℝ → ℝ × ℝ)
    (E : ℕ → Set (ℝ × ℝ)) (hE : ∀ n, MeasurableSet (E n))
    (hd : Pairwise (Disjoint on E)) :
    smoothAnalyticArea F (⋃ n, E n) = ∑' n, smoothAnalyticArea F (E n) := by
  exact MeasureTheory.measure_iUnion hd hE

/-- Continuity from above for smooth analytic area, assuming finite area at
the first set. The printed §4 claim omits this premise: for the identity map,
`Eₙ = {p : ℝ × ℝ | n < p.2}` is decreasing with empty intersection, while
every `Eₙ` has infinite area. The required finiteness is supplied by the endpoint area estimates. -/
theorem analytic_area_continuity (F : ℝ × ℝ → ℝ × ℝ)
    (E : ℕ → Set (ℝ × ℝ)) (hE : ∀ n, MeasurableSet (E n))
    (hmono : Antitone E) (hfinite : smoothAnalyticArea F (E 0) ≠ ∞)
    (hempty : (⋂ n, E n) = ∅) :
    Tendsto (fun n => smoothAnalyticArea F (E n)) atTop (𝓝 0) := by
  have h := MeasureTheory.tendsto_measure_iInter_atTop
    (μ := smoothAnalyticArea F) (fun n => (hE n).nullMeasurableSet) hmono
      ⟨0, hfinite⟩
  simpa only [hempty, measure_empty, Function.comp_def] using h

/-- A domain coordinate change preserves smooth analytic area. Here `e` is a
homeomorphism, and its inverse is `C¹` on the transformed domain, as for a
`C¹` diffeomorphism. The identity is on the smooth analytic carrier. -/
theorem analytic_area_change (F : ℝ × ℝ → ℝ × ℝ)
    (e : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U)
    (he : ContDiffOn ℝ 1 (e.symm : ℝ × ℝ → ℝ × ℝ) (e '' U)) :
    smoothAnalyticArea (F ∘ e.symm) (e '' U) = smoothAnalyticArea F U := by
  have hU' : IsOpen (e '' U) := e.isOpenMap U hU
  have hcomp : ContDiffOn ℝ 1 (F ∘ e.symm) (e '' U) := by
    apply hF.comp he
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    simpa using hy
  have hfiber (y : ℝ × ℝ) :
      MeasureTheory.fiberMultiplicity (F ∘ e.symm) (e '' U) y =
        MeasureTheory.fiberMultiplicity F U y := by
    unfold MeasureTheory.fiberMultiplicity
    have hsets : (e '' U) ∩ (F ∘ e.symm) ⁻¹' {y} =
        e '' (U ∩ F ⁻¹' {y}) := by
      ext x
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hx⟩
        exact ⟨z, ⟨hz, by simpa using hx⟩, rfl⟩
      · rintro ⟨z, ⟨hz, hFz⟩, rfl⟩
        exact ⟨⟨z, hz, rfl⟩, by simpa using hFz⟩
    rw [hsets, e.injective.encard_image]
  calc
    smoothAnalyticArea (F ∘ e.symm) (e '' U) =
        ∫⁻ y, MeasureTheory.fiberMultiplicity (F ∘ e.symm) (e '' U) y
          ∂((volume : Measure ℝ).prod volume) :=
      smooth_analytic_area_eq_multiplicity (F ∘ e.symm)
        hU' hU'.measurableSet Subset.rfl hcomp
    _ = ∫⁻ y, MeasureTheory.fiberMultiplicity F U y
          ∂((volume : Measure ℝ).prod volume) := by
      congr 1
      funext y
      exact hfiber y
    _ = smoothAnalyticArea F U :=
      (smooth_analytic_area_eq_multiplicity F hU hU.measurableSet Subset.rfl hF).symm

end ChristodoulouBV

end
