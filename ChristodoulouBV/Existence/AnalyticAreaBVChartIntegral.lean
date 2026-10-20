module

public import ChristodoulouBV.Existence.AnalyticAreaBVCompatibility
public import ChristodoulouBV.Existence.AnalyticAreaBVTransverse
import Mathlib.Tactic

/-!
# Unit-chart integrals on area cutoffs

The inner interval is kept in physical coordinates. The affine
transverse substitution contributes `a-δ`. The identity holds for lower
integrals, so it introduces no extra measurability premise.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

attribute [local instance] Measure.Subtype.measureSpace

namespace ChristodoulouBV

/-- The physical section integral with a cutoff indicator is the unit
chart integral with the outer transverse Jacobian. -/
theorem area_cutoff_chart_lintegral (k : AreaSectionPair) {a δ : ℝ}
    (hδa : δ < a) (E : Set (ℝ × ℝ)) (J : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ z, ∫⁻ t, (E ∩ areaInteriorCutoff δ a).indicator J (areaPhysicalPoint k z t)) =
      ENNReal.ofReal (a - δ) * ∫⁻ y : Ioo (0 : ℝ) 1,
        ∫⁻ t in areaOpenSection k a δ y, E.indicator J (areaBVChartPoint k a δ (y, t)) := by
  let F : ℝ → ℝ≥0∞ := fun z =>
    ∫⁻ t, (E ∩ areaInteriorCutoff δ a).indicator J (areaPhysicalPoint k z t)
  have hz0 (z : ℝ) (hz : z ∉ areaTransverseInterval k a δ) : F z = 0 := by
    have he : (fun t => (E ∩ areaInteriorCutoff δ a).indicator J
        (areaPhysicalPoint k z t)) = fun _ : ℝ => 0 := by
      funext t
      apply indicator_of_notMem
      intro hp
      exact hz ((area_physical_point_mem_interior_iff k δ a z t).mp hp.2).1
    dsimp only [F]
    rw [he, lintegral_zero]
  have hi : (∫⁻ z, F z) = ∫⁻ z in areaTransverseInterval k a δ, F z := by
    rw [← lintegral_indicator
      (show MeasurableSet (areaTransverseInterval k a δ) from measurableSet_Ioo)]
    apply lintegral_congr
    intro z
    by_cases hz : z ∈ areaTransverseInterval k a δ
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz, hz0 z hz]
  change (∫⁻ z, F z) = _
  rw [hi, areaTransverseInterval,
    lintegral_affine_unit (sub_pos.mpr hδa) (areaTransverseShift k δ)]
  apply congrArg (fun v : ℝ≥0∞ => ENNReal.ofReal (a - δ) * v)
  apply lintegral_congr
  intro y
  let z := areaTransverseShift k δ + (a - δ) * (y : ℝ)
  have hL : 0 < a - δ := sub_pos.mpr hδa
  have hz : z ∈ areaTransverseInterval k a δ := by
    change areaTransverseShift k δ < z ∧ z < areaTransverseShift k δ + (a - δ)
    dsimp only [z]
    constructor <;> nlinarith only [hL, y.property.1, y.property.2]
  have hj : areaPhysicalOpenSection k a δ z = areaOpenSection k a δ y := by
    cases hki : k.incoming <;>
      simp only [areaPhysicalOpenSection, areaOpenSection, areaTransverseShift,
        hki, Bool.false_eq_true, ite_false, ite_true, z, zero_add, add_comm δ,
        add_sub_cancel_right]
  have hmeas : MeasurableSet (areaOpenSection k a δ y) := by
    cases hki : k.incoming <;>
      simp only [areaOpenSection, hki, Bool.false_eq_true, ite_false, ite_true] <;>
        exact measurableSet_Ioo
  dsimp only [F]
  rw [← lintegral_indicator hmeas]
  apply lintegral_congr
  intro t
  have hp : areaPhysicalPoint k z t = areaBVChartPoint k a δ (y, t) := by
    cases hki : k.incoming <;>
      simp only [areaBVChartPoint, areaTransverseShift, hki,
        Bool.false_eq_true, ite_false, ite_true, zero_add, z]
  have hc : areaPhysicalPoint k z t ∈ areaInteriorCutoff δ a ↔
      t ∈ areaOpenSection k a δ y := by
    simp only [area_physical_point_mem_interior_iff, hz, true_and, hj]
  by_cases ht : t ∈ areaOpenSection k a δ y
  · have hpt := hc.mpr ht
    rw [indicator_of_mem ht, ← hp]
    by_cases he : areaPhysicalPoint k z t ∈ E
    · rw [indicator_of_mem (show areaPhysicalPoint k z t ∈ E ∩ areaInteriorCutoff δ a
          from ⟨he, hpt⟩), indicator_of_mem he]
    · rw [indicator_of_notMem
          (show areaPhysicalPoint k z t ∉ E ∩ areaInteriorCutoff δ a from fun hh => he hh.1),
        indicator_of_notMem he]
  · have hpt : areaPhysicalPoint k z t ∉ areaInteriorCutoff δ a :=
      fun hh => ht (hc.mp hh)
    rw [indicator_of_notMem ht, indicator_of_notMem
      (show areaPhysicalPoint k z t ∉ E ∩ areaInteriorCutoff δ a from fun hh => hpt hh.2)]

end ChristodoulouBV

end
