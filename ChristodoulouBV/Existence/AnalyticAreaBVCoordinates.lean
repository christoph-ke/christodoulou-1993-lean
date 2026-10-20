module

public import ChristodoulouBV.Existence.AnalyticAreaBVCompatibility
public import ChristodoulouBV.Existence.AnalyticAreaBVTransverse
import Mathlib.Tactic

/-!
# Agreement of the physical and unit area charts

Affine substitution in the transverse variable identifies the physical
kernel construction with the unit chart. Together with the signed
inner substitution for the area primitive, this accounts for both missing coordinate factors.
-/

public section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

attribute [local instance] Measure.Subtype.measureSpace

namespace ChristodoulouBV

/-- Reindexing the transverse variable gives exactly the local measure
with the outer factor `a-δ`. This holds for every measurable subset. -/
theorem areaBVPhysicalMeasure_eq_local
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    areaBVPhysicalMeasure h hD d k hδ hδa = areaBVLocalMeasure h hD d k hδ hδa := by
  apply Measure.ext
  intro E hE
  rw [areaBVPhysicalMeasure_apply h hD d k hδ hδa hE,
    areaBVLocalMeasure_apply h hD d k hδ hδa hE]
  let F : ℝ → ℝ≥0∞ := fun z => areaBVPhysicalKernel h hD d k hδ hδa z
    (areaPhysicalPoint k z ⁻¹' (E ∩ areaInteriorCutoff δ a))
  have hz0 (z : ℝ) (hz : z ∉ areaTransverseInterval k a δ) : F z = 0 := by
    dsimp only [F]
    rw [areaBVPhysicalKernel_of_not_mem h hD d k hδ hδa hz]
    rfl
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
  have hy : areaUnitParameter k hδa ⟨z, hz⟩ = y := by
    apply Subtype.ext
    change (z - areaTransverseShift k δ) / (a - δ) = (y : ℝ)
    dsimp only [z]
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hL.ne']
  have hp : (areaPhysicalPoint k z ⁻¹' E) =
      {t | areaBVChartPoint k a δ (y, t) ∈ E} := by
    ext t
    cases hki : k.incoming <;>
      simp only [mem_preimage, areaBVChartPoint, areaTransverseShift, hki,
        Bool.false_eq_true, ite_false, ite_true, zero_add, z, mem_ofPred_eq]
  have hj : areaPhysicalOpenSection k a δ z = areaOpenSection k a δ y := by
    cases hki : k.incoming <;>
      simp only [areaPhysicalOpenSection, areaOpenSection, areaTransverseShift,
        hki, Bool.false_eq_true, ite_false, ite_true, z, zero_add, add_comm δ, add_sub_cancel_right]
  dsimp only [F]
  rw [areaBVPhysicalKernel_of_mem h hD d k hδ hδa hz, hy, preimage_inter,
    area_physical_preimage_interior_of_mem k hz, hp, hj]
  rfl

end ChristodoulouBV

end
