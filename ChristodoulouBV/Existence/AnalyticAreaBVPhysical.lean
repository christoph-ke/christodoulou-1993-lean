module

public import ChristodoulouBV.Existence.AnalyticAreaBVLocal
public import ChristodoulouBV.Existence.AnalyticAreaBVCutoffs
import Mathlib.Tactic

/-!
# Section kernels indexed by the physical transverse coordinate

This reindexing puts all truncations on the same transverse measure
space. The kernel is zero outside the transverse interval of its chart.
-/

public section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem variation_measure_congr {f g : ℝ → ℝ} (he : f = g)
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ) :
    hf.vectorMeasure.variation = hg.vectorMeasure.variation := by
  subst g
  rfl

/-- The shift of the physical transverse coordinate in the two charts. -/
@[expose] def areaTransverseShift (k : AreaSectionPair) (δ : ℝ) : ℝ :=
  if k.incoming then δ else 0

/-- The physical transverse interval of an open off-axis chart. -/
@[expose] def areaTransverseInterval (k : AreaSectionPair) (a δ : ℝ) : Set ℝ :=
  Ioo (areaTransverseShift k δ) (areaTransverseShift k δ + (a - δ))

/-- Inverse affine transverse parametrization. -/
@[expose] noncomputable def areaUnitParameter (k : AreaSectionPair) {a δ : ℝ}
    (hδa : δ < a) (z : areaTransverseInterval k a δ) : Ioo (0 : ℝ) 1 :=
  ⟨((z : ℝ) - areaTransverseShift k δ) / (a - δ),
    (div_pos (sub_pos.mpr z.property.1) (sub_pos.mpr hδa)),
    (div_lt_one (sub_pos.mpr hδa)).mpr (by linarith only [z.property.2])⟩

/-- The inverse transverse parametrization is measurable. -/
theorem area_unit_parameter_measurable (k : AreaSectionPair) {a δ : ℝ}
    (hδa : δ < a) : Measurable (areaUnitParameter k hδa) := by
  apply Measurable.subtype_mk
  exact (measurable_subtype_coe.sub measurable_const).div_const (a - δ)

/-- The clamped section measure indexed by the physical transverse
coordinate, extended by the zero measure outside the chart. -/
@[expose] noncomputable def areaBVPhysicalKernel
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) : Kernel ℝ ℝ := by
  classical
  refine ⟨fun z => if hz : z ∈ areaTransverseInterval k a δ then
    areaBVSectionKernel h hD d k hδ hδa (areaUnitParameter k hδa ⟨z, hz⟩) else 0, ?_⟩
  exact ((areaBVSectionKernel h hD d k hδ hδa).measurable.comp
    (area_unit_parameter_measurable k hδa)).dite measurable_const measurableSet_Ioo

/-- On its transverse interval the physical kernel is the original
variation-measure kernel at the inverse affine parameter. -/
theorem areaBVPhysicalKernel_of_mem
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ z : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) (hz : z ∈ areaTransverseInterval k a δ) :
    areaBVPhysicalKernel h hD d k hδ hδa z =
      areaBVSectionKernel h hD d k hδ hδa (areaUnitParameter k hδa ⟨z, hz⟩) := by
  classical
  simp only [areaBVPhysicalKernel, Kernel.coe_mk, dite_eq_left hz]

/-- Outside its transverse interval the physical kernel is zero. -/
theorem areaBVPhysicalKernel_of_not_mem
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ z : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) (hz : z ∉ areaTransverseInterval k a δ) :
    areaBVPhysicalKernel h hD d k hδ hδa z = 0 := by
  classical
  simp only [areaBVPhysicalKernel, Kernel.coe_mk, dite_eq_right hz]

/-- Physical reindexing preserves the uniform finite kernel bound. -/
instance areaBVPhysicalKernel_isFiniteKernel
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    IsFiniteKernel (areaBVPhysicalKernel h hD d k hδ hδa) := by
  obtain ⟨V, hV, hb⟩ := (inferInstance :
    IsFiniteKernel (areaBVSectionKernel h hD d k hδ hδa)).exists_univ_le
  refine ⟨V, hV, fun z => ?_⟩
  by_cases hz : z ∈ areaTransverseInterval k a δ
  · rw [areaBVPhysicalKernel_of_mem h hD d k hδ hδa hz]
    exact hb _
  · rw [areaBVPhysicalKernel_of_not_mem h hD d k hδ hδa hz]
    exact bot_le

/-- The same clamped primitive written entirely in physical coordinates. -/
@[expose] noncomputable def areaPhysicalClampedPrimitive (k : AreaSectionPair)
    (S : Fields) (a δ z t : ℝ) : ℝ :=
  if k.incoming then
    areaPhysicalPrimitive k S z 0 (max 0 (min (z - δ) t))
  else
    areaPhysicalPrimitive k S z a (max (z + δ) (min a t))

/-- Reindexing the primitive gives the literal physical-coordinate
clamping formula in each orientation. -/
theorem area_physical_clamped_primitive_eq (k : AreaSectionPair) (S : Fields)
    {a δ : ℝ} (hδa : δ < a) (z : areaTransverseInterval k a δ) :
    areaClampedPrimitive k S a δ (areaUnitParameter k hδa z) =
      areaPhysicalClampedPrimitive k S a δ z := by
  have hL : a - δ ≠ 0 := (sub_pos.mpr hδa).ne'
  funext t
  cases hki : k.incoming with
  | false =>
    simp only [areaClampedPrimitive, areaPhysicalClampedPrimitive, hki,
      Bool.false_eq_true, ite_false, areaUnitParameter, areaTransverseShift,
      sub_zero, mul_div_cancel₀ _ hL, add_comm δ]
  | true =>
    simp only [areaClampedPrimitive, areaPhysicalClampedPrimitive, hki, ite_true,
      areaUnitParameter, areaTransverseShift, mul_div_cancel₀ _ hL,
      add_sub_cancel]

/-- The physical kernel is exactly the variation measure of its physical
clamped primitive. The proof of bounded variation is supplied here. -/
theorem areaBVPhysicalKernel_eq_variation
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ z : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) (hz : z ∈ areaTransverseInterval k a δ) :
    ∃ hb : BoundedVariationOn (areaPhysicalClampedPrimitive k d.rawFields a δ z) univ,
      areaBVPhysicalKernel h hD d k hδ hδa z = hb.vectorMeasure.variation := by
  let y := areaUnitParameter k hδa ⟨z, hz⟩
  have he := area_physical_clamped_primitive_eq k d.rawFields hδa ⟨z, hz⟩
  have hb := area_clamped_primitive_bv h hD d k hδ hδa y
  have hb' : BoundedVariationOn (areaPhysicalClampedPrimitive k d.rawFields a δ z) univ := by
    rwa [he] at hb
  refine ⟨hb', ?_⟩
  rw [areaBVPhysicalKernel_of_mem h hD d k hδ hδa hz, areaBVSectionKernel_apply]
  exact variation_measure_congr he _ hb'

/-- The interior cutoff omits the initial edge, whose smooth analytic
area is zero. No boundary atom is introduced by extending a primitive
across the initial edge. -/
@[expose] def areaInteriorCutoff (δ a : ℝ) : Set (ℝ × ℝ) :=
  areaOpenCutoff δ a ∩ {p | 0 < p.1}

/-- Interior cutoffs are Borel measurable. -/
theorem measurableSet_areaInteriorCutoff (δ a : ℝ) :
    MeasurableSet (areaInteriorCutoff δ a) :=
  (measurableSet_areaOpenCutoff δ a).inter
    (measurableSet_lt measurable_const measurable_fst)

/-- Area measure of a truncation, indexed by physical transverse
coordinates. This form is used to compare overlapping truncations. -/
@[expose] noncomputable def areaBVPhysicalMeasure
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) : Measure (ℝ × ℝ) :=
  (Measure.map (fun p : ℝ × ℝ => areaPhysicalPoint k p.1 p.2)
    ((volume : Measure ℝ) ⊗ₘ areaBVPhysicalKernel h hD d k hδ hδa)).restrict
      (areaInteriorCutoff δ a)

/-- The physical-coordinate section integral for any measurable set. -/
theorem areaBVPhysicalMeasure_apply
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) :
    areaBVPhysicalMeasure h hD d k hδ hδa E =
      ∫⁻ z, areaBVPhysicalKernel h hD d k hδ hδa z
        {t | areaPhysicalPoint k z t ∈ E ∩ areaInteriorCutoff δ a} := by
  rw [areaBVPhysicalMeasure, Measure.restrict_apply hE,
    Measure.map_apply (area_physical_point_continuous k).measurable
      (hE.inter (measurableSet_areaInteriorCutoff δ a)),
    Measure.compProd_apply ((area_physical_point_continuous k).measurable
      (hE.inter (measurableSet_areaInteriorCutoff δ a)))]
  rfl

end ChristodoulouBV

end
