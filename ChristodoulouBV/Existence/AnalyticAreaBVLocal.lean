module

public import ChristodoulouBV.Existence.AnalyticAreaBVKernel
public import ChristodoulouBV.Existence.AreaSectionLimit
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic

/-!
# The variation-measure kernels on each area chart

The clamped section primitives of the area-section construction have finite
variation on the whole real line. Their variation measures form finite
kernels. Restricting to the open physical section removes cutoff atoms;
this restriction is essential to the variation-measure domination statement.
-/

public section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

attribute [local instance] Measure.Subtype.measureSpace

namespace ChristodoulouBV

private instance areaBVUnitFiniteVolume :
    IsFiniteMeasure (volume : Measure (Ioo (0 : ℝ) 1)) where
  measure_univ_lt_top := by
    rw [Measure.Subtype.volume_univ nullMeasurableSet_Ioo]
    norm_num

/-- Constant extension of the physical primitive has no more variation
than the source's full closed-section pointwise functional. -/
theorem area_clamped_primitive_variation_le (k : AreaSectionPair) (S : Fields)
    {a δ : ℝ} (_hδ : 0 < δ) (hδa : δ < a) (y : Ioo (0 : ℝ) 1) :
    eVariationOn (areaClampedPrimitive k S a δ y) univ ≤
      areaSectionVariation k S a δ y := by
  let w := (a - δ) * (y : ℝ)
  have hw : 0 < w := mul_pos (sub_pos.mpr hδa) y.property.1
  have hwa : δ + w < a := by
    have hy := y.property.2
    have haδ : 0 < a - δ := sub_pos.mpr hδa
    dsimp only [w]
    nlinarith only [haδ, hy]
  have hb (F : ℝ → ℝ) {l r : ℝ} (hlr : l ≤ r) :
      eVariationOn (fun t => F (max l (min r t))) univ ≤
        eVariationOn F (Icc l r) :=
    eVariationOn.comp_le_of_monotoneOn F (fun t => max l (min r t))
      (fun _ _ _ _ hxy => max_le_max_left _ (min_le_min_left _ hxy))
      (fun _ _ => ⟨le_max_left _ _, max_le hlr (min_le_left _ _)⟩)
  change eVariationOn (fun t => areaClampedPrimitive k S a δ y t) univ ≤ _
  cases hki : k.incoming with
  | false =>
    simp only [areaClampedPrimitive, areaSectionVariation, hki,
      Bool.false_eq_true, ite_false]
    exact hb (areaPhysicalPrimitive k S w a) hwa.le
  | true =>
    simp only [areaClampedPrimitive, areaSectionVariation, hki, ite_true]
    exact hb (areaPhysicalPrimitive k S (δ + w) 0) hw.le

/-- Every clamped primitive of the actual shared BV limit has finite
whole-line variation. This uses the independently proved local area-section bound. -/
theorem area_clamped_primitive_bv
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) (y : Ioo (0 : ℝ) 1) :
    BoundedVariationOn (areaClampedPrimitive k d.rawFields a δ y) univ := by
  obtain ⟨V, hV, _, hb⟩ := uniform_area_section_variation_bound_with_limit h hD d k hδ hδa
  exact ne_top_of_le_ne_top hV
    ((area_clamped_primitive_variation_le k d.rawFields hδ hδa y).trans (hb y))

/-- Each evaluation of a clamped physical primitive is measurable in
the transverse unit parameter, including its prescribed raw values. -/
theorem area_clamped_primitive_measurable
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) (t : ℝ) :
    Measurable fun y => areaClampedPrimitive k d.rawFields a δ y t := by
  obtain ⟨E, hE, hc⟩ := area_clamped_common_exceptional_set h hD d k hδ hδa
  apply measurable_of_countable_not_continuousAt
  exact hE.mono fun y hy => by
    by_contra hye
    exact hy (hc y hye t)

/-- The actual variation-measure kernel of the clamped physical BV
primitive. Its use on an open section is independent of cutoff atoms. -/
@[expose] noncomputable def areaBVSectionKernel
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) : Kernel (Ioo (0 : ℝ) 1) ℝ where
  toFun y := (area_clamped_primitive_bv h hD d k hδ hδa y).vectorMeasure.variation
  measurable' := measurable_variation_kernel
    (area_clamped_primitive_measurable h hD d k hδ hδa)
    (area_clamped_primitive_bv h hD d k hδ hδa)

/-- Evaluation of the section kernel is the variation of Mathlib's
Stieltjes vector measure, rather than pointwise closed-interval variation. -/
theorem areaBVSectionKernel_apply
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) (y : Ioo (0 : ℝ) 1) :
    areaBVSectionKernel h hD d k hδ hδa y =
      (area_clamped_primitive_bv h hD d k hδ hδa y).vectorMeasure.variation := rfl

/-- On a fixed off-axis chart the whole section measures have one
finite mass bound, uniform in the transverse parameter. -/
instance areaBVSectionKernel_isFiniteKernel
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    IsFiniteKernel (areaBVSectionKernel h hD d k hδ hδa) := by
  obtain ⟨V, hV, _, hb⟩ := uniform_area_section_variation_bound_with_limit h hD d k hδ hδa
  refine ⟨V, lt_top_iff_ne_top.mpr hV, fun y => ?_⟩
  exact ((area_clamped_primitive_bv h hD d k hδ hδa y).variation_vectorMeasure_univ_le.trans
    (area_clamped_primitive_variation_le k d.rawFields hδ hδa y)).trans (hb y)

/-- The open physical interval in either triangular chart. -/
@[expose] def areaOpenSection (k : AreaSectionPair) (a δ : ℝ)
    (y : Ioo (0 : ℝ) 1) : Set ℝ :=
  if k.incoming then Ioo 0 ((a - δ) * (y : ℝ))
  else Ioo (δ + (a - δ) * (y : ℝ)) a

/-- Measure-theoretic variation on the open physical section is bounded
by the closed-section pointwise variation. No closed-cutoff analogue
of this assertion is used. -/
theorem areaBVSectionKernel_open_le
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) (y : Ioo (0 : ℝ) 1) :
    areaBVSectionKernel h hD d k hδ hδa y (areaOpenSection k a δ y) ≤
      areaSectionVariation k d.rawFields a δ y := by
  have hb := area_clamped_primitive_bv h hD d k hδ hδa y
  rw [areaBVSectionKernel_apply]
  have hbound := area_clamped_primitive_variation_le k d.rawFields hδ hδa y
  exact (measure_mono (subset_univ _)).trans
    (hb.variation_vectorMeasure_univ_le.trans hbound)

/-- Physical coordinates from a transverse unit parameter and a physical
section coordinate. The transverse derivative is exactly `a-δ`. -/
@[expose] def areaBVChartPoint (k : AreaSectionPair) (a δ : ℝ)
    (p : Ioo (0 : ℝ) 1 × ℝ) : ℝ × ℝ :=
  areaPhysicalPoint k
    (if k.incoming then δ + (a - δ) * (p.1 : ℝ) else (a - δ) * (p.1 : ℝ)) p.2

/-- The physical chart map is continuous. -/
theorem area_bv_chart_point_continuous (k : AreaSectionPair) (a δ : ℝ) :
    Continuous (areaBVChartPoint k a δ) := by
  change Continuous fun p => areaBVChartPoint k a δ p
  cases k <;> simp only [areaBVChartPoint, areaPhysicalPoint, AreaSectionPair.incoming,
    Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

/-- The open section region in the product chart. -/
@[expose] def areaBVChartInterior (k : AreaSectionPair) (a δ : ℝ) :
    Set (Ioo (0 : ℝ) 1 × ℝ) :=
  {p | p.2 ∈ areaOpenSection k a δ p.1}

/-- The open product-chart region is Borel measurable. -/
theorem measurableSet_areaBVChartInterior (k : AreaSectionPair) (a δ : ℝ) :
    MeasurableSet (areaBVChartInterior k a δ) := by
  cases hki : k.incoming with
  | false =>
    simp only [areaBVChartInterior, areaOpenSection, hki, Bool.false_eq_true, ite_false]
    change MeasurableSet {p : Ioo (0 : ℝ) 1 × ℝ |
      δ + (a - δ) * (p.1 : ℝ) < p.2 ∧ p.2 < a}
    exact (measurableSet_lt (by fun_prop) measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const)
  | true =>
    simp only [areaBVChartInterior, areaOpenSection, hki, ite_true]
    change MeasurableSet {p : Ioo (0 : ℝ) 1 × ℝ |
      0 < p.2 ∧ p.2 < (a - δ) * (p.1 : ℝ)}
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (by fun_prop))

/-- The countably additive area measure on one open truncation. The
factor `a-δ` is the outer coordinate Jacobian; the section kernel uses
physical coordinates and therefore already contains the inner factor. -/
@[expose] noncomputable def areaBVLocalMeasure
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) : Measure (ℝ × ℝ) :=
  ENNReal.ofReal (a - δ) • Measure.map (areaBVChartPoint k a δ)
    (((volume : Measure (Ioo (0 : ℝ) 1)) ⊗ₘ
      areaBVSectionKernel h hD d k hδ hδa).restrict (areaBVChartInterior k a δ))

/-- Transverse integration formula for the actual local area measure,
with the corrected outer coordinate factor. -/
theorem areaBVLocalMeasure_apply
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) :
    areaBVLocalMeasure h hD d k hδ hδa E = ENNReal.ofReal (a - δ) *
      ∫⁻ y : Ioo (0 : ℝ) 1, areaBVSectionKernel h hD d k hδ hδa y
        {t | areaBVChartPoint k a δ (y, t) ∈ E ∧ t ∈ areaOpenSection k a δ y} := by
  rw [areaBVLocalMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (area_bv_chart_point_continuous k a δ).measurable hE,
    Measure.restrict_apply ((area_bv_chart_point_continuous k a δ).measurable hE),
    Measure.compProd_apply
      (((area_bv_chart_point_continuous k a δ).measurable hE).inter
        (measurableSet_areaBVChartInterior k a δ))]
  rfl

/-- The local measure is bounded by the source pointwise functional,
including the outer transverse Jacobian. -/
theorem areaBVLocalMeasure_univ_le
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    areaBVLocalMeasure h hD d k hδ hδa univ ≤ ENNReal.ofReal (a - δ) *
      ∫⁻ y : Ioo (0 : ℝ) 1, areaSectionVariation k d.rawFields a δ y := by
  rw [areaBVLocalMeasure_apply h hD d k hδ hδa MeasurableSet.univ]
  apply mul_le_mul_of_nonneg_left _ bot_le
  apply lintegral_mono
  intro y
  simp only [mem_univ, true_and]
  exact areaBVSectionKernel_open_le h hD d k hδ hδa y

/-- Finite datum variation makes each local area measure finite before
any universal smooth-area estimate is used. -/
instance areaBVLocalMeasure_isFiniteMeasure
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    IsFiniteMeasure (areaBVLocalMeasure h hD d k hδ hδa) :=
  ⟨lt_of_le_of_lt (areaBVLocalMeasure_univ_le h hD d k hδ hδa)
    (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (area_section_integrals_finite h hD d k hδ hδa).2))⟩

end ChristodoulouBV

end
