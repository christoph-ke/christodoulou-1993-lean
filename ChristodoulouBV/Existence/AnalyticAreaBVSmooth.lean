module

public import ChristodoulouBV.Existence.AnalyticAreaBVGlobal
public import ChristodoulouBV.Existence.AnalyticAreaBVSectionGeometry
public import ChristodoulouBV.Existence.AnalyticAreaBVSmoothSection
public import ChristodoulouBV.Existence.AnalyticAreaBVSmoothFubini
import Mathlib.Tactic

/-!
# Agreement with smooth analytic area

For the smooth approximating C¹ fields, the variation-measure carrier is precisely
the smooth absolute-Jacobian measure on the global development. This
does not identify any nonsmooth carrier with multiplicity image area.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- At a smooth field, the actual BV section kernel has the absolute
smooth Jacobian density on its open physical section. -/
theorem areaBVPhysicalKernel_restrict_eq_smooth
    {a₀ : ℕ → ℝ → ℝ} {D D₁ : ℝ≥0∞} {C C₁ : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a₁ : ℝ → ℝ}
    (hS : SmoothSolutionBounds a₁ D₁ C₁ d.rawFields) (k : AreaSectionPair)
    {a δ z : ℝ} (hδ : 0 < δ) (hδa : δ < a)
    (hz : z ∈ areaTransverseInterval k a δ) :
    (areaBVPhysicalKernel h hD d k hδ hδa z).restrict (areaPhysicalOpenSection k a δ z) =
      ((volume : Measure ℝ).withDensity
        (fun t => ENNReal.ofReal
          |(fderiv ℝ (areaPairMap k d.rawFields) (areaPhysicalPoint k z t)).det|)).restrict
            (areaPhysicalOpenSection k a δ z) := by
  obtain ⟨hF, heF⟩ := areaBVPhysicalKernel_eq_variation h hD d k hδ hδa hz
  obtain ⟨hab, hb, hs, hsI⟩ := area_section_geometry k hδ hz
  rw [heF, areaPhysicalOpenSection_eq_Ioo]
  exact hS.area_section_variation_measure_eq_jacobian k hab.le hb hs hsI hF
    ((area_physical_clamped_eq_on_section k d.rawFields a δ z).mono Ioo_subset_Icc_self)

/-- On every cutoff the physical kernel carrier agrees with the
smooth analytic area of its ordered planar map. -/
theorem areaBVPhysicalMeasure_eq_smooth
    {a₀ : ℕ → ℝ → ℝ} {D D₁ : ℝ≥0∞} {C C₁ : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a₁ : ℝ → ℝ}
    (hS : SmoothSolutionBounds a₁ D₁ C₁ d.rawFields) (k : AreaSectionPair)
    {a δ : ℝ} (hδ : 0 < δ) (hδa : δ < a) :
    areaBVPhysicalMeasure h hD d k hδ hδa =
      (smoothAnalyticArea (areaPairMap k d.rawFields)).restrict (areaInteriorCutoff δ a) := by
  apply Measure.ext
  intro E hE
  rw [areaBVPhysicalMeasure_apply h hD d k hδ hδa hE,
    Measure.restrict_apply hE, hS.analytic_area_physical_formula k hδ hE]
  apply lintegral_congr
  intro z
  let c := areaPhysicalPoint k z
  have hc : Continuous c :=
    (area_physical_point_continuous k).comp (continuous_const.prodMk continuous_id)
  have hpre : MeasurableSet (c ⁻¹' (E ∩ areaInteriorCutoff δ a)) :=
    hc.measurable (hE.inter (measurableSet_areaInteriorCutoff δ a))
  have hi : (fun t => (E ∩ areaInteriorCutoff δ a).indicator
      (fun p => ENNReal.ofReal |(fderiv ℝ (areaPairMap k d.rawFields) p).det|) (c t)) =
      (c ⁻¹' (E ∩ areaInteriorCutoff δ a)).indicator
        (fun t => ENNReal.ofReal |(fderiv ℝ (areaPairMap k d.rawFields) (c t)).det|) := by
    funext t
    exact (indicator_comp_right c).symm
  change (areaBVPhysicalKernel h hD d k hδ hδa z) (c ⁻¹' (E ∩ areaInteriorCutoff δ a)) = _
  rw [hi, lintegral_indicator hpre]
  by_cases hz : z ∈ areaTransverseInterval k a δ
  · have he := areaBVPhysicalKernel_restrict_eq_smooth h hD d hS k hδ hδa hz
    have hv := congrArg (fun μ : Measure ℝ => μ (c ⁻¹' E)) he
    have hEpre : MeasurableSet (c ⁻¹' E) := hc.measurable hE
    have hJ : MeasurableSet (areaPhysicalOpenSection k a δ z) := by
      rw [areaPhysicalOpenSection_eq_Ioo]
      exact measurableSet_Ioo
    rw [Measure.restrict_apply hEpre, Measure.restrict_apply hEpre,
      withDensity_apply _ (hEpre.inter hJ)] at hv
    rw [preimage_inter, area_physical_preimage_interior_of_mem k hz]
    exact hv
  · rw [preimage_inter, area_physical_preimage_interior_of_not_mem k hz, inter_empty,
      measure_empty, setLIntegral_empty]

/-- The global BV carrier is the smooth analytic area on the strict
interior whenever its field is one of the bounded C¹ fields. -/
theorem bv_analytic_area_eq_smooth_on_interior
    {a₀ : ℕ → ℝ → ℝ} {D D₁ : ℝ≥0∞} {C C₁ : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a₁ : ℝ → ℝ}
    (hS : SmoothSolutionBounds a₁ D₁ C₁ d.rawFields) (k : AreaSectionPair) :
    bvAnalyticArea h hD d k =
      (smoothAnalyticArea (areaPairMap k d.rawFields)).restrict areaSmoothDomain := by
  apply Measure.ext
  intro E hE
  rw [bvAnalyticArea_apply h hD d k hE, Measure.restrict_apply hE]
  simp_rw [areaBVPhysicalMeasure_eq_smooth h hD d hS k,
    Measure.restrict_apply hE]
  have hm : Monotone fun n => E ∩
      areaInteriorCutoff (areaExhaustionGap n) (areaExhaustionUpper n) :=
    fun m n hmn => inter_subset_inter_right _ (areaInteriorCutoff_exhaustion_monotone hmn)
  rw [← hm.measure_iUnion, ← inter_iUnion, areaInteriorCutoff_iUnion_eq]
  rfl

/-- The initial characteristic has zero smooth analytic area for every
total planar map, since its planar Lebesgue measure is zero. -/
theorem smooth_analytic_area_initial_edge (F : ℝ × ℝ → ℝ × ℝ) :
    smoothAnalyticArea F {p : ℝ × ℝ | p.1 = 0} = 0 := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.1 = 0} :=
    measurableSet_eq_fun measurable_fst measurable_const
  have hline : (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | p.1 = 0} = 0 := by
    have he : {p : ℝ × ℝ | p.1 = 0} = ({0} : Set ℝ) ×ˢ univ := by
      ext p
      simp only [mem_ofPred_eq, mem_prod, mem_singleton_iff, mem_univ, and_true]
    rw [Measure.volume_eq_prod ℝ ℝ, he, Measure.prod_prod]
    simp only [measure_singleton, zero_mul]
  rw [smooth_analytic_area F hmeas,
    Measure.restrict_eq_zero.mpr hline, lintegral_zero_measure]

/-- Agreement with the smooth analytic area on the full global domain,
including its initial characteristic. -/
theorem bv_analytic_area_eq_smooth
    {a₀ : ℕ → ℝ → ℝ} {D D₁ : ℝ≥0∞} {C C₁ : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a₁ : ℝ → ℝ}
    (hS : SmoothSolutionBounds a₁ D₁ C₁ d.rawFields) (k : AreaSectionPair) :
    bvAnalyticArea h hD d k =
      (smoothAnalyticArea (areaPairMap k d.rawFields)).restrict globalDomain := by
  rw [bv_analytic_area_eq_smooth_on_interior h hD d hS k]
  apply Measure.restrict_congr_set
  have hz : ∀ᵐ p ∂smoothAnalyticArea (areaPairMap k d.rawFields), p.1 ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using smooth_analytic_area_initial_edge (areaPairMap k d.rawFields)
  filter_upwards [hz] with p hp
  apply propext
  change (0 < p.1 ∧ p.1 < p.2) ↔ (0 ≤ p.1 ∧ p.1 < p.2)
  exact ⟨fun h => ⟨h.1.le, h.2⟩,
    fun h => ⟨lt_of_le_of_ne h.1 hp.symm, h.2⟩⟩

end ChristodoulouBV

end
