module

public import ChristodoulouBV.Existence.AnalyticAreaBVGlobal
public import ChristodoulouBV.Existence.AnalyticAreaBVSectionGeometry
import Mathlib.Tactic

/-!
# The global transverse variation-measure formula

The global section kernel is the increasing union of the local
Stieltjes variation measures on their open sections. Monotone
convergence identifies its transverse integral with `bvAnalyticArea`.
-/

public section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem measurable_physical_section_graph (k : AreaSectionPair) (a δ : ℝ) :
    MeasurableSet {p : ℝ × ℝ | p.2 ∈ areaPhysicalOpenSection k a δ p.1} := by
  cases hki : k.incoming with
  | false =>
    simp only [areaPhysicalOpenSection, hki, Bool.false_eq_true, ite_false, mem_Ioo]
    exact (measurableSet_lt (measurable_fst.add_const δ) measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const)
  | true =>
    simp only [areaPhysicalOpenSection, hki, ite_true, mem_Ioo]
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_fst.sub_const δ))

/-- The local variation measure restricted to its open physical section,
still indexed by the physical transverse coordinate. -/
@[expose] noncomputable def areaBVOpenSectionKernel
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) : Kernel ℝ ℝ where
  toFun z := (areaBVPhysicalKernel h hD d k hδ hδa z).restrict (areaPhysicalOpenSection k a δ z)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro E hE
    simp_rw [Measure.restrict_apply hE]
    exact Kernel.measurable_kernel_prodMk_left
      ((measurable_snd hE).inter (measurable_physical_section_graph k a δ))

/-- Evaluation of the open section kernel is restriction of the
Stieltjes variation measure, with no cutoff endpoint atom. -/
theorem areaBVOpenSectionKernel_apply
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) (z : ℝ) {E : Set ℝ} (hE : MeasurableSet E) :
    areaBVOpenSectionKernel h hD d k hδ hδa z E =
      areaBVPhysicalKernel h hD d k hδ hδa z (E ∩ areaPhysicalOpenSection k a δ z) :=
  Measure.restrict_apply hE

/-- The local open section kernels retain the finite uniform mass bound. -/
instance areaBVOpenSectionKernel_isFiniteKernel
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    IsFiniteKernel (areaBVOpenSectionKernel h hD d k hδ hδa) := by
  obtain ⟨V, hV, hb⟩ := (inferInstance :
    IsFiniteKernel (areaBVPhysicalKernel h hD d k hδ hδa)).exists_univ_le
  refine ⟨V, hV, fun z => ?_⟩
  rw [areaBVOpenSectionKernel_apply h hD d k hδ hδa z MeasurableSet.univ, univ_inter]
  exact (measure_mono (subset_univ _)).trans (hb z)

/-- Local physical area is the transverse integral of its open section
variation kernel on every measurable set. -/
theorem areaBVPhysicalMeasure_apply_openSection
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) :
    areaBVPhysicalMeasure h hD d k hδ hδa E = ∫⁻ z,
      areaBVOpenSectionKernel h hD d k hδ hδa z (areaPhysicalPoint k z ⁻¹' E) := by
  rw [areaBVPhysicalMeasure_apply h hD d k hδ hδa hE]
  apply lintegral_congr
  intro z
  have hp : MeasurableSet (areaPhysicalPoint k z ⁻¹' E) :=
    ((area_physical_point_continuous k).comp
      (continuous_const.prodMk continuous_id)).measurable hE
  rw [areaBVOpenSectionKernel_apply h hD d k hδ hδa z hp]
  change (areaBVPhysicalKernel h hD d k hδ hδa z)
      (areaPhysicalPoint k z ⁻¹' (E ∩ areaInteriorCutoff δ a)) = _
  by_cases hz : z ∈ areaTransverseInterval k a δ
  · rw [preimage_inter, area_physical_preimage_interior_of_mem k hz]
  · rw [areaBVPhysicalKernel_of_not_mem h hD d k hδ hδa hz]
    rfl

private theorem transverse_interval_mono (k : AreaSectionPair) {a δ a' δ' : ℝ}
    (ha : a ≤ a') (hδ : δ' ≤ δ) :
    areaTransverseInterval k a δ ⊆ areaTransverseInterval k a' δ' := by
  intro z hz
  cases hki : k.incoming <;>
    simp only [areaTransverseInterval, areaTransverseShift, hki, Bool.false_eq_true,
      ite_false, ite_true, zero_add, mem_Ioo] at hz ⊢ <;>
    constructor <;> linarith only [hz.1, hz.2, ha, hδ]

private theorem physical_open_section_mono (k : AreaSectionPair) {a δ a' δ' z : ℝ}
    (ha : a ≤ a') (hδ : δ' ≤ δ) :
    areaPhysicalOpenSection k a δ z ⊆ areaPhysicalOpenSection k a' δ' z := by
  cases hki : k.incoming <;>
    simp only [areaPhysicalOpenSection, hki, Bool.false_eq_true, ite_false, ite_true] <;>
    apply Ioo_subset_Ioo <;> linarith only [ha, hδ]

/-- Nested cutoffs give an increasing family of variation measures on
each fixed physical null section. -/
theorem areaBVOpenSectionKernel_mono_of_cutoffs
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ a' δ' : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) (hδ' : 0 < δ') (hδa' : δ' < a')
    (ha : a ≤ a') (hgap : δ' ≤ δ) (z : ℝ) :
    areaBVOpenSectionKernel h hD d k hδ hδa z ≤
      areaBVOpenSectionKernel h hD d k hδ' hδa' z := by
  change (areaBVPhysicalKernel h hD d k hδ hδa z).restrict
      (areaPhysicalOpenSection k a δ z) ≤
    (areaBVPhysicalKernel h hD d k hδ' hδa' z).restrict
      (areaPhysicalOpenSection k a' δ' z)
  by_cases hz : z ∈ areaTransverseInterval k a δ
  · have hz' := transverse_interval_mono k ha hgap hz
    have hs := physical_open_section_mono k ha hgap (z := z)
    have he := areaBVPhysicalKernel_restrict_overlap h hD d k hδ hδa hδ' hδa' hz hz'
    rw [inter_eq_left.mpr hs] at he
    rw [he]
    exact Measure.restrict_mono hs le_rfl
  · rw [areaBVPhysicalKernel_of_not_mem h hD d k hδ hδa hz]
    rw [Measure.restrict_zero]
    exact bot_le

/-- The canonical section variation measures increase on every section. -/
theorem areaBVOpenSectionKernel_exhaustion_monotone
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) (z : ℝ) :
    Monotone fun n => areaBVOpenSectionKernel h hD d k
      (area_exhaustion_gap_pos n) (area_exhaustion_gap_lt_upper n) z := by
  intro m n hmn
  have ha : areaExhaustionUpper m ≤ areaExhaustionUpper n := by
    unfold areaExhaustionUpper
    have hh : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
    linarith only [hh]
  exact areaBVOpenSectionKernel_mono_of_cutoffs h hD d k
    (area_exhaustion_gap_pos m) (area_exhaustion_gap_lt_upper m)
    (area_exhaustion_gap_pos n) (area_exhaustion_gap_lt_upper n) ha
    (one_div_le_one_div_of_le (by unfold areaExhaustionUpper; positivity) ha) z

/-- The section variation measure on the entire admissible null
section, obtained by joining its compatible local Stieltjes measures. -/
@[expose] noncomputable def areaBVGlobalSectionKernel
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) : Kernel ℝ ℝ where
  toFun z := increasingAreaMeasure (fun n => areaBVOpenSectionKernel h hD d k
    (area_exhaustion_gap_pos n) (area_exhaustion_gap_lt_upper n) z)
      (areaBVOpenSectionKernel_exhaustion_monotone h hD d k z)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro E hE
    simp_rw [increasingAreaMeasure_apply _ _ hE]
    exact Measurable.iSup fun n => (Measure.measurable_coe hE).comp
      (areaBVOpenSectionKernel h hD d k
        (area_exhaustion_gap_pos n) (area_exhaustion_gap_lt_upper n)).measurable

/-- Evaluation of the global section variation measure on a Borel set. -/
theorem areaBVGlobalSectionKernel_apply
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) (z : ℝ)
    {E : Set ℝ} (hE : MeasurableSet E) :
    areaBVGlobalSectionKernel h hD d k z E = ⨆ n,
      areaBVOpenSectionKernel h hD d k
        (area_exhaustion_gap_pos n) (area_exhaustion_gap_lt_upper n) z E :=
  increasingAreaMeasure_apply _
    (areaBVOpenSectionKernel_exhaustion_monotone h hD d k z) hE

/-- The global analytic area is literally the transverse integral of
the variation measures of its physical section primitives. -/
theorem bv_analytic_area_eq_section_integral
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {E : Set (ℝ × ℝ)}
    (hE : MeasurableSet E) :
    bvAnalyticArea h hD d k E = ∫⁻ z,
      areaBVGlobalSectionKernel h hD d k z (areaPhysicalPoint k z ⁻¹' E) := by
  rw [bvAnalyticArea_apply h hD d k hE]
  simp_rw [areaBVPhysicalMeasure_apply_openSection h hD d k _ _ hE]
  have hm : Monotone fun n z => areaBVOpenSectionKernel h hD d k
      (area_exhaustion_gap_pos n) (area_exhaustion_gap_lt_upper n) z
        (areaPhysicalPoint k z ⁻¹' E) :=
    fun m n hmn z => (areaBVOpenSectionKernel_exhaustion_monotone h hD d k z hmn) _
  have hmeas (n : ℕ) : Measurable fun z => areaBVOpenSectionKernel h hD d k
      (area_exhaustion_gap_pos n) (area_exhaustion_gap_lt_upper n) z
        (areaPhysicalPoint k z ⁻¹' E) :=
    Kernel.measurable_kernel_prodMk_left ((area_physical_point_continuous k).measurable hE)
  rw [← lintegral_iSup (μ := volume) hmeas hm]
  apply lintegral_congr
  intro z
  have hp : MeasurableSet (areaPhysicalPoint k z ⁻¹' E) :=
    ((area_physical_point_continuous k).comp
      (continuous_const.prodMk continuous_id)).measurable hE
  exact (areaBVGlobalSectionKernel_apply h hD d k z hp).symm

end ChristodoulouBV

end
