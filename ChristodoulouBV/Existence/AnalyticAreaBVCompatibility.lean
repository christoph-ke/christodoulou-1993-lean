module

public import ChristodoulouBV.Existence.AnalyticAreaBVOverlap
import Mathlib.Tactic

/-!
# Compatibility of the local area measures

All truncations are indexed by the same physical transverse variable.
Their section variation measures agree on overlaps, so their two
dimensional area measures agree after restriction to either overlap.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Membership in an interior cutoff splits into admissibility of the
transverse coordinate and membership in its open physical section. -/
theorem area_physical_point_mem_interior_iff (k : AreaSectionPair) (δ a z t : ℝ) :
    areaPhysicalPoint k z t ∈ areaInteriorCutoff δ a ↔
      z ∈ areaTransverseInterval k a δ ∧ t ∈ areaPhysicalOpenSection k a δ z := by
  cases hki : k.incoming with
  | false =>
    simp only [areaPhysicalPoint, areaInteriorCutoff, areaOpenCutoff,
      areaTransverseInterval, areaTransverseShift, areaPhysicalOpenSection,
      hki, Bool.false_eq_true, ite_false, zero_add, mem_inter_iff, mem_ofPred_eq, mem_Ioo]
    constructor
    · rintro ⟨⟨hz, hta, hgap⟩, hz'⟩
      exact ⟨⟨hz', by linarith only [hta, hgap]⟩,
        by linarith only [hgap], hta⟩
    · rintro ⟨⟨hz, _⟩, hgap, hta⟩
      exact ⟨⟨hz.le, hta, by linarith only [hgap]⟩, hz⟩
  | true =>
    simp only [areaPhysicalPoint, areaInteriorCutoff, areaOpenCutoff,
      areaTransverseInterval, areaTransverseShift, areaPhysicalOpenSection,
      hki, ite_true, mem_inter_iff, mem_ofPred_eq, mem_Ioo]
    constructor
    · rintro ⟨⟨_, hza, hgap⟩, ht⟩
      exact ⟨⟨by linarith only [hgap, ht], by linarith only [hza]⟩,
        ht, by linarith only [hgap]⟩
    · rintro ⟨⟨_, hza⟩, ht, hgap⟩
      exact ⟨⟨ht.le, by linarith only [hza], by linarith only [hgap]⟩, ht⟩

/-- At an admissible transverse coordinate the cutoff's preimage is
exactly the open physical section. -/
theorem area_physical_preimage_interior_of_mem (k : AreaSectionPair)
    {δ a z : ℝ} (hz : z ∈ areaTransverseInterval k a δ) :
    areaPhysicalPoint k z ⁻¹' areaInteriorCutoff δ a = areaPhysicalOpenSection k a δ z := by
  ext t
  simp only [mem_preimage, area_physical_point_mem_interior_iff, hz, true_and]

/-- At an inadmissible transverse coordinate the cutoff's section is empty. -/
theorem area_physical_preimage_interior_of_not_mem (k : AreaSectionPair)
    {δ a z : ℝ} (hz : z ∉ areaTransverseInterval k a δ) :
    areaPhysicalPoint k z ⁻¹' areaInteriorCutoff δ a = ∅ := by
  ext t
  simp only [mem_preimage, area_physical_point_mem_interior_iff, hz, false_and,
    mem_empty_iff_false]

/-- Local analytic areas give the same measure on the overlap of any
two open off-axis truncations. -/
theorem areaBVPhysicalMeasure_restrict_comm
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ a' δ' : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) (hδ' : 0 < δ') (hδa' : δ' < a') :
    (areaBVPhysicalMeasure h hD d k hδ hδa).restrict (areaInteriorCutoff δ' a') =
      (areaBVPhysicalMeasure h hD d k hδ' hδa').restrict (areaInteriorCutoff δ a) := by
  apply Measure.ext
  intro E hE
  rw [Measure.restrict_apply hE, Measure.restrict_apply hE,
    areaBVPhysicalMeasure_apply h hD d k hδ hδa
      (hE.inter (measurableSet_areaInteriorCutoff δ' a')),
    areaBVPhysicalMeasure_apply h hD d k hδ' hδa'
      (hE.inter (measurableSet_areaInteriorCutoff δ a))]
  apply lintegral_congr
  intro z
  change (areaBVPhysicalKernel h hD d k hδ hδa z)
      (areaPhysicalPoint k z ⁻¹' ((E ∩ areaInteriorCutoff δ' a') ∩ areaInteriorCutoff δ a)) =
    (areaBVPhysicalKernel h hD d k hδ' hδa' z)
      (areaPhysicalPoint k z ⁻¹' ((E ∩ areaInteriorCutoff δ a) ∩ areaInteriorCutoff δ' a'))
  simp only [preimage_inter]
  by_cases hz : z ∈ areaTransverseInterval k a δ
  · rw [area_physical_preimage_interior_of_mem k hz]
    by_cases hz' : z ∈ areaTransverseInterval k a' δ'
    · rw [area_physical_preimage_interior_of_mem k hz']
      have hk := areaBVPhysicalKernel_restrict_overlap h hD d k hδ hδa hδ' hδa' hz hz'
      have hv := congrArg (fun μ : Measure ℝ => μ (areaPhysicalPoint k z ⁻¹' E)) hk
      have hp : MeasurableSet (areaPhysicalPoint k z ⁻¹' E) :=
        ((area_physical_point_continuous k).comp
          (continuous_const.prodMk continuous_id)).measurable hE
      rw [Measure.restrict_apply hp, Measure.restrict_apply hp] at hv
      simpa only [inter_assoc, inter_left_comm, inter_comm] using hv
    · rw [area_physical_preimage_interior_of_not_mem k hz']
      simp only [inter_empty, empty_inter, measure_empty]
  · rw [area_physical_preimage_interior_of_not_mem k hz]
    simp only [inter_empty, empty_inter, measure_empty]

/-- A local measure restricted to a containing cutoff is unchanged. -/
theorem areaBVPhysicalMeasure_restrict_of_subset
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E)
    (hs : areaInteriorCutoff δ a ⊆ E) :
    (areaBVPhysicalMeasure h hD d k hδ hδa).restrict E =
      areaBVPhysicalMeasure h hD d k hδ hδa := by
  rw [areaBVPhysicalMeasure, Measure.restrict_restrict hE, inter_eq_right.mpr hs]

/-- Inclusion of open cutoffs gives the exact restriction identity,
and hence the monotonicity needed for the global area measure. -/
theorem areaBVPhysicalMeasure_eq_restrict_of_subset
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ a' δ' : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) (hδ' : 0 < δ') (hδa' : δ' < a')
    (hs : areaInteriorCutoff δ a ⊆ areaInteriorCutoff δ' a') :
    areaBVPhysicalMeasure h hD d k hδ hδa =
      (areaBVPhysicalMeasure h hD d k hδ' hδa').restrict (areaInteriorCutoff δ a) := by
  rw [← areaBVPhysicalMeasure_restrict_comm h hD d k hδ hδa hδ' hδa',
    areaBVPhysicalMeasure_restrict_of_subset h hD d k hδ hδa
      (measurableSet_areaInteriorCutoff δ' a') hs]

end ChristodoulouBV

end
