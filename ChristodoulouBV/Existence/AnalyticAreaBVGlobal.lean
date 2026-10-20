module

public import ChristodoulouBV.Existence.AnalyticAreaBVCompatibility
public import ChristodoulouBV.Existence.AnalyticAreaBVMeasureLimit
import Mathlib.Tactic

/-!
# The global analytic BV area carrier

Compatible variation-measure kernels on open off-axis truncations give
one increasing exhaustion of measures. Its increasing limit is the
global carrier. The initial edge has zero area; no endpoint value is
used to create a boundary atom.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Upper coordinate cutoff in the canonical countable exhaustion. -/
@[expose] def areaExhaustionUpper (n : ℕ) : ℝ := (n : ℝ) + 2

/-- Positive gap cutoff in the canonical countable exhaustion. -/
@[expose] noncomputable def areaExhaustionGap (n : ℕ) : ℝ := 1 / areaExhaustionUpper n

/-- Every exhaustion gap is positive. -/
theorem area_exhaustion_gap_pos (n : ℕ) : 0 < areaExhaustionGap n := by
  unfold areaExhaustionGap areaExhaustionUpper
  positivity

/-- Every exhaustion chart is nondegenerate. -/
theorem area_exhaustion_gap_lt_upper (n : ℕ) :
    areaExhaustionGap n < areaExhaustionUpper n := by
  have ha : (1 : ℝ) < areaExhaustionUpper n := by
    unfold areaExhaustionUpper
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith only [hn]
  exact ((div_lt_one (lt_trans zero_lt_one ha)).mpr ha).trans ha

/-- Nested gap and upper cutoffs give nested interior domains. -/
theorem areaInteriorCutoff_mono {δ a δ' a' : ℝ} (hδ : δ' ≤ δ) (ha : a ≤ a') :
    areaInteriorCutoff δ a ⊆ areaInteriorCutoff δ' a' := by
  rintro p ⟨⟨hu, hv, hgap⟩, hu'⟩
  exact ⟨⟨hu, hv.trans_le ha, hδ.trans_lt hgap⟩, hu'⟩

/-- The interior domains in the canonical exhaustion are increasing. -/
theorem areaInteriorCutoff_exhaustion_monotone :
    Monotone fun n => areaInteriorCutoff (areaExhaustionGap n) (areaExhaustionUpper n) := by
  intro m n hmn
  have ha : areaExhaustionUpper m ≤ areaExhaustionUpper n := by
    unfold areaExhaustionUpper
    have hh : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
    linarith only [hh]
  apply areaInteriorCutoff_mono _ ha
  exact one_div_le_one_div_of_le (by unfold areaExhaustionUpper; positivity) ha

/-- The exhaustion covers exactly the strict interior of the global domain. -/
theorem areaInteriorCutoff_iUnion_eq :
    (⋃ n, areaInteriorCutoff (areaExhaustionGap n) (areaExhaustionUpper n)) =
      {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} := by
  ext p
  constructor
  · intro hp
    obtain ⟨n, hn⟩ := mem_iUnion.mp hp
    exact ⟨hn.2, (areaOpenCutoff_subset_globalDomain (area_exhaustion_gap_pos n) hn.1).2⟩
  · rintro ⟨hu, huv⟩
    have hp : p ∈ globalDomain := ⟨hu.le, huv⟩
    rw [← areaOpenCutoff_iUnion_eq_globalDomain] at hp
    obtain ⟨n, hn⟩ := mem_iUnion.mp hp
    refine mem_iUnion.mpr ⟨n, ⟨?_, ?_, ?_⟩, hu⟩
    · exact hn.1
    · change p.2 < (n : ℝ) + 2
      linarith only [hn.2.1]
    · apply lt_of_le_of_lt _ hn.2.2
      exact one_div_le_one_div_of_le (by positivity)
        (by unfold areaExhaustionUpper; linarith)

/-- Compatibility makes the physical area measures in the exhaustion increasing. -/
theorem areaBVPhysicalMeasure_exhaustion_monotone
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) :
    Monotone fun n => areaBVPhysicalMeasure h hD d k
      (area_exhaustion_gap_pos n) (area_exhaustion_gap_lt_upper n) := by
  intro m n hmn
  change areaBVPhysicalMeasure h hD d k
    (area_exhaustion_gap_pos m) (area_exhaustion_gap_lt_upper m) ≤
      areaBVPhysicalMeasure h hD d k
        (area_exhaustion_gap_pos n) (area_exhaustion_gap_lt_upper n)
  rw [areaBVPhysicalMeasure_eq_restrict_of_subset h hD d k
    (area_exhaustion_gap_pos m) (area_exhaustion_gap_lt_upper m)
    (area_exhaustion_gap_pos n) (area_exhaustion_gap_lt_upper n)
    (areaInteriorCutoff_exhaustion_monotone hmn)]
  exact Measure.restrict_le_self

/-- The global analytic area measure of the actual shared BV limit.
It integrates the section variation measures, rather than the raw
closed-section pointwise variations. -/
@[expose] noncomputable def bvAnalyticArea
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) : Measure (ℝ × ℝ) :=
  increasingAreaMeasure (fun n => areaBVPhysicalMeasure h hD d k
    (area_exhaustion_gap_pos n) (area_exhaustion_gap_lt_upper n))
      (areaBVPhysicalMeasure_exhaustion_monotone h hD d k)

/-- Measurable-set evaluation of the global analytic carrier is the
increasing supremum of its compatible local restrictions. -/
theorem bvAnalyticArea_apply
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {E : Set (ℝ × ℝ)}
    (hE : MeasurableSet E) :
    bvAnalyticArea h hD d k E = ⨆ n, areaBVPhysicalMeasure h hD d k
      (area_exhaustion_gap_pos n) (area_exhaustion_gap_lt_upper n) E :=
  increasingAreaMeasure_apply _ _ hE

/-- The global carrier restricts to the original local measure on every
open off-axis interior cutoff, independently of the exhaustion. -/
theorem bvAnalyticArea_restrict_interior
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    (bvAnalyticArea h hD d k).restrict (areaInteriorCutoff δ a) =
      areaBVPhysicalMeasure h hD d k hδ hδa := by
  apply Measure.ext
  intro E hE
  rw [Measure.restrict_apply hE,
    bvAnalyticArea_apply h hD d k (hE.inter (measurableSet_areaInteriorCutoff δ a))]
  have he (n : ℕ) : areaBVPhysicalMeasure h hD d k
      (area_exhaustion_gap_pos n) (area_exhaustion_gap_lt_upper n)
        (E ∩ areaInteriorCutoff δ a) =
      areaBVPhysicalMeasure h hD d k hδ hδa
        (E ∩ areaInteriorCutoff (areaExhaustionGap n) (areaExhaustionUpper n)) := by
    have hr := areaBVPhysicalMeasure_restrict_comm h hD d k
      (area_exhaustion_gap_pos n) (area_exhaustion_gap_lt_upper n) hδ hδa
    have hv := congrArg (fun μ : Measure (ℝ × ℝ) => μ E) hr
    simpa only [Measure.restrict_apply hE] using hv
  simp_rw [he]
  have hm : Monotone fun n => E ∩
      areaInteriorCutoff (areaExhaustionGap n) (areaExhaustionUpper n) :=
    fun m n hmn => inter_subset_inter_right _ (areaInteriorCutoff_exhaustion_monotone hmn)
  rw [← hm.measure_iUnion, ← inter_iUnion, areaInteriorCutoff_iUnion_eq]
  have hs : areaInteriorCutoff δ a ⊆ {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} := by
    intro p hp
    exact ⟨hp.2, (areaOpenCutoff_subset_globalDomain hδ hp.1).2⟩
  have hr := areaBVPhysicalMeasure_restrict_of_subset h hD d k hδ hδa
    ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd)) hs
  have hv := congrArg (fun μ : Measure (ℝ × ℝ) => μ E) hr
  simpa only [Measure.restrict_apply hE, Set.ofPred_and] using hv

/-- Restricting the global analytic carrier to `u>0` does not change it. -/
theorem bvAnalyticArea_restrict_positive_u
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) :
    (bvAnalyticArea h hD d k).restrict {p | 0 < p.1} = bvAnalyticArea h hD d k := by
  apply Measure.ext
  intro E hE
  rw [Measure.restrict_apply hE,
    bvAnalyticArea_apply h hD d k
      (hE.inter (measurableSet_lt measurable_const measurable_fst)),
    bvAnalyticArea_apply h hD d k hE]
  congr 1
  funext n
  have hr := areaBVPhysicalMeasure_restrict_of_subset h hD d k
    (area_exhaustion_gap_pos n) (area_exhaustion_gap_lt_upper n)
    (measurableSet_lt measurable_const measurable_fst) (fun _ hp => hp.2)
  have hv := congrArg (fun μ : Measure (ℝ × ℝ) => μ E) hr
  simpa only [Measure.restrict_apply hE] using hv

/-- The global analytic carrier on an open cutoff is the mass of its
local transverse variation-measure construction. This is the local
carrier rule used in the area limit estimates, with no claim about multiplicity image area. -/
theorem bv_analytic_area
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    bvAnalyticArea h hD d k (areaOpenCutoff δ a) =
      areaBVPhysicalMeasure h hD d k hδ hδa univ := by
  have hs := congrArg (fun μ : Measure (ℝ × ℝ) => μ (areaOpenCutoff δ a))
    (bvAnalyticArea_restrict_positive_u h hD d k)
  rw [Measure.restrict_apply (measurableSet_areaOpenCutoff δ a)] at hs
  rw [← hs]
  have hr := congrArg (fun μ : Measure (ℝ × ℝ) => μ univ)
    (bvAnalyticArea_restrict_interior h hD d k hδ hδa)
  simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter, areaInteriorCutoff]
    using hr

end ChristodoulouBV

end
