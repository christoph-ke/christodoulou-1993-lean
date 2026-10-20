module

public import ChristodoulouBV.Existence.AreaLimitBoundsCore
import Mathlib.Tactic

/-!
# Removing the area cutoffs

The gap tends to zero before the upper coordinate cutoff tends to infinity.
The supremum/liminf comparison is proved explicitly for measures. Closed
cutoffs give uniform bounds; lower semicontinuity of the carrier is used on
open cutoffs, in accordance with the corrected boundary convention.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The source's finite upper cutoff, with its terminal characteristic. -/
@[expose] def areaFiniteCutoff (a : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ globalDomain ∧ p.2 ≤ a}

/-- The open upper cutoff used for carrier lower semicontinuity. -/
@[expose] def areaOpenFiniteCutoff (a : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ globalDomain ∧ p.2 < a}

/-- Both finite upper cutoffs are measurable. -/
theorem measurableSet_areaFiniteCutoff (a : ℝ) : MeasurableSet (areaFiniteCutoff a) := by
  change MeasurableSet {p : ℝ × ℝ | (0 ≤ p.1 ∧ p.1 < p.2) ∧ p.2 ≤ a}
  exact ((measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_lt measurable_fst measurable_snd)).inter
      (measurableSet_le measurable_snd measurable_const)

/-- The open finite upper cutoff is measurable. -/
theorem measurableSet_areaOpenFiniteCutoff (a : ℝ) :
    MeasurableSet (areaOpenFiniteCutoff a) := by
  change MeasurableSet {p : ℝ × ℝ | (0 ≤ p.1 ∧ p.1 < p.2) ∧ p.2 < a}
  exact ((measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_lt measurable_fst measurable_snd)).inter
      (measurableSet_lt measurable_snd measurable_const)

private theorem gap_cutoff_pos_lt {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 < a / ((n : ℝ) + 2) ∧ a / ((n : ℝ) + 2) < a := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨div_pos ha (by positivity), (div_lt_iff₀ (by positivity)).mpr ?_⟩
  nlinarith only [ha, hn, mul_nonneg ha.le hn]

private theorem gap_cutoff_antitone {a : ℝ} (ha : 0 < a) :
    Antitone fun n : ℕ => a / ((n : ℝ) + 2) := by
  intro m n hmn
  have hmn' : (m : ℝ) + 2 ≤ (n : ℝ) + 2 := by
    exact_mod_cast Nat.add_le_add_right hmn 2
  exact div_le_div_of_nonneg_left ha.le (by positivity)
    hmn'

private theorem exists_gap_cutoff_lt {a g : ℝ} (_ha : 0 < a) (hg : 0 < g) :
    ∃ n : ℕ, a / ((n : ℝ) + 2) < g := by
  obtain ⟨n, hn⟩ := exists_nat_gt (a / g)
  refine ⟨n, (div_lt_iff₀ (by positivity)).mpr ?_⟩
  have hn' := (div_lt_iff₀ hg).mp hn
  nlinarith only [hn', hg]

/-- Closed gap cutoffs increase to the source's finite upper cutoff. -/
theorem areaClosedCutoff_gap_exhaustion {a : ℝ} (ha : 0 < a) :
    Monotone (fun n : ℕ => areaClosedCutoff (a / ((n : ℝ) + 2)) a) ∧
      (⋃ n : ℕ, areaClosedCutoff (a / ((n : ℝ) + 2)) a) = areaFiniteCutoff a := by
  refine ⟨fun m n hmn p hp => ⟨hp.1, hp.2.1,
    (gap_cutoff_antitone ha hmn).trans hp.2.2⟩, ?_⟩
  apply Subset.antisymm
  · exact iUnion_subset fun _ _ hp => ⟨hp.1, hp.2.1⟩
  · intro p hp
    obtain ⟨n, hn⟩ := exists_gap_cutoff_lt ha (sub_pos.mpr hp.1.2)
    exact mem_iUnion.mpr ⟨n, hp.1, hp.2, hn.le⟩

/-- Open gap cutoffs increase to the open finite upper cutoff. -/
theorem areaOpenCutoff_gap_exhaustion {a : ℝ} (ha : 0 < a) :
    Monotone (fun n : ℕ => areaOpenCutoff (a / ((n : ℝ) + 2)) a) ∧
      (⋃ n : ℕ, areaOpenCutoff (a / ((n : ℝ) + 2)) a) =
        areaOpenFiniteCutoff a := by
  refine ⟨fun m n hmn p hp => ⟨hp.1, hp.2.1,
    (gap_cutoff_antitone ha hmn).trans_lt hp.2.2⟩, ?_⟩
  apply Subset.antisymm
  · apply iUnion_subset
    intro n p hp
    exact ⟨areaOpenCutoff_subset_globalDomain (gap_cutoff_pos_lt ha n).1 hp, hp.2.1⟩
  · intro p hp
    obtain ⟨n, hn⟩ := exists_gap_cutoff_lt ha (sub_pos.mpr hp.1.2)
    exact mem_iUnion.mpr ⟨n, hp.1.1, hp.2, hn⟩

/-- Measure continuity for the source's `δ↓0` exhaustion. -/
theorem measure_areaClosedCutoff_tendsto (μ : Measure (ℝ × ℝ))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => μ (areaClosedCutoff (a / ((n : ℝ) + 2)) a))
      atTop (𝓝 (μ (areaFiniteCutoff a))) := by
  obtain ⟨hm, he⟩ := areaClosedCutoff_gap_exhaustion ha
  simpa only [he, Function.comp_def] using tendsto_measure_iUnion_atTop (μ := μ) hm

/-- The measure supremum/liminf comparison needed when removing a cutoff. -/
theorem measure_iUnion_le_liminf_of_cutoffs
    (μ : Measure (ℝ × ℝ)) (ν : ℕ → Measure (ℝ × ℝ))
    (E : ℕ → Set (ℝ × ℝ)) (hm : Monotone E)
    (hcut : ∀ j, μ (E j) ≤ liminf (fun n => ν n (E j)) atTop) :
    μ (⋃ j, E j) ≤ liminf (fun n => ν n (⋃ j, E j)) atTop := by
  rw [hm.measure_iUnion]
  apply iSup_le
  intro j
  exact (hcut j).trans (liminf_le_liminf (Eventually.of_forall fun _ =>
    measure_mono (subset_iUnion E j)))

/-- The carrier liminf after `δ↓0`. Its upper cutoff is open, since a
terminal characteristic can carry positive BV area. -/
theorem bv_analytic_area_open_finite_cutoff_le_liminf
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a : ℝ} (ha : 0 < a) :
    bvAnalyticArea h hD d k (areaOpenFiniteCutoff a) ≤
      liminf (fun n => smoothAnalyticArea (areaPairMap k (T (d.subsequence n)))
        (areaOpenFiniteCutoff a)) atTop := by
  obtain ⟨hm, he⟩ := areaOpenCutoff_gap_exhaustion ha
  rw [← he]
  apply measure_iUnion_le_liminf_of_cutoffs _ _ _ hm
  intro j
  exact bv_analytic_area_open_le_liminf h hD d k
    (gap_cutoff_pos_lt ha j).1 (gap_cutoff_pos_lt ha j).2

/-- The pointwise form of (6.5): removing the gap cutoff by a supremum
preserves the liminf inequality on the source's closed finite domain.
The pointwise convention and the carrier convention remain separate. -/
theorem eq6_5
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n))
    (d : RadiusLimitData T) (k : AreaSectionPair) (a : ℝ) :
    (⨆ δ : Ioo (0 : ℝ) a, areaPointwiseFunctional k d.rawFields a δ) ≤
      liminf (fun n => smoothAnalyticArea (areaPairMap k (T (d.subsequence n)))
        (areaFiniteCutoff a)) atTop := by
  apply iSup_le
  intro δ
  exact (area_pointwise_functional_le_liminf_closed h d k δ.property.1
    δ.property.2).trans (liminf_le_liminf (Eventually.of_forall fun _ =>
      measure_mono (fun _ hp => ⟨hp.1, hp.2.1⟩)))

/-- The D-only bound survives `δ↓0`, including the terminal characteristic
of the source's closed finite upper cutoff. -/
theorem bv_analytic_area_finite_cutoff_bound
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a : ℝ} (ha : 0 < a) :
    bvAnalyticArea h hD d k (areaFiniteCutoff a) ≤ areaPairBound D k := by
  apply le_of_tendsto (measure_areaClosedCutoff_tendsto _ ha)
  exact Eventually.of_forall fun n => bv_analytic_area_closed_bound h hD d k
    (gap_cutoff_pos_lt ha n).1 (gap_cutoff_pos_lt ha n).2

/-- Explicit D-only bounds and finiteness after `δ↓0`, separately for
the pointwise exhaustion and the closed finite-domain carrier. -/
theorem eq6_5_finite
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a : ℝ} (ha : 0 < a) :
    (⨆ δ : Ioo (0 : ℝ) a, areaPointwiseFunctional k d.rawFields a δ) ≤
        areaPairBound D k ∧
      (⨆ δ : Ioo (0 : ℝ) a, areaPointwiseFunctional k d.rawFields a δ) ≠ ∞ ∧
      bvAnalyticArea h hD d k (areaFiniteCutoff a) ≤ areaPairBound D k ∧
      bvAnalyticArea h hD d k (areaFiniteCutoff a) ≠ ∞ := by
  have hp := (eq6_5 h d k a).trans
    (smooth_area_liminf_le_pair_bound h d k (fun _ hp => hp.1))
  have hc := bv_analytic_area_finite_cutoff_bound h hD d k ha
  have hf := area_pair_bound_ne_top hD k
  exact ⟨hp, ne_top_of_le_ne_top hf hp, hc, ne_top_of_le_ne_top hf hc⟩

/-- Finite upper cutoffs increase to the full global domain. -/
theorem areaFiniteCutoff_exhaustion :
    Monotone (fun n : ℕ => areaFiniteCutoff ((n : ℝ) + 1)) ∧
      (⋃ n : ℕ, areaFiniteCutoff ((n : ℝ) + 1)) = globalDomain := by
  refine ⟨?_, ?_⟩
  · intro m n hmn p hp
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hmn 1
    exact ⟨hp.1, hp.2.trans hmn'⟩
  apply Subset.antisymm
  · exact iUnion_subset fun _ _ hp => hp.1
  · intro p hp
    obtain ⟨n, hn⟩ := exists_nat_gt p.2
    exact mem_iUnion.mpr ⟨n, hp, hn.le.trans (le_add_of_nonneg_right zero_le_one)⟩

/-- Open finite upper cutoffs also increase to the full global domain. -/
theorem areaOpenFiniteCutoff_exhaustion :
    Monotone (fun n : ℕ => areaOpenFiniteCutoff ((n : ℝ) + 1)) ∧
      (⋃ n : ℕ, areaOpenFiniteCutoff ((n : ℝ) + 1)) = globalDomain := by
  refine ⟨?_, ?_⟩
  · intro m n hmn p hp
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hmn 1
    exact ⟨hp.1, hp.2.trans_le hmn'⟩
  apply Subset.antisymm
  · exact iUnion_subset fun _ _ hp => hp.1
  · intro p hp
    obtain ⟨n, hn⟩ := exists_nat_gt p.2
    exact mem_iUnion.mpr ⟨n, hp, hn.trans (lt_add_one _)⟩

/-- Measure continuity for the source's `a↑∞` exhaustion. -/
theorem measure_areaFiniteCutoff_tendsto (μ : Measure (ℝ × ℝ)) :
    Tendsto (fun n : ℕ => μ (areaFiniteCutoff ((n : ℝ) + 1)))
      atTop (𝓝 (μ globalDomain)) := by
  obtain ⟨hm, he⟩ := areaFiniteCutoff_exhaustion
  simpa only [he, Function.comp_def] using tendsto_measure_iUnion_atTop (μ := μ) hm

/-- Global carrier lower semicontinuity after both exhaustions. -/
theorem bv_analytic_area_global_le_liminf
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) :
    bvAnalyticArea h hD d k globalDomain ≤
      liminf (fun n => smoothAnalyticArea (areaPairMap k (T (d.subsequence n)))
        globalDomain) atTop := by
  obtain ⟨hm, he⟩ := areaOpenFiniteCutoff_exhaustion
  rw [← he]
  apply measure_iUnion_le_liminf_of_cutoffs _ _ _ hm
  exact fun n => bv_analytic_area_open_finite_cutoff_le_liminf h hD d k (by positivity)

/-- Global D-only bounds with the same universal coefficient as the smooth area estimates. -/
theorem bv_analytic_area_global_bound
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) :
    bvAnalyticArea h hD d k globalDomain ≤ areaPairBound D k :=
  (bv_analytic_area_global_le_liminf h hD d k).trans
    (smooth_area_liminf_le_pair_bound h d k Subset.rfl)

/-- The pointwise form of the global liminf in (6.6), with both cutoff
suprema explicit. This does not identify the pointwise exhaustion with
the countably additive carrier. -/
theorem area_global_pointwise_le_liminf
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n))
    (d : RadiusLimitData T) (k : AreaSectionPair) :
    (⨆ a : Ioi (0 : ℝ), ⨆ δ : Ioo (0 : ℝ) a,
      areaPointwiseFunctional k d.rawFields a δ) ≤
      liminf (fun n => smoothAnalyticArea (areaPairMap k (T (d.subsequence n)))
        globalDomain) atTop := by
  apply iSup_le
  intro a
  exact (eq6_5 h d k a).trans (liminf_le_liminf
    (Eventually.of_forall fun _ => measure_mono (fun _ hp => hp.1)))

/-- The full pointwise exhaustion has its own universal D-only bound
and finiteness proof, independently of the carrier's global finiteness. -/
theorem area_global_pointwise_finite
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) :
    (⨆ a : Ioi (0 : ℝ), ⨆ δ : Ioo (0 : ℝ) a,
      areaPointwiseFunctional k d.rawFields a δ) ≤ areaPairBound D k ∧
      (⨆ a : Ioi (0 : ℝ), ⨆ δ : Ioo (0 : ℝ) a,
        areaPointwiseFunctional k d.rawFields a δ) ≠ ∞ := by
  have hb := (area_global_pointwise_le_liminf h d k).trans
    (smooth_area_liminf_le_pair_bound h d k Subset.rfl)
  exact ⟨hb, ne_top_of_le_ne_top (area_pair_bound_ne_top hD k) hb⟩

/-- Explicit global finiteness, derived from the smooth quantitative bound. -/
theorem bv_analytic_area_global_finite
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) :
    bvAnalyticArea h hD d k globalDomain ≠ ∞ :=
  ne_top_of_le_ne_top (area_pair_bound_ne_top hD k)
    (bv_analytic_area_global_bound h hD d k)

end ChristodoulouBV

end
