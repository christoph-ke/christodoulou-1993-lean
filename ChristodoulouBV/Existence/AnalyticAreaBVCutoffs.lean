module

public import ChristodoulouBV.Frozen.GlobalDomain
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Open and closed cutoffs for the analytic BV area

Closed cutoffs must be enlarged in both parameters before applying an
open-cutoff bound. Enlarging only the upper coordinate cutoff does not
include the boundary `v-u=δ`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The open cutoff used for comparison with pointwise section variation. -/
@[expose] def areaOpenCutoff (δ a : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.2 < a ∧ δ < p.2 - p.1}

/-- The source's closed off-axis cutoff inside the global domain. -/
@[expose] def areaClosedCutoff (δ a : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ globalDomain ∧ p.2 ≤ a ∧ δ ≤ p.2 - p.1}

/-- Open cutoffs are Borel measurable. -/
theorem measurableSet_areaOpenCutoff (δ a : ℝ) : MeasurableSet (areaOpenCutoff δ a) :=
  (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_snd measurable_const).inter
      (measurableSet_lt measurable_const (measurable_snd.sub measurable_fst)))

/-- The closed source cutoffs are Borel measurable. -/
theorem measurableSet_areaClosedCutoff (δ a : ℝ) : MeasurableSet (areaClosedCutoff δ a) := by
  change MeasurableSet {p : ℝ × ℝ |
    (0 ≤ p.1 ∧ p.1 < p.2) ∧ p.2 ≤ a ∧ δ ≤ p.2 - p.1}
  exact ((measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_lt measurable_fst measurable_snd)).inter
      ((measurableSet_le measurable_snd measurable_const).inter
        (measurableSet_le measurable_const (measurable_snd.sub measurable_fst)))

/-- Positive off-axis open cutoffs lie in the global domain. -/
theorem areaOpenCutoff_subset_globalDomain {δ a : ℝ} (hδ : 0 < δ) :
    areaOpenCutoff δ a ⊆ globalDomain := by
  rintro p ⟨hp, _, hgap⟩
  exact ⟨hp, by linarith only [hδ, hgap]⟩

/-- A closed cutoff is contained in a larger open cutoff. Both the gap
cutoff and the upper coordinate cutoff are changed. -/
theorem areaClosedCutoff_subset_open_enlarged {δ a : ℝ} (hδ : 0 < δ) :
    areaClosedCutoff δ a ⊆ areaOpenCutoff (δ / 2) (a + 1) := by
  rintro p ⟨hp, hpa, hgap⟩
  exact ⟨hp.1, by linarith only [hpa], by linarith only [hδ, hgap]⟩

/-- Increasing upper cutoffs and decreasing positive gap cutoffs give
an increasing family of open domains. -/
theorem areaOpenCutoff_exhaustion_monotone :
    Monotone fun n : ℕ => areaOpenCutoff (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) := by
  intro m n hmn p hp
  have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
  refine ⟨hp.1, hp.2.1.trans_le hmn', ?_⟩
  exact (one_div_le_one_div_of_le (by positivity) hmn').trans_lt hp.2.2

/-- The global domain is a countable union of open off-axis cutoffs. -/
theorem areaOpenCutoff_iUnion_eq_globalDomain :
    (⋃ n : ℕ, areaOpenCutoff (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)) =
      globalDomain := by
  apply Subset.antisymm
  · exact iUnion_subset fun _ => areaOpenCutoff_subset_globalDomain (by positivity)
  · intro p hp
    obtain ⟨m, hm⟩ := exists_nat_gt p.2
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hp.2)
    let N := max m n
    refine mem_iUnion.mpr ⟨N, hp.1, ?_, ?_⟩
    · have hmN : (m : ℝ) ≤ N := Nat.cast_le.mpr (le_max_left _ _)
      linarith only [hm, hmN]
    · exact (one_div_le_one_div_of_le (by positivity)
        (show (n : ℝ) + 1 ≤ (N : ℝ) + 1 by
          have hh : (n : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr (le_max_right m n)
          linarith only [hh])).trans_lt hn

/-- A cutoff-uniform bound on a measure gives the same global bound.
The area limit estimates supply the uniform bound from the smooth approximants. -/
theorem measure_global_le_of_areaOpenCutoff_bound (μ : Measure (ℝ × ℝ)) {B : ℝ≥0∞}
    (hB : ∀ δ a : ℝ, 0 < δ → δ < a → μ (areaOpenCutoff δ a) ≤ B) :
    μ globalDomain ≤ B := by
  rw [← areaOpenCutoff_iUnion_eq_globalDomain,
    areaOpenCutoff_exhaustion_monotone.measure_iUnion]
  apply iSup_le
  intro n
  by_cases hn : n = 0
  · subst n
    have he : areaOpenCutoff 1 1 = ∅ := by
      ext p
      simp only [areaOpenCutoff, mem_ofPred_eq,
        mem_empty_iff_false, iff_false, not_and]
      intro hp hpa hgap
      linarith only [hp, hpa, hgap]
    simp only [Nat.cast_zero, zero_add, div_one, he, measure_empty, zero_le]
  · apply hB _ _ (by positivity)
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hn' : (1 : ℝ) < (n : ℝ) + 1 := by linarith only [hnpos]
    exact ((div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr hn').trans hn'

end ChristodoulouBV

end
