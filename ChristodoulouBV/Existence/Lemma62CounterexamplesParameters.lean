module

public import ChristodoulouBV.Existence.Lemma62CounterexamplesTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Transverse parameters for the failed lower-semicontinuity step

Exceptional parameters `1/2 + 1/(n+4)` approach the nonexceptional parameter
`1/2`. The transition scale is `y - 1/2`. Off the exceptional set the data
are the constant multiplier one and the unit step at the left endpoint.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

attribute [local instance] Measure.Subtype.measureSpace

namespace ChristodoulouBV.Lemma62Counterexamples

/-- The nonexceptional accumulation point. -/
noncomputable def center : Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩

/-- The exceptional parameters. -/
noncomputable def parameter (n : ℕ) : Ioo (0 : ℝ) 1 :=
  ⟨1 / 2 + 1 / ((n : ℝ) + 4), by
    have hn : (4 : ℝ) ≤ (n : ℝ) + 4 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hp : 0 < 1 / ((n : ℝ) + 4) := by positivity
    have hb : 1 / ((n : ℝ) + 4) ≤ 1 / 4 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn
    constructor <;> linarith⟩

/-- The common countable exceptional set. -/
def exceptional : Set (Ioo (0 : ℝ) 1) := range parameter

theorem exceptional_countable : exceptional.Countable := countable_range _

theorem parameter_gt_center (n : ℕ) : (center : ℝ) < (parameter n : ℝ) := by
  change 1 / 2 < 1 / 2 + 1 / ((n : ℝ) + 4)
  have : 0 < 1 / ((n : ℝ) + 4) := by positivity
  linarith

theorem exceptional_gt_center {y : Ioo (0 : ℝ) 1} (hy : y ∈ exceptional) :
    (center : ℝ) < (y : ℝ) := by
  obtain ⟨n, rfl⟩ := hy
  exact parameter_gt_center n

theorem center_not_exceptional : center ∉ exceptional := by
  intro h
  exact (lt_irrefl (center : ℝ)) (exceptional_gt_center h)

theorem parameter_tendsto : Tendsto parameter atTop (𝓝 center) := by
  rw [tendsto_subtype_rng]
  have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 4)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      ((tendsto_add_atTop_iff_nat 4).2 (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
  simpa only [parameter, center, add_zero] using tendsto_const_nhds.add h

/-- The baseline step; its jump at zero is retained by `eVariationOn`. -/
noncomputable def step (x : ℝ) : ℝ := if x ≤ 0 then 0 else 1

theorem step_monotone : Monotone step := by
  intro x z hxz
  simp only [step]
  split_ifs <;> norm_num
  linarith

theorem step_measurable : Measurable step := by
  unfold step
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

theorem step_variation : eVariationOn step (Icc (0 : ℝ) 1) = 1 := by
  have h := step_monotone.monotoneOn (Icc (0 : ℝ) 1)
  have he := h.eVariationOn_eq (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  norm_num [step] at he
  exact he

/-- The limit multiplier, modified on the exceptional sections only. -/
noncomputable def movingF (y : Ioo (0 : ℝ) 1) : ℝ → ℝ := by
  classical
  exact if y ∈ exceptional then dip ((y : ℝ) - center) else fun _ => 1

/-- The limit BV function, modified on the exceptional sections only. -/
noncomputable def movingG (y : Ioo (0 : ℝ) 1) : ℝ → ℝ := by
  classical
  exact if y ∈ exceptional then rise ((y : ℝ) - center) else step

theorem movingF_smooth (y : Ioo (0 : ℝ) 1) : ContDiff ℝ 1 (movingF y) := by
  classical
  by_cases hy : y ∈ exceptional
  · simpa [movingF, hy] using dip_smooth ((y : ℝ) - center)
  · simpa [movingF, hy] using (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ)))

theorem movingG_variation_le (y : Ioo (0 : ℝ) 1) :
    eVariationOn (movingG y) (Icc (0 : ℝ) 1) ≤ 1 := by
  classical
  by_cases hy : y ∈ exceptional
  · simpa [movingG, hy] using rise_variation_le (sub_pos.mpr (exceptional_gt_center hy))
  · simp [movingG, hy, step_variation]

/-- At zero the values and multiplier derivatives are independent of the parameter. -/
theorem moving_at_zero (y : Ioo (0 : ℝ) 1) :
    movingF y 0 = 1 ∧ deriv (movingF y) 0 = 0 ∧ movingG y 0 = 0 := by
  classical
  by_cases hy : y ∈ exceptional
  · have hs := sub_pos.mpr (exceptional_gt_center hy)
    simp only [movingF, movingG, ite_eq_left hy]
    exact ⟨dip_eq_one_left hs (by linarith),
      dip_deriv_left hs (by linarith), rise_eq_zero hs (by linarith)⟩
  · simp [movingF, movingG, hy, step]

private theorem eventually_not_exceptional {y : Ioo (0 : ℝ) 1}
    (hy : y ∉ exceptional) (hy0 : y ≠ center) : ∀ᶠ z in 𝓝 y, z ∉ exceptional := by
  have hc := parameter_tendsto.isCompact_insert_range.isClosed
  have hm : y ∈ (insert center exceptional)ᶜ := by simp [hy, hy0]
  have he : ∀ᶠ z in 𝓝 y, z ∈ (insert center exceptional)ᶜ := hc.isOpen_compl.mem_nhds hm
  exact he.mono fun z hz => fun h => hz (mem_insert_of_mem _ h)

private theorem eventually_baseline {x : ℝ} (hx : 0 < x) :
    ∀ᶠ z in 𝓝 center,
      movingF z x = 1 ∧ deriv (movingF z) x = 0 ∧ movingG z x = 1 := by
  classical
  have he : ∀ᶠ z : Ioo (0 : ℝ) 1 in 𝓝 center, (z : ℝ) < (center : ℝ) + x / 3 :=
    continuousAt_subtype_val.eventually (gt_mem_nhds (by linarith))
  filter_upwards [he] with z hz
  by_cases hzS : z ∈ exceptional
  · have hs := sub_pos.mpr (exceptional_gt_center hzS)
    have hsmall : 3 * ((z : ℝ) - center) < x := by linarith
    simp only [movingF, movingG, ite_eq_left hzS]
    exact ⟨dip_eq_one_right hs hsmall, dip_deriv_right hs hsmall,
      rise_eq_one hs (by linarith)⟩
  · simp [movingF, movingG, hzS, step, not_le.mpr hx]

/-- All four transverse continuity premises, with continuity through the exceptional
sections at the accumulation point. -/
theorem moving_continuity (y : Ioo (0 : ℝ) 1) (hy : y ∉ exceptional)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (fun z => movingF z x) y ∧
    ContinuousAt (fun z => deriv (movingF z) x) y ∧
    ContinuousAt (fun z => movingG z x) y := by
  classical
  by_cases hzero : x = 0
  · subst x
    have hf : (fun z => movingF z 0) = fun _ => (1 : ℝ) := funext fun z => (moving_at_zero z).1
    have hp : (fun z => deriv (movingF z) 0) = fun _ => (0 : ℝ) :=
      funext fun z => (moving_at_zero z).2.1
    have hg : (fun z => movingG z 0) = fun _ => (0 : ℝ) :=
      funext fun z => (moving_at_zero z).2.2
    simp [hf, hp, hg, continuousAt_const]
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hzero)
  by_cases hy0 : y = center
  · subst y
    have he := eventually_baseline hxpos
    exact ⟨continuousAt_const.congr_of_eventuallyEq (he.mono fun _ h => h.1),
      continuousAt_const.congr_of_eventuallyEq (he.mono fun _ h => h.2.1),
      continuousAt_const.congr_of_eventuallyEq (he.mono fun _ h => h.2.2)⟩
  · have he := eventually_not_exceptional hy hy0
    refine ⟨(continuousAt_const (y := (1 : ℝ))).congr_of_eventuallyEq ?_,
      (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq ?_,
      (continuousAt_const (y := step x)).congr_of_eventuallyEq ?_⟩
    · exact he.mono fun z hz => by simp [movingF, hz]
    · exact he.mono fun z hz => by simp [movingF, hz]
    · exact he.mono fun z hz => by simp [movingG, hz]

end ChristodoulouBV.Lemma62Counterexamples
