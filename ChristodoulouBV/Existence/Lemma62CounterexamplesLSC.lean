module

public import ChristodoulouBV.Existence.Lemma62CounterexamplesParameters
public import ChristodoulouBV.Existence.Lemma62CounterexamplesL1

/-!
# Failure of the printed lower-semicontinuity proof step

Constant approximating sequences suffice. The rectangle bounds hold because
the limit data equal bounded baseline functions outside countably many
transverse sections. On each exceptional section the smooth multiplier
vanishes where the smooth BV function changes, so its weighted variation
is zero. At the nonexceptional accumulation point it is one.

The sketch is adjusted only by putting the limiting jump at the left
endpoint of the closed interval. The carrier deliberately retains that
jump; none of the hypotheses is changed.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

attribute [local instance] Measure.Subtype.measureSpace Classical.propDecidable

namespace ChristodoulouBV.Lemma62Counterexamples

/-- The section functional is zero on the exceptional set and one elsewhere. -/
theorem moving_functional (y : Ioo (0 : ℝ) 1) :
    lemma62Functional movingF movingG (fun _ _ => 0) y =
      if y ∈ exceptional then 0 else 1 := by
  classical
  by_cases hy : y ∈ exceptional
  · have hs := sub_pos.mpr (exceptional_gt_center hy)
    simp only [lemma62Functional, movingF, movingG, ite_eq_left hy]
    rw [dip_primitive_zero hs]
    exact (eVariationOn.eq_zero_iff _).2 (by intros; exact edist_self _)
  · simp only [lemma62Functional, movingF, movingG, ite_eq_right hy]
    rw [variation_primitive_one_zero, step_variation]

/-- In this example the section functional is measurable despite failing
lower semicontinuity at the center. -/
theorem moving_functional_measurable :
    Measurable (lemma62Functional movingF movingG (fun _ _ => 0)) := by
  classical
  have he : lemma62Functional movingF movingG (fun _ _ => 0) =
      fun y => if y ∈ exceptional then (0 : ℝ≥0∞) else 1 := funext moving_functional
  rw [he]
  exact Measurable.ite exceptional_countable.measurableSet measurable_const measurable_const

private theorem ae_outside_exceptional :
    ∀ᵐ p : Icc (0 : ℝ) 1 × Ioo (0 : ℝ) 1 ∂volume, p.2 ∉ exceptional := by
  have hnull : (volume : Measure (Ioo (0 : ℝ) 1)) exceptional = 0 := by
    rw [← volume_image_subtype_coe measurableSet_Ioo]
    exact (exceptional_countable.image Subtype.val).measure_zero volume
  have he : ∀ᵐ y : Ioo (0 : ℝ) 1 ∂volume, y ∉ exceptional :=
    ae_iff.mpr (by simpa using hnull)
  exact Measure.quasiMeasurePreserving_snd.ae he

/-- Every printed premise holds, with constant approximating sequences. -/
theorem moving_hypotheses :
    Lemma62Hypotheses (fun _ => movingF) (fun _ => movingG) (fun _ _ _ => 0)
      movingF movingG (fun _ _ => 0) exceptional := by
  classical
  have hf_Linf : MemLp
      (fun p : Icc (0 : ℝ) 1 × Ioo (0 : ℝ) 1 => movingF p.2 p.1) ∞ volume := by
    apply (memLp_congr_ae (g := fun _ => (1 : ℝ)) ?_).2 (memLp_top_const 1)
    filter_upwards [ae_outside_exceptional] with p hp
    simp [movingF, hp]
  have hp_Linf : MemLp
      (fun p : Icc (0 : ℝ) 1 × Ioo (0 : ℝ) 1 => deriv (movingF p.2) p.1) ∞ volume := by
    apply (memLp_congr_ae (g := fun _ => (0 : ℝ)) ?_).2 (memLp_top_const 0)
    filter_upwards [ae_outside_exceptional] with p hp
    simp [movingF, hp]
  have hg_Linf : MemLp
      (fun p : Icc (0 : ℝ) 1 × Ioo (0 : ℝ) 1 => movingG p.2 p.1) ∞ volume := by
    have hb : MemLp (fun p : Icc (0 : ℝ) 1 × Ioo (0 : ℝ) 1 => step p.1) ∞ volume := by
      apply memLp_top_of_bound
        (step_measurable.comp (measurable_subtype_coe.comp measurable_fst)).aestronglyMeasurable 1
      exact Filter.Eventually.of_forall fun p => by
        change |step (p.1 : ℝ)| ≤ 1
        simp only [step]
        split_ifs <;> norm_num
    apply (memLp_congr_ae (g := fun p => step p.1) ?_).2 hb
    filter_upwards [ae_outside_exceptional] with p hp
    simp [movingG, hp]
  refine {
    hS := exceptional_countable
    hfₙ_diff := fun _ y x _ => (movingF_smooth y).differentiable (by norm_num) x
    hf_diff := fun y x _ => (movingF_smooth y).differentiable (by norm_num) x
    hf_lim := fun _ _ _ => tendsto_const_nhds
    hf_deriv_lim := fun _ _ _ => tendsto_const_nhds
    hf_deriv_bound := ?_
    hg_var := fun y => ⟨1, by norm_num, fun _ => movingG_variation_le y⟩
    hg_lim := fun _ _ _ => tendsto_const_nhds
    hhₙ_meas := fun _ _ => measurable_const
    hhₙ_bound := fun _ => ⟨0, le_rfl, fun _ => Filter.Eventually.of_forall (by simp)⟩
    hh_lim := fun _ _ _ => tendsto_const_nhds
    hFₙ_ae := fun _ => moving_functional_measurable.aemeasurable
    hFₙ_finite := ?_
    hf_Linf := hf_Linf
    hf_deriv_Linf := hp_Linf
    hg_Linf := hg_Linf
    hh_Linf := memLp_top_const 0
    hf_cont := fun y hy x hx => (moving_continuity y hy x hx).1
    hf_deriv_cont := fun y hy x hx => (moving_continuity y hy x hx).2.1
    hg_cont := fun y hy x hx => (moving_continuity y hy x hx).2.2
    hh_cont := fun _ _ _ _ => continuousAt_const }
  · intro y
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((movingF_smooth y).continuous_deriv (by norm_num)).continuousOn
    refine ⟨max C 0, le_max_right _ _, fun _ => Filter.Eventually.of_forall ?_⟩
    intro x hx
    have hc : |deriv (movingF y) x| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC x hx
    exact hc.trans (le_max_left _ _)
  · intro n
    apply ne_top_of_le_ne_top
      (lintegral_const_lt_top (μ := (volume : Measure (Ioo (0 : ℝ) 1)))
        (c := 1) (by norm_num)).ne
    apply lintegral_mono
    intro y
    change lemma62Functional movingF movingG (fun _ _ => 0) y ≤ 1
    rw [moving_functional]
    split_ifs <;> norm_num

theorem moving_functional_center :
    lemma62Functional movingF movingG (fun _ _ => 0) center = 1 := by
  rw [moving_functional, ite_eq_right center_not_exceptional]

theorem moving_functional_parameter (n : ℕ) :
    lemma62Functional movingF movingG (fun _ _ => 0) (parameter n) = 0 := by
  rw [moving_functional, ite_eq_left
    (show parameter n ∈ exceptional from mem_range_self n)]

theorem moving_not_lowerSemicontinuous :
    ¬ LowerSemicontinuousAt (lemma62Functional movingF movingG (fun _ _ => 0)) center := by
  intro h
  have hpos : (0 : ℝ≥0∞) < lemma62Functional movingF movingG (fun _ _ => 0) center := by
    rw [moving_functional_center]
    norm_num
  have he := parameter_tendsto.eventually (h 0 hpos)
  obtain ⟨n, hn⟩ := he.exists
  simp only [moving_functional_parameter, lt_self_iff_false] at hn

end ChristodoulouBV.Lemma62Counterexamples

namespace ChristodoulouBV

/-- The printed proof step asserting lower semicontinuity at every `y₀ ∉ S`
is false. All printed hypotheses hold; exceptional parameters approach a
nonexceptional point, with functional values zero along the sequence and
one at its limit. -/
theorem lemma6_2_lsc_step_false :
    ∃ (fₙ gₙ hₙ : ℕ → Ioo (0 : ℝ) 1 → ℝ → ℝ)
      (f g h : Ioo (0 : ℝ) 1 → ℝ → ℝ) (S : Set (Ioo (0 : ℝ) 1))
      (y₀ : Ioo (0 : ℝ) 1) (yₙ : ℕ → Ioo (0 : ℝ) 1),
      Lemma62Hypotheses fₙ gₙ hₙ f g h S ∧ y₀ ∉ S ∧
      (∀ n, yₙ n ∈ S) ∧ Tendsto yₙ atTop (𝓝 y₀) ∧
      (∀ n, lemma62Functional f g h (yₙ n) = 0) ∧
      lemma62Functional f g h y₀ = 1 ∧
      ¬ LowerSemicontinuousAt (lemma62Functional f g h) y₀ := by
  exact ⟨_, _, _, _, _, _, _, _, _, Lemma62Counterexamples.moving_hypotheses,
    Lemma62Counterexamples.center_not_exceptional, fun n => mem_range_self n,
    Lemma62Counterexamples.parameter_tendsto, Lemma62Counterexamples.moving_functional_parameter,
    Lemma62Counterexamples.moving_functional_center,
    Lemma62Counterexamples.moving_not_lowerSemicontinuous⟩

end ChristodoulouBV
