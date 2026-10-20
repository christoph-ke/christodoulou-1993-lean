module

public import ChristodoulouBV.Existence.Lemma62CounterexamplesSine
import Mathlib.Analysis.SpecificLimits.Basic
import ChristodoulouBV.ForMathlib.BoundedVariation.Algebra

/-!
# Failure of the printed L¹ conclusion of Lemma 6.2

We use `fₙ = f = 1`, `hₙ = h = 0`, `S = ∅`, and
`gₙ(y,x) = sin (4*x/max(y,1/(n+1)))`, `g(y,x) = sin (4*x/y)`.
All the premises of the established lower-integral lemma are retained verbatim
in `Lemma62Hypotheses`. The variation of the limit is at least `1/y`.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

attribute [local instance] Measure.Subtype.measureSpace

namespace ChristodoulouBV.Lemma62Counterexamples

/-- The frequency cutoff in the approximating sections. -/
noncomputable def cutoff (n : ℕ) (y : Ioo (0 : ℝ) 1) : ℝ :=
  max (y : ℝ) (1 / ((n : ℝ) + 1))

/-- Limit section for the first counterexample. -/
noncomputable def oscillation (y : Ioo (0 : ℝ) 1) : ℝ → ℝ := sine y

/-- Approximating sections for the first counterexample. -/
noncomputable def oscillationSeq (n : ℕ) (y : Ioo (0 : ℝ) 1) : ℝ → ℝ :=
  sine (cutoff n y)

theorem primitive_one_zero (g : ℝ → ℝ) :
    intervalIntegral.productPrimitive (fun _ => (1 : ℝ)) g
      (deriv (fun _ => (1 : ℝ))) (fun _ => 0) = fun x => g x - g 0 := by
  funext x
  simp [intervalIntegral.productPrimitive]

theorem variation_primitive_one_zero (g : ℝ → ℝ) :
    eVariationOn (intervalIntegral.productPrimitive (fun _ => (1 : ℝ)) g
      (deriv (fun _ => (1 : ℝ))) (fun _ => 0)) (Icc (0 : ℝ) 1) =
      eVariationOn g (Icc (0 : ℝ) 1) := by
  rw [primitive_one_zero]
  simpa only [sub_eq_add_neg] using eVariationOn.add_const g (-g 0) (Icc (0 : ℝ) 1)

theorem cutoff_pos (n : ℕ) (y : Ioo (0 : ℝ) 1) : 0 < cutoff n y :=
  lt_of_lt_of_le y.property.1 (le_max_left _ _)

theorem oscillationSeq_measurable (n : ℕ) :
    Measurable (fun y => eVariationOn (oscillationSeq n y) (Icc (0 : ℝ) 1)) := by
  apply eVariationOn.measurable_of_countable_noncontinuous_sections (S := ∅) (by simp)
  intro y _ x _
  change ContinuousAt (fun z : Ioo (0 : ℝ) 1 =>
    Real.sin (4 * x / max (z : ℝ) (1 / ((n : ℝ) + 1)))) y
  exact (Real.continuous_sin.continuousAt.comp
    (continuousAt_const.div (continuousAt_subtype_val.max continuousAt_const)
      (ne_of_gt (cutoff_pos n y))))

theorem oscillationSeq_eventually (y : Ioo (0 : ℝ) 1) :
    ∀ᶠ n : ℕ in atTop, oscillationSeq n y = oscillation y := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds y.property.1)
  filter_upwards [h] with n hn
  change sine (max (y : ℝ) (1 / ((n : ℝ) + 1))) = sine y
  rw [max_eq_left hn.le]

/-- Every premise of `lemma6_2_lintegral` for the oscillatory construction. -/
theorem oscillation_hypotheses :
    Lemma62Hypotheses (fun _ _ _ => 1) oscillationSeq (fun _ _ _ => 0)
      (fun _ _ => 1) oscillation (fun _ _ => 0) ∅ := by
  refine {
    hS := by simp
    hfₙ_diff := fun _ _ _ _ => differentiableAt_const 1
    hf_diff := fun _ _ _ => differentiableAt_const 1
    hf_lim := fun _ _ _ => tendsto_const_nhds
    hf_deriv_lim := fun _ _ _ => tendsto_const_nhds
    hf_deriv_bound := ?_
    hg_var := ?_
    hg_lim := ?_
    hhₙ_meas := fun _ _ => measurable_const
    hhₙ_bound := ?_
    hh_lim := fun _ _ _ => tendsto_const_nhds
    hFₙ_ae := ?_
    hFₙ_finite := ?_
    hf_Linf := memLp_top_const 1
    hf_deriv_Linf := ?_
    hg_Linf := ?_
    hh_Linf := memLp_top_const 0
    hf_cont := fun _ _ _ _ => continuousAt_const
    hf_deriv_cont := ?_
    hg_cont := ?_
    hh_cont := fun _ _ _ _ => continuousAt_const }
  · intro y
    exact ⟨0, le_rfl, fun _ => Filter.Eventually.of_forall (by simp)⟩
  · intro y
    refine ⟨ENNReal.ofReal (4 / (y : ℝ)), ENNReal.ofReal_ne_top, fun n => ?_⟩
    exact (sine_variation_le (cutoff_pos n y)).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (by norm_num)
        y.property.1 (le_max_left _ _)))
  · intro y x _
    apply tendsto_const_nhds.congr'
    filter_upwards [oscillationSeq_eventually y] with n hn
    exact congrFun hn x |>.symm
  · intro y
    exact ⟨0, le_rfl, fun _ => Filter.Eventually.of_forall (by simp)⟩
  · intro n
    simpa only [variation_primitive_one_zero] using (oscillationSeq_measurable n).aemeasurable
  · intro n
    apply ne_top_of_le_ne_top
      (lintegral_const_lt_top (μ := (volume : Measure (Ioo (0 : ℝ) 1)))
        (c := ENNReal.ofReal (4 * ((n : ℝ) + 1))) ENNReal.ofReal_ne_top).ne
    apply lintegral_mono
    intro y
    dsimp only
    rw [variation_primitive_one_zero]
    refine (sine_variation_le (cutoff_pos n y)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hc : 1 / ((n : ℝ) + 1) ≤ cutoff n y := le_max_right _ _
    calc
      4 / cutoff n y ≤ 4 / (1 / ((n : ℝ) + 1)) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hc
      _ = 4 * ((n : ℝ) + 1) := by field_simp
  · simpa only [deriv_const] using
      (memLp_top_const (μ := (volume : Measure (Icc (0 : ℝ) 1 × Ioo (0 : ℝ) 1))) (0 : ℝ))
  · apply memLp_top_of_bound (C := 1)
    · apply Measurable.aestronglyMeasurable
      change Measurable (fun p : Icc (0 : ℝ) 1 × Ioo (0 : ℝ) 1 =>
        Real.sin (4 * (p.1 : ℝ) / (p.2 : ℝ)))
      fun_prop
    · exact Filter.Eventually.of_forall fun p => by
        simpa [oscillation, sine, Real.norm_eq_abs] using
          Real.abs_sin_le_one (4 * (p.1 : ℝ) / (p.2 : ℝ))
  · intro y _ x _
    simpa only [deriv_const] using
      (continuousAt_const : ContinuousAt (fun _ : Ioo (0 : ℝ) 1 => (0 : ℝ)) y)
  · intro y _ x _
    change ContinuousAt (fun z : Ioo (0 : ℝ) 1 => Real.sin (4 * x / (z : ℝ))) y
    exact Real.continuous_sin.continuousAt.comp
      (continuousAt_const.div continuousAt_subtype_val (ne_of_gt y.property.1))

end ChristodoulouBV.Lemma62Counterexamples

namespace ChristodoulouBV

/-- The printed conclusion `F ∈ L¹(0,1)` is false, even with `S = ∅` and
jointly continuous bounded limit data. The nonnegative section functional
has infinite lower Lebesgue integral. -/
theorem lemma6_2_L1_conclusion_false :
    ∃ (fₙ gₙ hₙ : ℕ → Ioo (0 : ℝ) 1 → ℝ → ℝ)
      (f g h : Ioo (0 : ℝ) 1 → ℝ → ℝ) (S : Set (Ioo (0 : ℝ) 1)),
      Lemma62Hypotheses fₙ gₙ hₙ f g h S ∧
      (∫⁻ y : Ioo (0 : ℝ) 1, lemma62Functional f g h y) = ∞ := by
  refine ⟨_, _, _, _, _, _, _, Lemma62Counterexamples.oscillation_hypotheses, ?_⟩
  apply top_unique
  rw [← Lemma62Counterexamples.lintegral_inv_top]
  apply lintegral_mono
  intro y
  rw [lemma62Functional, Lemma62Counterexamples.variation_primitive_one_zero]
  exact Lemma62Counterexamples.sine_variation_ge y.property.1 y.property.2

end ChristodoulouBV
