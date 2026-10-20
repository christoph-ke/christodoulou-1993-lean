module

public import ChristodoulouBV.Existence.GlobalBVAxisIntegrals
import Mathlib.Tactic

/-!
# Pointwise axis cancellation for the final BV witness

The signed outgoing and incoming integrals agree. Their errors from the
endpoint values are bounded by the outgoing and incoming variations.
Outgoing BV gives a shrinking half-open tail even for arbitrary values
of α; right continuity of ν and β removes the incoming endpoint cost.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem axis_pair_bound {f g : ℝ → ℝ} {a v : ℝ} (hav : a < v)
    (hf : BoundedVariationOn f (Ioc a v))
    (hg : BoundedVariationOn g (Ico a v))
    (hfi : IntervalIntegrable f volume a v) (hgi : IntervalIntegrable g volume a v)
    (hbalance : (∫ t in a..v, f t) = -(∫ t in a..v, g t)) :
    |f v + g a| ≤ (eVariationOn f (Ioc a v)).toReal +
      (eVariationOn g (Ico a v)).toReal := by
  have hfb : |∫ t in a..v, f v - f t| ≤
      (eVariationOn f (Ioc a v)).toReal * (v - a) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := v) (f := fun t => f v - f t) (C := (eVariationOn f (Ioc a v)).toReal)
      (fun t ht => by
        rw [uIoc_of_le hav.le] at ht
        simpa only [Real.norm_eq_abs, Real.dist_eq] using hf.dist_le ⟨hav, le_rfl⟩ ht)
    simpa only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hav)] using hb
  have hgb : |∫ t in a..v, g a - g t| ≤
      (eVariationOn g (Ico a v)).toReal * (v - a) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (a := a) (b := v) (f := fun t => g a - g t) (C := (eVariationOn g (Ico a v)).toReal)
      (by
        filter_upwards [Measure.ae_ne volume v] with t hne ht
        rw [uIoc_of_le hav.le] at ht
        simpa only [Real.norm_eq_abs, Real.dist_eq] using
          hg.dist_le ⟨le_rfl, hav⟩ ⟨ht.1.le, lt_of_le_of_ne ht.2 hne⟩)
    simpa only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hav)] using hb
  have he : (f v + g a) * (v - a) =
      (∫ t in a..v, f v - f t) + (∫ t in a..v, g a - g t) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hfi,
      intervalIntegral.integral_sub intervalIntegrable_const hgi,
      intervalIntegral.integral_const, intervalIntegral.integral_const, hbalance]
    simp only [smul_eq_mul]
    ring
  have hb : |f v + g a| * (v - a) ≤
      ((eVariationOn f (Ioc a v)).toReal + (eVariationOn g (Ico a v)).toReal) *
        (v - a) := by
    calc
      _ = |(f v + g a) * (v - a)| := by
        rw [abs_mul, abs_of_pos (sub_pos.mpr hav)]
      _ ≤ _ := by
        rw [he, add_mul]
        exact (abs_add_le _ _).trans (add_le_add hfb hgb)
  exact (mul_le_mul_iff_left₀ (sub_pos.mpr hav)).mp hb

private theorem axis_pair_tendsto {f g : ℝ → ℝ → ℝ} {a : ℝ}
    (hf : BoundedVariationOn (f a) (Ioi a))
    (hg : ∀ v, a < v → BoundedVariationOn (fun t => g t v) (Ico a v))
    (hright : ∀ v, a < v → ContinuousWithinAt (fun t => g t v) (Ici a) a)
    (hints : ∀ v, a < v →
      IntervalIntegrable (f a) volume a v ∧
      IntervalIntegrable (fun t => g t v) volume a v ∧
      (∫ t in a..v, f a t) = -(∫ t in a..v, g t v))
    (hvar : Tendsto (fun v => eVariationOn (fun t => g t v) (Ioo a v))
      (𝓝[>] a) (𝓝 0)) :
    Tendsto (fun v => f a v + g a v) (𝓝[>] a) (𝓝 0) := by
  have htail : Tendsto (fun v => eVariationOn (f a) (Ioc a v))
      (𝓝[>] a) (𝓝 0) := by
    simpa only [inter_eq_right.mpr Ioc_subset_Ioi_self] using
      hf.tendsto_eVariationOn_Ioc_zero a
  have hout : Tendsto (fun v => (eVariationOn (f a) (Ioc a v)).toReal)
      (𝓝[>] a) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htail
  have hin : Tendsto (fun v => (eVariationOn (fun t => g t v) (Ioo a v)).toReal)
      (𝓝[>] a) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hvar
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_
    (by simpa only [add_zero] using hout.add hin)
  filter_upwards [self_mem_nhdsWithin] with v hv
  obtain ⟨hfi, hgi, he⟩ := hints v hv
  have hb := axis_pair_bound hv (hf.mono Ioc_subset_Ioi_self) (hg v hv) hfi hgi he
  rwa [eVariationOn.Ico_eq_Ioo_of_continuousWithinAt hv (hright v hv)] at hb

/-- Frozen BV item 2 for the final right-representative witness. The pointwise expansion
sum vanishes at every adjacent axis point, including the origin. -/
theorem s6_bv_item2
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (hsmall : D < ENNReal.ofReal epsilonChosen) :
    ∀ a ∈ adjacentAxis globalDomain,
      Tendsto (fun v => d.incomingRightFields.nu a v + d.incomingRightFields.lam a v)
        (nhdsWithin a (Ioi a) ⊓ principal {v | (a, v) ∈ globalDomain}) (𝓝 0) := by
  intro a ha
  have ha0 : 0 ≤ a := by
    have hcl : (a, a) ∈ closure globalDomain := ha
    rw [s6_closure_globalDomain] at hcl
    exact hcl.1
  have hV : s4UniversalC * D ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top s4UniversalC_ne_top (ENNReal.pow_ne_top hD)
  have ht := axis_pair_tendsto
    (f := d.incomingRightFields.lam) (g := d.incomingRightFields.nu)
    (ne_top_of_le_ne_top hV ((expansions_limit h d).1 a ha0))
    (fun v hv => (show BoundedVariationOn (fun t => d.rightNu t v) (Ico 0 v) from
      ne_top_of_le_ne_top hV
        ((right_expansions_variation h hD d).2 v (ha0.trans_lt hv))).mono
      (Ico_subset_Ico_left ha0))
    (fun v hv => (nu_right_rep h hD d (a, v) ⟨ha0, hv⟩).2)
    (fun _ hv => incoming_right_fields_radius_axis_integrals h hD d ha0 hv)
    (s6_nu_axis_var h hD d hsmall ha0)
  have ht' : Tendsto
      (fun v => d.incomingRightFields.nu a v + d.incomingRightFields.lam a v)
      (𝓝[>] a) (𝓝 0) := by simpa only [add_comm] using ht
  exact ht'.mono_left inf_le_left

/-- Frozen BV item 6 for the same witness and arbitrary outgoing α
values. This corrects the printed reference to “condition 4” (ERR-33). -/
theorem s6_bv_item6
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (hsmall : D < ENNReal.ofReal epsilonChosen) :
    ∀ a ∈ adjacentAxis globalDomain,
      Tendsto (fun v => d.incomingRightFields.alpha a v + d.incomingRightFields.beta a v)
        (nhdsWithin a (Ioi a) ⊓ principal {v | (a, v) ∈ globalDomain}) (𝓝 0) := by
  intro a ha
  have ha0 : 0 ≤ a := by
    have hcl : (a, a) ∈ closure globalDomain := ha
    rw [s6_closure_globalDomain] at hcl
    exact hcl.1
  have ht := axis_pair_tendsto
    (f := d.incomingRightFields.alpha) (g := d.incomingRightFields.beta)
    (ne_top_of_le_ne_top (scalarVariationBound_ne_top hD C)
      ((alpha_beta_limit h d).2.1 a ha0))
    (fun v hv => (show BoundedVariationOn (fun t => d.rightBeta t v) (Ico 0 v) from
      ne_top_of_le_ne_top (scalarVariationBound_ne_top hD C)
        ((right_scalar_derivatives_variation h hD d).2 v (ha0.trans_lt hv))).mono
      (Ico_subset_Ico_left ha0))
    (fun v hv => (beta_right_rep h hD d (a, v) ⟨ha0, hv⟩).2)
    (fun _ hv => incoming_right_fields_scalar_axis_integrals h hD d ha0 hv)
    (s6_beta_axis_var h hD d hsmall ha0)
  exact ht.mono_left inf_le_left

end ChristodoulouBV

end
