module

public import ChristodoulouBV.Existence.Representatives
public import ChristodoulouBV.BVSolution.AxisIntegrals
import Mathlib.Tactic

/-!
# Axis integrals for the final BV witness

Both orientations integrate to the same continuous primitive, whose
diagonal value is zero. The outgoing densities retain their arbitrary
point values; only the incoming densities use the final right-u representatives.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem axis_integrals_of_continuous_primitive
    {F : ℝ × ℝ → ℝ} {f g : ℝ → ℝ → ℝ}
    (hF : Continuous F) (hzero : ∀ x, 0 ≤ x → F (x, x) = 0)
    (hout : ∀ u x y, x ≤ y → outSeg u x y ⊆ globalDomain →
      IntervalPrimitive (fun t => F (u, t)) (f u) x y)
    (hin : ∀ v x y, x ≤ y → inSeg v x y ⊆ globalDomain →
      IntervalPrimitive (fun t => F (t, v)) (fun t => g t v) x y)
    {a v : ℝ} (ha : 0 ≤ a) (hav : a < v)
    (hf : BoundedVariationOn (f a) (Ioi a))
    (hg : BoundedVariationOn (fun t => g t v) (Ico 0 v)) :
    IntervalIntegrable (f a) volume a v ∧
      IntervalIntegrable (fun t => g t v) volume a v ∧
      (∫ t in a..v, f a t) = -(∫ t in a..v, g t v) := by
  have hsout {x : ℝ} (hx : x ∈ Ioc a v) : outSeg a x v ⊆ globalDomain := by
    rintro ⟨s, t⟩ ⟨rfl, ht⟩
    exact ⟨ha, hx.1.trans_le ht.1⟩
  have hsin {x : ℝ} (hx : x ∈ Ico a v) : inSeg v a x ⊆ globalDomain := by
    rintro ⟨s, t⟩ ⟨hs, rfl⟩
    exact ⟨ha.trans hs.1, hs.2.trans_lt hx.2⟩
  have hfi : IntervalIntegrable (f a) volume a v := by
    refine IsBVSolution.interval_integrable_of_bounded_left
      (M := (eVariationOn (f a) (Ioi a)).toReal + |f a v|) hav
      (add_nonneg ENNReal.toReal_nonneg (abs_nonneg (f a v)))
      (fun x hx => (hout a x v hx.2 (hsout hx)).1) ?_
    intro x hx
    have hd := hf.dist_le hx.1 hav
    rw [Real.dist_eq] at hd
    have ht := abs_add_le (f a x - f a v) (f a v)
    rw [sub_add_cancel] at ht
    exact ht.trans (add_le_add hd le_rfl)
  have hgi : IntervalIntegrable (fun t => g t v) volume a v := by
    refine IsBVSolution.interval_integrable_of_bounded_right
      (M := (eVariationOn (fun t => g t v) (Ico 0 v)).toReal + |g a v|) hav
      (add_nonneg ENNReal.toReal_nonneg (abs_nonneg (g a v)))
      (fun x hx => (hin v a x hx.1 (hsin hx)).1) ?_
    intro x hx
    have hd := hg.dist_le (show x ∈ Ico 0 v from ⟨ha.trans hx.1, hx.2⟩)
      (show a ∈ Ico 0 v from ⟨ha, hav⟩)
    rw [Real.dist_eq] at hd
    have ht := abs_add_le (g x v - g a v) (g a v)
    rw [sub_add_cancel] at ht
    exact ht.trans (add_le_add hd le_rfl)
  have hleft : Tendsto (fun t => F (a, t)) (𝓝[>] a) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => F (a, t)) :=
      hF.comp (continuous_const.prodMk continuous_id)
    have ht := hc.tendsto a
    rw [hzero a ha] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  have hright : Tendsto (fun t => F (t, v)) (𝓝[<] v) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => F (t, v)) :=
      hF.comp (continuous_id.prodMk continuous_const)
    have ht := hc.tendsto v
    rw [hzero v (ha.trans hav.le)] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  have heout := IsBVSolution.primitive_eq_integral_of_left_trace hav hfi
    (fun x hx => hout a x v hx.2.le (hsout ⟨hx.1, hx.2.le⟩)) hleft
  have hein := IsBVSolution.primitive_eq_integral_of_right_trace hav hgi
    (fun x hx => hin v a x hx.1.le (hsin ⟨hx.1.le, hx.2⟩)) hright
  exact ⟨hfi, hgi, heout.symm.trans hein⟩

/-- The final λ and ν have integrable axis sections and their signed
axis integrals agree, including when the axis basepoint is zero. -/
theorem incoming_right_fields_radius_axis_integrals
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a v : ℝ} (ha : 0 ≤ a) (hav : a < v) :
    IntervalIntegrable (d.incomingRightFields.lam a) volume a v ∧
      IntervalIntegrable (fun t => d.incomingRightFields.nu t v) volume a v ∧
      (∫ t in a..v, d.incomingRightFields.lam a t) =
        -(∫ t in a..v, d.incomingRightFields.nu t v) := by
  have hV : s4UniversalC * D ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top s4UniversalC_ne_top (ENNReal.pow_ne_top hD)
  exact axis_integrals_of_continuous_primitive d.radius_continuous
    (fun _ hx => d.radius_axis h hx)
    (radius_primitive_limit h hD d).1 (right_radius_primitive_limit h hD d).2 ha hav
    (ne_top_of_le_ne_top hV ((expansions_limit h d).1 a ha))
    (ne_top_of_le_ne_top hV
      ((right_expansions_variation h hD d).2 v (ha.trans_lt hav)))

/-- The final α and β have integrable axis sections and their signed
axis integrals agree. No right-continuity assumption is made on α. -/
theorem incoming_right_fields_scalar_axis_integrals
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a v : ℝ} (ha : 0 ≤ a) (hav : a < v) :
    IntervalIntegrable (d.incomingRightFields.alpha a) volume a v ∧
      IntervalIntegrable (fun t => d.incomingRightFields.beta t v) volume a v ∧
      (∫ t in a..v, d.incomingRightFields.alpha a t) =
        -(∫ t in a..v, d.incomingRightFields.beta t v) := by
  exact axis_integrals_of_continuous_primitive d.scalarRadius_continuous
    (fun _ hx => d.scalarRadius_axis h hx)
    (scalar_radius_primitive_limit h hD d).1
    (right_scalar_radius_primitive_limit h hD d).2 ha hav
    (ne_top_of_le_ne_top (scalarVariationBound_ne_top hD C)
      ((alpha_beta_limit h d).2.1 a ha))
    (ne_top_of_le_ne_top (scalarVariationBound_ne_top hD C)
      ((right_scalar_derivatives_variation h hD d).2 v (ha.trans_lt hav)))

end ChristodoulouBV

end
