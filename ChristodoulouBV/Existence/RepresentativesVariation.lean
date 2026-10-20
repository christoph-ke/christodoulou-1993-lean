module

public import ChristodoulouBV.Existence.RepresentativesCore
public import ChristodoulouBV.Existence.RepresentativesCorner
import Mathlib.Tactic

/-!
# Decay of the incoming field variations

The same chosen incoming representatives have uniformly negative ν.
Exponentiating log(-ν) controls ν variation; multiplying ν by β/ν
controls β variation. These estimates retain every point value on the
open incoming section and include the initial axis basepoint.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem variation_le_log_of_negative {f : ℝ → ℝ} {s : Set ℝ}
    (hneg : ∀ x ∈ s, f x < 0) (hb : ∀ x ∈ s, -f x ≤ 1) :
    eVariationOn f s ≤ eVariationOn (fun x => Real.log (-f x)) s := by
  have he : EqOn (-f) (Real.exp ∘ fun x => Real.log (-f x)) s := by
    intro x hx
    exact (Real.exp_log (neg_pos.mpr (hneg x hx))).symm
  calc
    _ = eVariationOn (-f) s := (eVariationOn.neg f s).symm
    _ = _ := eVariationOn.congr he
    _ ≤ ENNReal.ofReal (Real.exp 0) * eVariationOn (fun x => Real.log (-f x)) s :=
      eVariationOn.exp_comp_le (fun x hx => Real.log_nonpos
        (neg_pos.mpr (hneg x hx)).le (hb x hx))
    _ = _ := by rw [Real.exp_zero, ENNReal.ofReal_one, one_mul]

/-- The right-u ν variation tends to zero on the incoming axis segments.
This includes a = 0 and uses the final witness. -/
theorem s6_nu_axis_var
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (hsmall : D < ENNReal.ofReal epsilonChosen)
    {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun v => eVariationOn (fun u => d.incomingRightFields.nu u v)
      (Ioo a v)) (𝓝[>] a) (𝓝 0) := by
  have ht := (representatives_incoming_corner h hD d hsmall ha).2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [self_mem_nhdsWithin] with v _hv
  apply variation_le_log_of_negative
  · intro u hu
    have hn := (incoming_right_fields_geometry h hD d (u, v)
      ⟨ha.trans hu.1.le, hu.2⟩).2.2.1
    linarith only [hn]
  · intro u hu
    have hn := (incoming_right_fields_geometry h hD d (u, v)
      ⟨ha.trans hu.1.le, hu.2⟩).2.2.2.1
    exact hn.trans (by norm_num)

/-- The right-u β variation tends to zero on the same incoming axis
segments. The scalar-offset amplitude cancels
from the zero limit and all numerical coefficients are universal. -/
theorem s6_beta_axis_var
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (hsmall : D < ENNReal.ofReal epsilonChosen)
    {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun v => eVariationOn (fun u => d.incomingRightFields.beta u v)
      (Ioo a v)) (𝓝[>] a) (𝓝 0) := by
  let M := ENNReal.ofReal (12 * D.toReal + 2 * C)
  have hnu := s6_nu_axis_var h hD d hsmall ha
  have hq := (representatives_incoming_corner h hD d hsmall ha).1
  have hmul := ENNReal.Tendsto.const_mul (a := M) hnu (Or.inr ENNReal.ofReal_ne_top)
  have hsum : Tendsto (fun v => eVariationOn
      (fun u => d.scalarRightFields.beta u v / d.scalarRightFields.nu u v) (Ioo a v) +
      M * eVariationOn (fun u => d.incomingRightFields.nu u v) (Ioo a v))
      (𝓝[>] a) (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hq.add hmul
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [self_mem_nhdsWithin] with v _hv
  let S := d.incomingRightFields
  have hn (u : ℝ) (hu : u ∈ Ioo a v) : S.nu u v ≠ 0 := by
    have hh := (incoming_right_fields_geometry h hD d (u, v)
      ⟨ha.trans hu.1.le, hu.2⟩).2.2.1
    change d.incomingRightFields.nu u v ≠ 0
    linarith only [hh]
  have he : EqOn (fun u => S.beta u v)
      ((fun u => S.nu u v) * fun u => S.beta u v / S.nu u v) (Ioo a v) := by
    intro u hu
    rw [Pi.mul_apply, mul_div_cancel₀ _ (hn u hu)]
  rw [eVariationOn.congr he]
  have hprod := eVariationOn.mul_le_of_abs_le
    (f := fun u => S.nu u v) (g := fun u => S.beta u v / S.nu u v)
    (C := 1) (D := 12 * D.toReal + 2 * C) (s := Ioo a v)
    (fun u hu => by
      obtain ⟨_, _, hn0, hn1, _⟩ := incoming_right_fields_geometry h hD d (u, v)
        ⟨ha.trans hu.1.le, hu.2⟩
      change |d.incomingRightFields.nu u v| ≤ 1
      rw [abs_of_nonpos (by linarith only [hn0])]
      exact hn1.trans (by norm_num))
    (fun u hu => (bv_ratio_amplitudes h hD d (u, v) ⟨ha.trans hu.1.le, hu.2⟩).2)
  simpa only [S, M, RadiusLimitData.incomingRightFields, RadiusLimitData.scalarRightFields,
    RadiusLimitData.rightFields, ENNReal.ofReal_one, one_mul] using hprod

end ChristodoulouBV

end
