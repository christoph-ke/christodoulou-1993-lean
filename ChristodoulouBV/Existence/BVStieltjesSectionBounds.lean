module

public import ChristodoulouBV.Existence.BVStieltjesDerivative
public import ChristodoulouBV.Existence.BVStieltjesQuotient
public import ChristodoulouBV.Existence.BVStieltjesOutgoing
import Mathlib.Tactic

/-!
# Uniform section bounds for the residual absorption

All constants below are universal. The deliberately generous numerical
budget fits the already fixed threshold `epsilonChosen = 10⁻⁸⁰`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Both normalized scalar ratios and both logarithms have finite
variation on every axis-based open characteristic section. -/
theorem bv_corner_variations_finite
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u b : ℝ, 0 ≤ u →
      BoundedVariationOn (fun t => d.scalarRightFields.alpha u t /
        d.scalarRightFields.lam u t) (Ioo u b) ∧
      BoundedVariationOn (fun t => Real.log (d.scalarRightFields.lam u t)) (Ioo u b)) ∧
    (∀ a v : ℝ, 0 ≤ a → a < v →
      BoundedVariationOn (fun t => d.scalarRightFields.beta t v /
        d.scalarRightFields.nu t v) (Ioo a v) ∧
      BoundedVariationOn (fun t => Real.log (-d.scalarRightFields.nu t v)) (Ioo a v)) := by
  have hfin : 3 * ENNReal.ofReal (s6EndpointTVK * D.toReal) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  constructor
  · intro u b hu
    have hb := (scalar_right_fields_three_term_tv h hD d).1 u hu
    change _ + _ + _ ≤ _ at hb
    constructor
    · exact ne_top_of_le_ne_top hfin ((eVariationOn.mono _ Ioo_subset_Ioi_self).trans
        ((le_add_of_nonneg_right bot_le).trans
          ((le_add_of_nonneg_right bot_le).trans hb)))
    · exact ne_top_of_le_ne_top hfin ((eVariationOn.mono _ Ioo_subset_Ioi_self).trans
        ((le_add_of_nonneg_left bot_le).trans hb))
  · intro a v ha hav
    have hb := (scalar_right_fields_three_term_tv h hD d).2 v (ha.trans_lt hav)
    change _ + _ + _ ≤ _ at hb
    have hs : Ioo a v ⊆ Ioo 0 v := fun _ ht => ⟨ha.trans_lt ht.1, ht.2⟩
    constructor
    · exact ne_top_of_le_ne_top hfin ((eVariationOn.mono _ hs).trans
        ((le_add_of_nonneg_right bot_le).trans
          ((le_add_of_nonneg_right bot_le).trans hb)))
    · exact ne_top_of_le_ne_top hfin ((eVariationOn.mono _ hs).trans
        ((le_add_of_nonneg_left bot_le).trans hb))

/-- One generous universal real budget bounds both open scalar variations. -/
theorem bv_open_scalar_variation_budget
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    (∀ u b : ℝ, 0 ≤ u → (eVariationOn (d.scalarRightFields.phi u) (Ioo u b)).toReal ≤
      10 ^ (64 : ℕ) * D.toReal) ∧
    (∀ a v : ℝ, 0 ≤ a → a < v →
      (eVariationOn (fun t => d.scalarRightFields.phi t v) (Ioo a v)).toReal ≤
        10 ^ (64 : ℕ) * D.toReal) := by
  have hK : 3 * s6EndpointTVK ≤ (10 : ℝ) ^ (64 : ℕ) := by
    norm_num [s6EndpointTVK_eq, s4SliceTVK_eq]
  have hD0 := ENNReal.toReal_nonneg (a := D)
  have hbound {V : ℝ≥0∞} (hV : V ≤ ENNReal.ofReal (3 * s6EndpointTVK * D.toReal)) :
      V.toReal ≤ 10 ^ (64 : ℕ) * D.toReal := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hV
    rw [ENNReal.toReal_ofReal (mul_nonneg
      (mul_nonneg (by norm_num) s6EndpointTVK_pos.le) hD0)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hK hD0)
  constructor
  · intro u b hu
    exact hbound ((eVariationOn.mono _ Ioo_subset_Ioi_self).trans
      ((bv_scalar_variation h hD d).1 u hu))
  · intro a v ha hav
    exact hbound ((eVariationOn.mono _ (fun t ht =>
      show t ∈ Ico 0 v from ⟨ha.trans ht.1.le, ht.2⟩)).trans
        ((bv_scalar_variation h hD d).2 v (ha.trans_lt hav)))

private theorem expansion_variation_le_log {L : ℝ → ℝ} {s : Set ℝ}
    (hL0 : ∀ t ∈ s, 0 < L t) (hL1 : ∀ t ∈ s, L t ≤ 1) :
    eVariationOn L s ≤ eVariationOn (fun t => Real.log (L t)) s := by
  have he : EqOn L (Real.exp ∘ fun t => Real.log (L t)) s := by
    intro t ht
    exact (Real.exp_log (hL0 t ht)).symm
  rw [eVariationOn.eq_of_eqOn he]
  have hh := eVariationOn.exp_comp_le (g := fun t => Real.log (L t)) (K := 0)
    (fun t ht => Real.log_nonpos (hL0 t ht).le (hL1 t ht))
  simpa only [Real.exp_zero, ENNReal.ofReal_one, one_mul] using hh

/-- Outgoing quotient variation is controlled by its scalar residual
and the logarithmic expansion variation, including every expansion jump. -/
theorem bv_outgoing_quotient_residual_bound
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u a : ℝ} (hu : 0 ≤ u) (hua : u < a) :
    eVariationOn (fun t => d.scalarRightFields.alpha u t / d.scalarRightFields.lam u t)
        (Ioo u a) ≤
      3 * eVariationOn (bvOutgoingScalarResidual d.scalarRightFields u a) (Ioo u a) +
        ENNReal.ofReal (10 ^ (65 : ℕ) * D.toReal) *
          eVariationOn (fun t => Real.log (d.scalarRightFields.lam u t)) (Ioo u a) := by
  let S := d.scalarRightFields
  have hL (t : ℝ) (ht : t ∈ Ioo u a) : (1 / 3 : ℝ) ≤ S.lam u t :=
    (scalar_right_fields_geometry h hD d (u, t) ⟨hu, ht.1⟩).1
  have hLBV : BoundedVariationOn (S.lam u) (Ioo u a) :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top s4UniversalC_ne_top (ENNReal.pow_ne_top hD))
      ((eVariationOn.mono _ Ioo_subset_Ioi_self).trans
        ((right_expansions_variation h hD d).1 u hu))
  have hs (x y : ℝ) (hx : x ∈ Ioo u a) (hy : y ∈ Ioo u a) :
      outSeg u x y ⊆ globalDomain := by
    rintro ⟨s, t⟩ ⟨rfl, ht⟩
    exact ⟨hu, hx.1.trans_le ht.1⟩
  have hp (x : ℝ) (hx : x ∈ Ioo u a) (y : ℝ) (hy : y ∈ Ioo u a) (hxy : x ≤ y) :=
    IntervalPrimitive.of_ac_ae hxy
      ((scalar_limit_absolute_continuity h hD d).1 u x y hxy (hs x y hx hy))
      (bv_ae_deriv_phi_out h hD d hxy (hs x y hx hy))
  have hφBV : BoundedVariationOn (S.phi u) (Ioo u a) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((eVariationOn.mono _ Ioo_subset_Ioi_self).trans
      ((bv_scalar_variation h hD d).1 u hu))
  have hwhole := bv_density_integrable_and_bound hua.le hφBV
    (bv_ae_deriv_phi_out_open h hD d hu)
  have hpb := (bv_open_scalar_variation_budget h hD d).1 u a hu
  have hh := bv_quotient_variation_le_residual
    (L := S.lam u) (Θ := S.theta u) (φ := S.phi u)
    (p := fun t => S.theta u t / S.r u t)
    (R := bvOutgoingScalarResidual S u a)
    (P := 10 ^ (64 : ℕ) * D.toReal) (T := 5 * D.toReal)
    (by positivity) (by positivity) hL
    (fun t ht => (bv_invariant_amplitudes h hD d (u, t) ⟨hu, ht.1⟩).1) hLBV
    (fun x hx y hy hxy => ⟨(hp x hx y hy hxy).1, by
      have hmono := intervalIntegral.integral_mono_interval
        (f := fun t => |S.theta u t / S.r u t|) hx.1.le hxy hy.2.le
        (Eventually.of_forall fun _ => abs_nonneg _) hwhole.1.abs
      exact hmono.trans (hwhole.2.trans hpb)⟩)
    (fun x hx y hy hxy => (hp x hx y hy hxy).2)
    (fun x hx y hy hxy => bv_outgoing_scalar_flux_integrable h hD d hu hx.1 hxy)
    (fun x hx y hy hxy => bv_outgoing_scalar_residual_increment_right h hD d
      hu hx.1 hxy hy.2.le)
  have he : EqOn (fun t => S.phi u t + S.theta u t / S.lam u t)
      (fun t => S.alpha u t / S.lam u t) (Ioo u a) := by
    intro t ht
    dsimp only [Fields.theta]
    field_simp [(lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3) (hL t ht)).ne']
    ring
  rw [eVariationOn.eq_of_eqOn he] at hh
  have hcoef : 3 * (10 ^ (64 : ℕ) * D.toReal) + 9 * (5 * D.toReal) ≤
      10 ^ (65 : ℕ) * D.toReal := by
    have hd := ENNReal.toReal_nonneg (a := D)
    nlinarith only [hd]
  have hv := expansion_variation_le_log
    (fun t ht => lt_of_lt_of_le (by norm_num) (hL t ht))
    (fun t ht => ((scalar_right_fields_geometry h hD d (u, t) ⟨hu, ht.1⟩).2.1).trans
      (by norm_num : (1 / 2 : ℝ) ≤ 1))
  exact hh.trans (add_le_add le_rfl
    (mul_le_mul (ENNReal.ofReal_le_ofReal hcoef) hv bot_le bot_le))

/-- The incoming quotient-residual inequality, including all jumps.
Negating ν, ζ and the scalar residual reduces it to the positive-expansion estimate. -/
theorem bv_incoming_quotient_residual_bound
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a v : ℝ} (ha : 0 ≤ a) (hav : a < v) :
    eVariationOn (fun t => d.scalarRightFields.beta t v / d.scalarRightFields.nu t v)
        (Ioo a v) ≤
      3 * eVariationOn (bvIncomingScalarResidual d.scalarRightFields v a) (Ioo a v) +
        ENNReal.ofReal (10 ^ (65 : ℕ) * D.toReal) *
          eVariationOn (fun t => Real.log (-d.scalarRightFields.nu t v)) (Ioo a v) := by
  let S := d.scalarRightFields
  have hL (t : ℝ) (ht : t ∈ Ioo a v) : (1 / 3 : ℝ) ≤ -S.nu t v :=
    (scalar_right_fields_geometry h hD d (t, v) ⟨ha.trans ht.1.le, ht.2⟩).2.2.1
  have hNuBV : BoundedVariationOn (fun t => S.nu t v) (Ioo a v) :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top s4UniversalC_ne_top (ENNReal.pow_ne_top hD))
      ((eVariationOn.mono _ (fun t ht => show t ∈ Ico 0 v from
        ⟨ha.trans ht.1.le, ht.2⟩)).trans
        ((right_expansions_variation h hD d).2 v (ha.trans_lt hav)))
  have hs (x y : ℝ) (hx : x ∈ Ioo a v) (hy : y ∈ Ioo a v) :
      inSeg v x y ⊆ globalDomain := by
    rintro ⟨t, s⟩ ⟨ht, rfl⟩
    exact ⟨ha.trans (hx.1.le.trans ht.1), ht.2.trans_lt hy.2⟩
  have hp (x : ℝ) (hx : x ∈ Ioo a v) (y : ℝ) (hy : y ∈ Ioo a v) (hxy : x ≤ y) :=
    IntervalPrimitive.of_ac_ae hxy
      ((scalar_limit_absolute_continuity h hD d).2 v x y hxy (hs x y hx hy))
      (bv_ae_deriv_phi_in h hD d hxy (hs x y hx hy))
  have hφBV : BoundedVariationOn (fun t => S.phi t v) (Ioo a v) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((eVariationOn.mono _
      (fun t ht => show t ∈ Ico 0 v from ⟨ha.trans ht.1.le, ht.2⟩)).trans
        ((bv_scalar_variation h hD d).2 v (ha.trans_lt hav)))
  have hwhole := bv_density_integrable_and_bound hav.le hφBV
    (bv_ae_deriv_phi_in_open h hD d ha)
  have hpb := (bv_open_scalar_variation_budget h hD d).2 a v ha hav
  have hh := bv_quotient_variation_le_residual
    (L := fun t => -S.nu t v) (Θ := fun t => -S.zeta t v) (φ := fun t => S.phi t v)
    (p := fun t => S.zeta t v / S.r t v)
    (R := fun t => -bvIncomingScalarResidual S v a t)
    (P := 10 ^ (64 : ℕ) * D.toReal) (T := 8 * D.toReal)
    (by positivity) (by positivity) hL
    (fun t ht => by
      rw [abs_neg]
      exact (bv_invariant_amplitudes h hD d (t, v) ⟨ha.trans ht.1.le, ht.2⟩).2)
    hNuBV.neg
    (fun x hx y hy hxy => ⟨(hp x hx y hy hxy).1, by
      have hmono := intervalIntegral.integral_mono_interval
        (f := fun t => |S.zeta t v / S.r t v|) hx.1.le hxy hy.2.le
        (Eventually.of_forall fun _ => abs_nonneg _) hwhole.1.abs
      exact hmono.trans (hwhole.2.trans hpb)⟩)
    (fun x hx y hy hxy => (hp x hx y hy hxy).2)
    (fun x hx y hy hxy => by
      have hi := (bv_incoming_scalar_flux_integrable h hD d
        (ha.trans hx.1.le) hxy hy.2).neg
      change IntervalIntegrable (fun t => -(S.nu t v * (S.zeta t v / S.r t v)))
        volume x y at hi
      simpa only [neg_mul] using hi)
    (fun x hx y hy hxy => by
      have hi := bv_incoming_scalar_residual_increment h hD d ha hx.1.le hxy hy.2
      rw [show (fun t => -S.nu t v * (S.zeta t v / S.r t v)) =
        fun t => -(S.nu t v * (S.zeta t v / S.r t v)) by funext t; ring,
        intervalIntegral.integral_neg]
      linarith only [hi])
  have he : EqOn (fun t => S.phi t v + -S.zeta t v / -S.nu t v)
      (fun t => S.beta t v / S.nu t v) (Ioo a v) := by
    intro t ht
    have hn : S.nu t v ≠ 0 := by linarith only [hL t ht]
    dsimp only [Fields.zeta]
    field_simp [hn]
    ring
  rw [eVariationOn.eq_of_eqOn he,
    show eVariationOn (fun t => -bvIncomingScalarResidual S v a t) (Ioo a v) =
      eVariationOn (bvIncomingScalarResidual S v a) (Ioo a v) from eVariationOn.neg _ _] at hh
  have hcoef : 3 * (10 ^ (64 : ℕ) * D.toReal) + 9 * (8 * D.toReal) ≤
      10 ^ (65 : ℕ) * D.toReal := by
    have hd := ENNReal.toReal_nonneg (a := D)
    nlinarith only [hd]
  have hv := expansion_variation_le_log
    (L := fun t => -S.nu t v) (s := Ioo a v)
    (fun t ht => lt_of_lt_of_le (by norm_num) (hL t ht))
    (fun t ht => ((scalar_right_fields_geometry h hD d (t, v)
      ⟨ha.trans ht.1.le, ht.2⟩).2.2.2.1).trans (by norm_num : (2 / 3 : ℝ) ≤ 1))
  exact hh.trans (add_le_add le_rfl
    (mul_le_mul (ENNReal.ofReal_le_ofReal hcoef) hv bot_le bot_le))

end ChristodoulouBV

end
