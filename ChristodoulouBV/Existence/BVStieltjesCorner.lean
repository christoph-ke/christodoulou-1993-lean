module

public import ChristodoulouBV.Existence.BVStieltjesSectionBounds
public import ChristodoulouBV.Existence.BVStieltjesLogBounds
public import ChristodoulouBV.Existence.BVStieltjesLogShrink
public import ChristodoulouBV.Existence.BVStieltjesContraction
import Mathlib.Tactic

/-!
# Coupled corner absorption with explicit mass-ratio inputs

The universal threshold is the already fixed `epsilonChosen`. The only
extra premises in the corner lemmas are exactly the explicit mass-ratio
majorants. The unconditional source names (6.9) and (6.12) are reserved
until those inputs are available for the canonical limit.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The existing universal threshold simultaneously absorbs all four
canonical corner inequalities with the same numerical coefficient. -/
theorem bv_absorption_coefficient_small {D : ℝ≥0∞}
    (hsmall : D < ENNReal.ofReal epsilonChosen) :
    0 ≤ (10 : ℝ) ^ (65 : ℕ) * D.toReal ∧
      (10 : ℝ) ^ (65 : ℕ) * D.toReal < 1 := by
  have hd : D.toReal < epsilonChosen := ENNReal.toReal_lt_of_lt_ofReal hsmall
  refine ⟨by positivity, ?_⟩
  have hh := mul_lt_mul_of_pos_left hd (by norm_num : (0 : ℝ) < 10 ^ (65 : ℕ))
  have hnum : (10 : ℝ) ^ (65 : ℕ) * epsilonChosen < 1 := by
    norm_num [epsilonChosen_eq]
  exact hh.trans hnum

/-- Internal outgoing corner conclusion with exactly the axis-to-point
outgoing mass-ratio majorant. No conditional theorem named `eq6_9` is exported. -/
theorem bv_outgoing_corner_of_mass_ratio_majorant
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (hsmall : D < ENNReal.ofReal epsilonChosen)
    (hA : ∀ u b : ℝ, 0 ≤ u → u < b →
      IntervalIntegrable (fun t =>
        (2 * d.scalarRightFields.m u t / d.scalarRightFields.r u t) *
          d.scalarRightFields.lam u t /
          ((1 - 2 * d.scalarRightFields.m u t / d.scalarRightFields.r u t) *
            d.scalarRightFields.r u t)) volume u b ∧
      (∫ t in u..b, (2 * d.scalarRightFields.m u t / d.scalarRightFields.r u t) *
        d.scalarRightFields.lam u t /
        ((1 - 2 * d.scalarRightFields.m u t / d.scalarRightFields.r u t) *
          d.scalarRightFields.r u t)) ≤
        (15 * D.toReal) * (eVariationOn (d.scalarRightFields.phi u) (Ioo u b)).toReal)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun u => eVariationOn (fun t => d.scalarRightFields.alpha u t /
      d.scalarRightFields.lam u t) (Ioo u a)) (𝓝[<] a) (𝓝 0) ∧
    Tendsto (fun u => eVariationOn (fun t => Real.log (d.scalarRightFields.lam u t))
      (Ioo u a)) (𝓝[<] a) (𝓝 0) := by
  let S := d.scalarRightFields
  let κ := (10 : ℝ) ^ (65 : ℕ) * D.toReal
  have hκ := bv_absorption_coefficient_small hsmall
  have hfin := (bv_corner_variations_finite h hD d).1
  have hQfin : ∀ᶠ u in 𝓝[<] a, eVariationOn (fun t => S.alpha u t / S.lam u t)
      (Ioo u a) ≠ ∞ := by
    filter_upwards [Ioo_mem_nhdsLT ha] with u hu
    exact (hfin u a hu.1.le).1
  have hLfin : ∀ᶠ u in 𝓝[<] a,
      eVariationOn (fun t => Real.log (S.lam u t)) (Ioo u a) ≠ ∞ := by
    filter_upwards [Ioo_mem_nhdsLT ha] with u hu
    exact (hfin u a hu.1.le).2
  have hQ : ∀ᶠ u in 𝓝[<] a,
      eVariationOn (fun t => S.alpha u t / S.lam u t) (Ioo u a) ≤
        3 * eVariationOn (bvOutgoingScalarResidual S u a) (Ioo u a) +
          ENNReal.ofReal κ * eVariationOn (fun t => Real.log (S.lam u t)) (Ioo u a) := by
    filter_upwards [Ioo_mem_nhdsLT ha] with u hu
    exact bv_outgoing_quotient_residual_bound h hD d hu.1.le hu.2
  have hL : ∀ᶠ u in 𝓝[<] a,
      eVariationOn (fun t => Real.log (S.lam u t)) (Ioo u a) ≤
        eVariationOn (bvOutgoingLogResidual S u a) (Ioo u a) +
          ENNReal.ofReal κ * eVariationOn (fun t => S.alpha u t / S.lam u t) (Ioo u a) := by
    filter_upwards [Ioo_mem_nhdsLT ha] with u hu
    have hg := bv_outgoing_g_bound_of_mass_ratio_majorant h hD d hu.1.le hu.2
      (hA u a hu.1.le hu.2)
    have hh := bv_variation_le_residual_add_integral hu.2.le hg.1
      (fun x hx y hy hxy => bv_outgoing_log_residual_increment h hD d
        hu.1.le hx.1 hxy hy.2.le)
    have hqfinite := (hfin u a hu.1.le).1
    have hφq := ENNReal.toReal_mono hqfinite
      (bv_outgoing_ratio_variation h hD d hu.1.le hu.2)
    have hcoef : 54 * D.toReal ≤ κ :=
      mul_le_mul_of_nonneg_right (by norm_num : (54 : ℝ) ≤ 10 ^ (65 : ℕ))
        ENNReal.toReal_nonneg
    have hr : (∫ t in u..a, |bvOutgoingLogCoefficient S u t|) ≤
        κ * (eVariationOn (fun t => S.alpha u t / S.lam u t) (Ioo u a)).toReal :=
      hg.2.trans (mul_le_mul hcoef hφq ENNReal.toReal_nonneg hκ.1)
    calc
      _ ≤ eVariationOn (bvOutgoingLogResidual S u a) (Ioo u a) +
          ENNReal.ofReal (∫ t in u..a, |bvOutgoingLogCoefficient S u t|) := hh
      _ ≤ eVariationOn (bvOutgoingLogResidual S u a) (Ioo u a) +
          ENNReal.ofReal (κ * (eVariationOn (fun t => S.alpha u t / S.lam u t)
            (Ioo u a)).toReal) := add_le_add le_rfl (ENNReal.ofReal_le_ofReal hr)
      _ = _ := by rw [ENNReal.ofReal_mul hκ.1, ENNReal.ofReal_toReal hqfinite]
  exact tendsto_zero_of_coupled_ennreal_variation_bounds hκ.1 hκ.2 hQfin hLfin hQ hL
    (eq6_7b h hD d ha) (eq6_8b h hD d ha)

/-- Internal incoming corner conclusion with exactly the incoming
mass-ratio majorant. The universal threshold and corrected log sign are unchanged. -/
theorem bv_incoming_corner_of_mass_ratio_majorant
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (hsmall : D < ENNReal.ofReal epsilonChosen)
    (hB : ∀ a v : ℝ, 0 ≤ a → a < v →
      IntervalIntegrable (fun t =>
        (2 * d.scalarRightFields.m t v / d.scalarRightFields.r t v) *
          d.scalarRightFields.nu t v /
          ((1 - 2 * d.scalarRightFields.m t v / d.scalarRightFields.r t v) *
            d.scalarRightFields.r t v)) volume a v ∧
      -(∫ t in a..v, (2 * d.scalarRightFields.m t v / d.scalarRightFields.r t v) *
        d.scalarRightFields.nu t v /
        ((1 - 2 * d.scalarRightFields.m t v / d.scalarRightFields.r t v) *
          d.scalarRightFields.r t v)) ≤
        (24 * D.toReal) * (eVariationOn (fun t => d.scalarRightFields.phi t v)
          (Ioo a v)).toReal)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun v => eVariationOn (fun t => d.scalarRightFields.beta t v /
      d.scalarRightFields.nu t v) (Ioo a v)) (𝓝[>] a) (𝓝 0) ∧
    Tendsto (fun v => eVariationOn (fun t => Real.log (-d.scalarRightFields.nu t v))
      (Ioo a v)) (𝓝[>] a) (𝓝 0) := by
  let S := d.scalarRightFields
  let κ := (10 : ℝ) ^ (65 : ℕ) * D.toReal
  have hκ := bv_absorption_coefficient_small hsmall
  have hfin := (bv_corner_variations_finite h hD d).2
  have hQfin : ∀ᶠ v in 𝓝[>] a, eVariationOn (fun t => S.beta t v / S.nu t v)
      (Ioo a v) ≠ ∞ := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact (hfin a v ha.le hv).1
  have hLfin : ∀ᶠ v in 𝓝[>] a,
      eVariationOn (fun t => Real.log (-S.nu t v)) (Ioo a v) ≠ ∞ := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact (hfin a v ha.le hv).2
  have hQ : ∀ᶠ v in 𝓝[>] a,
      eVariationOn (fun t => S.beta t v / S.nu t v) (Ioo a v) ≤
        3 * eVariationOn (bvIncomingScalarResidual S v a) (Ioo a v) +
          ENNReal.ofReal κ * eVariationOn (fun t => Real.log (-S.nu t v)) (Ioo a v) := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact bv_incoming_quotient_residual_bound h hD d ha.le hv
  have hL : ∀ᶠ v in 𝓝[>] a,
      eVariationOn (fun t => Real.log (-S.nu t v)) (Ioo a v) ≤
        eVariationOn (bvIncomingLogResidual S v a) (Ioo a v) +
          ENNReal.ofReal κ * eVariationOn (fun t => S.beta t v / S.nu t v) (Ioo a v) := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hg := bv_incoming_g_bound_of_mass_ratio_majorant h hD d ha.le hv
      (hB a v ha.le hv)
    have hh := bv_variation_le_residual_add_integral hv.le hg.1
      (fun x hx y hy hxy => bv_incoming_log_residual_increment h hD d
        ha.le hx.1.le hxy hy.2)
    have hqfinite := (hfin a v ha.le hv).1
    have hφq := ENNReal.toReal_mono hqfinite
      (bv_incoming_ratio_variation h hD d ha.le hv)
    have hcoef : 63 * D.toReal ≤ κ :=
      mul_le_mul_of_nonneg_right (by norm_num : (63 : ℝ) ≤ 10 ^ (65 : ℕ))
        ENNReal.toReal_nonneg
    have hr : (∫ t in a..v, |bvIncomingLogCoefficient S t v|) ≤
        κ * (eVariationOn (fun t => S.beta t v / S.nu t v) (Ioo a v)).toReal :=
      hg.2.trans (mul_le_mul hcoef hφq ENNReal.toReal_nonneg hκ.1)
    calc
      _ ≤ eVariationOn (bvIncomingLogResidual S v a) (Ioo a v) +
          ENNReal.ofReal (∫ t in a..v, |bvIncomingLogCoefficient S t v|) := hh
      _ ≤ eVariationOn (bvIncomingLogResidual S v a) (Ioo a v) +
          ENNReal.ofReal (κ * (eVariationOn (fun t => S.beta t v / S.nu t v)
            (Ioo a v)).toReal) := add_le_add le_rfl (ENNReal.ofReal_le_ofReal hr)
      _ = _ := by rw [ENNReal.ofReal_mul hκ.1, ENNReal.ofReal_toReal hqfinite]
  exact tendsto_zero_of_coupled_ennreal_variation_bounds hκ.1 hκ.2 hQfin hLfin hQ hL
    (eq6_10b h hD d ha (lt_add_one a)) (eq6_11b h hD d ha (lt_add_one a))

end ChristodoulouBV

end
