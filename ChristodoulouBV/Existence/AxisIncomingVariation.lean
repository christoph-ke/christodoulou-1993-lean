module

public import ChristodoulouBV.Existence.AxisIncomingResiduals
import Mathlib.Tactic

/-!
# Uniform incoming axis variation

The scalar and corrected logarithmic residuals vanish uniformly on the
shrinking past triangles. The coupled BV quotient/logarithm inequalities
absorb at the existing universal threshold, proving (6.18).
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The incoming logarithmic variation is bounded by its residual and
the quotient variation with the universal BV absorption coefficient. -/
theorem bv_incoming_log_residual_bound
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a v : ℝ} (ha : 0 ≤ a) (hav : a < v) :
    eVariationOn (fun t => Real.log (-d.scalarRightFields.nu t v)) (Ioo a v) ≤
      eVariationOn (bvIncomingLogResidual d.scalarRightFields v a) (Ioo a v) +
        ENNReal.ofReal (10 ^ (65 : ℕ) * D.toReal) *
          eVariationOn (fun t => d.scalarRightFields.beta t v /
            d.scalarRightFields.nu t v) (Ioo a v) := by
  let S := d.scalarRightFields
  let κ := (10 : ℝ) ^ (65 : ℕ) * D.toReal
  have hκ : 0 ≤ κ := by positivity
  have hg := bv_incoming_g_bound h hD d ha hav
  have hh := bv_variation_le_residual_add_integral hav.le hg.1
    (fun x hx y hy hxy => bv_incoming_log_residual_increment h hD d
      ha hx.1.le hxy hy.2)
  have hqfinite := ((bv_corner_variations_finite h hD d).2 a v ha hav).1
  have hcoef : 63 * D.toReal ≤ κ :=
    mul_le_mul_of_nonneg_right (by norm_num : (63 : ℝ) ≤ 10 ^ (65 : ℕ))
      ENNReal.toReal_nonneg
  have hr := hg.2.trans (mul_le_mul_of_nonneg_right hcoef
    (ENNReal.toReal_nonneg (a := eVariationOn (fun t => S.beta t v / S.nu t v)
      (Ioo a v))))
  calc
    _ ≤ eVariationOn (bvIncomingLogResidual S v a) (Ioo a v) +
        ENNReal.ofReal (∫ t in a..v, |bvIncomingLogCoefficient S t v|) := hh
    _ ≤ eVariationOn (bvIncomingLogResidual S v a) (Ioo a v) +
        ENNReal.ofReal (κ * (eVariationOn (fun t => S.beta t v / S.nu t v)
          (Ioo a v)).toReal) := add_le_add le_rfl (ENNReal.ofReal_le_ofReal hr)
    _ = _ := by rw [ENNReal.ofReal_mul hκ, ENNReal.ofReal_toReal hqfinite]

/-- Equation (6.18): both incoming quotient and logarithmic expansion
variations tend uniformly to zero on every shrinking past triangle.
The threshold and absorption constants are universal. -/
theorem eq6_18
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (hsmall : D < ENNReal.ofReal epsilonChosen)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε => ⨆ v ∈ Ioo (a - ε) a, eVariationOn
      (fun t => d.scalarRightFields.beta t v / d.scalarRightFields.nu t v)
        (Ioo (a - ε) v)) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε => ⨆ v ∈ Ioo (a - ε) a, eVariationOn
      (fun t => Real.log (-d.scalarRightFields.nu t v)) (Ioo (a - ε) v))
        (𝓝[>] 0) (𝓝 0) := by
  let S := d.scalarRightFields
  let Q := fun ε v => eVariationOn (fun t => S.beta t v / S.nu t v) (Ioo (a - ε) v)
  let L := fun ε v => eVariationOn (fun t => Real.log (-S.nu t v)) (Ioo (a - ε) v)
  let R := fun ε v => eVariationOn (bvIncomingScalarResidual S v (a - ε)) (Ioo (a - ε) v)
  let G := fun ε v => eVariationOn (bvIncomingLogResidual S v (a - ε)) (Ioo (a - ε) v)
  let κ := (10 : ℝ) ^ (65 : ℕ) * D.toReal
  have hκ := bv_absorption_coefficient_small hsmall
  have hM : 3 * ENNReal.ofReal (s6EndpointTVK * D.toReal) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hbound (ε : ℝ) (hεa : ε < a) :
      (⨆ v ∈ Ioo (a - ε) a, Q ε v) ≤ 3 * ENNReal.ofReal (s6EndpointTVK * D.toReal) ∧
      (⨆ v ∈ Ioo (a - ε) a, L ε v) ≤ 3 * ENNReal.ofReal (s6EndpointTVK * D.toReal) := by
    have hb (v : ℝ) (hv : v ∈ Ioo (a - ε) a) :=
      (scalar_right_fields_three_term_tv h hD d).2 v ((sub_pos.mpr hεa).trans hv.1)
    have hsub (v : ℝ) : Ioo (a - ε) v ⊆ Ioo 0 v :=
      Ioo_subset_Ioo (sub_nonneg.mpr hεa.le) le_rfl
    constructor
    · refine iSup_le fun v => iSup_le fun hv => ?_
      have ht := hb v hv
      change _ + _ + _ ≤ _ at ht
      exact (eVariationOn.mono _ (hsub v)).trans
        ((le_add_of_nonneg_right bot_le).trans
          ((le_add_of_nonneg_right bot_le).trans ht))
    · refine iSup_le fun v => iSup_le fun hv => ?_
      have ht := hb v hv
      change _ + _ + _ ≤ _ at ht
      exact (eVariationOn.mono _ (hsub v)).trans
        ((le_add_of_nonneg_left bot_le).trans ht)
  have hQfin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (⨆ v ∈ Ioo (a - ε) a, Q ε v) ≠ ∞ := by
    filter_upwards [Ioo_mem_nhdsGT ha] with ε hε
    exact ne_top_of_le_ne_top hM (hbound ε hε.2).1
  have hLfin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (⨆ v ∈ Ioo (a - ε) a, L ε v) ≠ ∞ := by
    filter_upwards [Ioo_mem_nhdsGT ha] with ε hε
    exact ne_top_of_le_ne_top hM (hbound ε hε.2).2
  have hQ : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (⨆ v ∈ Ioo (a - ε) a, Q ε v) ≤
        3 * (⨆ v ∈ Ioo (a - ε) a, R ε v) +
          ENNReal.ofReal κ * (⨆ v ∈ Ioo (a - ε) a, L ε v) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with ε hε
    refine iSup_le fun v => iSup_le fun hv => ?_
    exact (bv_incoming_quotient_residual_bound h hD d (sub_nonneg.mpr hε.2.le) hv.1).trans
      (add_le_add
        (mul_le_mul le_rfl (le_iSup_of_le v (le_iSup_of_le hv le_rfl)) bot_le bot_le)
        (mul_le_mul le_rfl (le_iSup_of_le v (le_iSup_of_le hv le_rfl)) bot_le bot_le))
  have hL : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (⨆ v ∈ Ioo (a - ε) a, L ε v) ≤
        (⨆ v ∈ Ioo (a - ε) a, G ε v) +
          ENNReal.ofReal κ * (⨆ v ∈ Ioo (a - ε) a, Q ε v) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with ε hε
    refine iSup_le fun v => iSup_le fun hv => ?_
    exact (bv_incoming_log_residual_bound h hD d (sub_nonneg.mpr hε.2.le) hv.1).trans
      (add_le_add (le_iSup_of_le v (le_iSup_of_le hv le_rfl))
        (mul_le_mul le_rfl (le_iSup_of_le v (le_iSup_of_le hv le_rfl)) bot_le bot_le))
  exact tendsto_zero_of_coupled_ennreal_variation_bounds hκ.1 hκ.2 hQfin hLfin hQ hL
    (eq6_16b h hD d ha) (eq6_17b h hD d ha)

end ChristodoulouBV

end
