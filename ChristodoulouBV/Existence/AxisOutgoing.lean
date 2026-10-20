module

public import ChristodoulouBV.Existence.AxisOutgoingResiduals
import Mathlib.Tactic

/-!
# Uniform outgoing axis variation

The two residuals on shrinking outgoing triangles vanish uniformly by
(6.13b) and (6.14b). Taking suprema in the coupled quotient/logarithm
inequalities and absorbing at the existing universal threshold gives
the corrected zero conclusion in (6.15).
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The outgoing logarithmic variation is bounded by its residual and
the quotient variation with the universal BV absorption coefficient. -/
theorem bv_outgoing_log_residual_bound
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u b : ℝ} (hu : 0 ≤ u) (hub : u < b) :
    eVariationOn (fun t => Real.log (d.scalarRightFields.lam u t)) (Ioo u b) ≤
      eVariationOn (bvOutgoingLogResidual d.scalarRightFields u b) (Ioo u b) +
        ENNReal.ofReal (10 ^ (65 : ℕ) * D.toReal) *
          eVariationOn (fun t => d.scalarRightFields.alpha u t /
            d.scalarRightFields.lam u t) (Ioo u b) := by
  let S := d.scalarRightFields
  let κ := (10 : ℝ) ^ (65 : ℕ) * D.toReal
  have hκ : 0 ≤ κ := by positivity
  have hg := bv_outgoing_g_bound h hD d hu hub
  have hh := bv_variation_le_residual_add_integral hub.le hg.1
    (fun x hx y hy hxy => bv_outgoing_log_residual_increment h hD d
      hu hx.1 hxy hy.2.le)
  have hqfinite := ((bv_corner_variations_finite h hD d).1 u b hu).1
  have hcoef : 54 * D.toReal ≤ κ :=
    mul_le_mul_of_nonneg_right (by norm_num : (54 : ℝ) ≤ 10 ^ (65 : ℕ))
      ENNReal.toReal_nonneg
  have hr := hg.2.trans (mul_le_mul_of_nonneg_right hcoef
    (ENNReal.toReal_nonneg (a := eVariationOn (fun t => S.alpha u t / S.lam u t)
      (Ioo u b))))
  calc
    _ ≤ eVariationOn (bvOutgoingLogResidual S u b) (Ioo u b) +
        ENNReal.ofReal (∫ t in u..b, |bvOutgoingLogCoefficient S u t|) := hh
    _ ≤ eVariationOn (bvOutgoingLogResidual S u b) (Ioo u b) +
        ENNReal.ofReal (κ * (eVariationOn (fun t => S.alpha u t / S.lam u t)
          (Ioo u b)).toReal) := add_le_add le_rfl (ENNReal.ofReal_le_ofReal hr)
    _ = _ := by rw [ENNReal.ofReal_mul hκ, ENNReal.ofReal_toReal hqfinite]

/-- Corrected (6.15): both outgoing quotient and logarithmic expansion
variations tend uniformly to zero on every shrinking future triangle.
The smallness threshold and every absorption constant are universal. -/
theorem eq6_15
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (hsmall : D < ENNReal.ofReal epsilonChosen)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε => ⨆ u ∈ Ioo a (a + ε), eVariationOn
      (fun t => d.scalarRightFields.alpha u t / d.scalarRightFields.lam u t)
        (Ioo u (a + ε))) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε => ⨆ u ∈ Ioo a (a + ε), eVariationOn
      (fun t => Real.log (d.scalarRightFields.lam u t)) (Ioo u (a + ε)))
        (𝓝[>] 0) (𝓝 0) := by
  let S := d.scalarRightFields
  let Q := fun ε u => eVariationOn (fun t => S.alpha u t / S.lam u t) (Ioo u (a + ε))
  let L := fun ε u => eVariationOn (fun t => Real.log (S.lam u t)) (Ioo u (a + ε))
  let R := fun ε u => eVariationOn (bvOutgoingScalarResidual S u (a + ε)) (Ioo u (a + ε))
  let G := fun ε u => eVariationOn (bvOutgoingLogResidual S u (a + ε)) (Ioo u (a + ε))
  let κ := (10 : ℝ) ^ (65 : ℕ) * D.toReal
  have hκ := bv_absorption_coefficient_small hsmall
  have hM : 3 * ENNReal.ofReal (s6EndpointTVK * D.toReal) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hbound (ε : ℝ) :
      (⨆ u ∈ Ioo a (a + ε), Q ε u) ≤ 3 * ENNReal.ofReal (s6EndpointTVK * D.toReal) ∧
      (⨆ u ∈ Ioo a (a + ε), L ε u) ≤ 3 * ENNReal.ofReal (s6EndpointTVK * D.toReal) := by
    have hb (u : ℝ) (hu : u ∈ Ioo a (a + ε)) :=
      (scalar_right_fields_three_term_tv h hD d).1 u (ha.le.trans hu.1.le)
    constructor
    · refine iSup_le fun u => iSup_le fun hu => ?_
      have ht := hb u hu
      change _ + _ + _ ≤ _ at ht
      exact (eVariationOn.mono _ Ioo_subset_Ioi_self).trans
        ((le_add_of_nonneg_right bot_le).trans
          ((le_add_of_nonneg_right bot_le).trans ht))
    · refine iSup_le fun u => iSup_le fun hu => ?_
      have ht := hb u hu
      change _ + _ + _ ≤ _ at ht
      exact (eVariationOn.mono _ Ioo_subset_Ioi_self).trans
        ((le_add_of_nonneg_left bot_le).trans ht)
  have hQfin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (⨆ u ∈ Ioo a (a + ε), Q ε u) ≠ ∞ :=
    Eventually.of_forall fun ε => ne_top_of_le_ne_top hM (hbound ε).1
  have hLfin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (⨆ u ∈ Ioo a (a + ε), L ε u) ≠ ∞ :=
    Eventually.of_forall fun ε => ne_top_of_le_ne_top hM (hbound ε).2
  have hQ : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (⨆ u ∈ Ioo a (a + ε), Q ε u) ≤
        3 * (⨆ u ∈ Ioo a (a + ε), R ε u) +
          ENNReal.ofReal κ * (⨆ u ∈ Ioo a (a + ε), L ε u) := by
    apply Eventually.of_forall
    intro ε
    refine iSup_le fun u => iSup_le fun hu => ?_
    exact (bv_outgoing_quotient_residual_bound h hD d (ha.le.trans hu.1.le) hu.2).trans
      (add_le_add
        (mul_le_mul le_rfl (le_iSup_of_le u (le_iSup_of_le hu le_rfl)) bot_le bot_le)
        (mul_le_mul le_rfl (le_iSup_of_le u (le_iSup_of_le hu le_rfl)) bot_le bot_le))
  have hL : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (⨆ u ∈ Ioo a (a + ε), L ε u) ≤
        (⨆ u ∈ Ioo a (a + ε), G ε u) +
          ENNReal.ofReal κ * (⨆ u ∈ Ioo a (a + ε), Q ε u) := by
    apply Eventually.of_forall
    intro ε
    refine iSup_le fun u => iSup_le fun hu => ?_
    exact (bv_outgoing_log_residual_bound h hD d (ha.le.trans hu.1.le) hu.2).trans
      (add_le_add (le_iSup_of_le u (le_iSup_of_le hu le_rfl))
        (mul_le_mul le_rfl (le_iSup_of_le u (le_iSup_of_le hu le_rfl)) bot_le bot_le))
  exact tendsto_zero_of_coupled_ennreal_variation_bounds hκ.1 hκ.2 hQfin hLfin hQ hL
    (eq6_13b h hD d ha) (eq6_14b h hD d ha)

end ChristodoulouBV

end
