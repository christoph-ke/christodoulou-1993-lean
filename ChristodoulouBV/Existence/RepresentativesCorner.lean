module

public import ChristodoulouBV.Existence.BVStieltjes
public import ChristodoulouBV.AreaEstimates.SourceInputsWeak
import Mathlib.Tactic

/-!
# Incoming corner estimates including the initial axis point

The positive-basepoint Stieltjes transports extend to basepoint zero by
exhausting the open incoming interval. Changing the primitive basepoint
preserves increments. This supplies the initial axis point without
asserting that characteristic jump lines have zero analytic area.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem variation_le_of_same_increments {f g : ℝ → ℝ} {s : Set ℝ}
    (he : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → f y - f x = g y - g x) :
    eVariationOn f s ≤ eVariationOn g s := by
  have hb := eVariationOn.le_of_dist_le (h := f) (k := g) (s := s)
    (by norm_num : (0 : ℝ) ≤ 1) (by
      intro x hx y hy
      simp only [one_mul, Real.dist_eq]
      rcases le_total x y with hxy | hyx
      · rw [abs_sub_comm (f x), he x hx y hy hxy, abs_sub_comm (g y)]
      · rw [he y hy x hx hyx])
  simpa only [ENNReal.ofReal_one, one_mul] using hb

private theorem variation_le_of_positive_left_cutoffs {f : ℝ → ℝ} {v : ℝ} {M : ℝ≥0∞}
    (hb : ∀ a, 0 < a → a < v → eVariationOn f (Ioo a v) ≤ M) :
    eVariationOn f (Ioo 0 v) ≤ M := by
  rw [eVariationOn]
  refine iSup_le ?_
  rintro ⟨n, w, hw, hs⟩
  have ha : 0 < w 0 / 2 := half_pos (hs 0).1
  have haw : w 0 / 2 < w 0 := half_lt_self (hs 0).1
  exact (eVariationOn.sum_le hw (fun i =>
    show w i ∈ Ioo (w 0 / 2) v from
      ⟨haw.trans_le (hw (Nat.zero_le i)), (hs i).2⟩)).trans
    (hb _ ha (haw.trans (hs 0).2))

private theorem incoming_scalar_transport_zero
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {v b : ℝ} (_hv : 0 < v) (hvb : v < b) :
    eVariationOn (bvIncomingScalarResidual d.scalarRightFields v 0) (Ioo 0 v) ≤
      eVariationOn (bvIncomingScalarResidual d.scalarRightFields b 0) (Ioo 0 v) +
        bvAnalyticArea h hD d .nuPhi (Ioo 0 v ×ˢ Ioo v b) := by
  have hbase (a w : ℝ) (ha : 0 < a) (hw : v ≤ w) :
      eVariationOn (bvIncomingScalarResidual d.scalarRightFields w 0) (Ioo a v) =
        eVariationOn (bvIncomingScalarResidual d.scalarRightFields w a) (Ioo a v) := by
    have he (x : ℝ) (hx : x ∈ Ioo a v) (y : ℝ) (hy : y ∈ Ioo a v) (hxy : x ≤ y) :
        bvIncomingScalarResidual d.scalarRightFields w 0 y -
          bvIncomingScalarResidual d.scalarRightFields w 0 x =
        bvIncomingScalarResidual d.scalarRightFields w a y -
          bvIncomingScalarResidual d.scalarRightFields w a x := by
      rw [bv_incoming_scalar_residual_increment h hD d le_rfl
          (ha.le.trans hx.1.le) hxy (hy.2.trans_le hw),
        bv_incoming_scalar_residual_increment h hD d ha.le hx.1.le hxy (hy.2.trans_le hw)]
    exact le_antisymm (variation_le_of_same_increments he)
      (variation_le_of_same_increments (fun x hx y hy hxy => (he x hx y hy hxy).symm))
  apply variation_le_of_positive_left_cutoffs
  intro a ha hav
  rw [hbase a v ha le_rfl]
  calc
    _ ≤ eVariationOn (bvIncomingScalarResidual d.scalarRightFields b a) (Ioo a v) +
        bvAnalyticArea h hD d .nuPhi (Ioo a v ×ˢ Ioo v b) :=
      eq6_10a h hD d ha hav hvb
    _ = eVariationOn (bvIncomingScalarResidual d.scalarRightFields b 0) (Ioo a v) +
        bvAnalyticArea h hD d .nuPhi (Ioo a v ×ˢ Ioo v b) := by
      rw [hbase a b ha hvb.le]
    _ ≤ _ := add_le_add (eVariationOn.mono _ (Ioo_subset_Ioo ha.le le_rfl))
      (measure_mono (Set.prod_mono (Ioo_subset_Ioo ha.le le_rfl) Subset.rfl))

private theorem incoming_log_transport_zero
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {v b : ℝ} (_hv : 0 < v) (hvb : v < b) :
    eVariationOn (bvIncomingLogResidual d.scalarRightFields v 0) (Ioo 0 v) ≤
      eVariationOn (bvIncomingLogResidual d.scalarRightFields b 0) (Ioo 0 v) +
        bvAnalyticArea h hD d .phiAlphaLam (Ioo 0 v ×ˢ Icc v b) := by
  have hbase (a w : ℝ) (ha : 0 < a) (hw : v ≤ w) :
      eVariationOn (bvIncomingLogResidual d.scalarRightFields w 0) (Ioo a v) =
        eVariationOn (bvIncomingLogResidual d.scalarRightFields w a) (Ioo a v) := by
    have he (x : ℝ) (hx : x ∈ Ioo a v) (y : ℝ) (hy : y ∈ Ioo a v) (hxy : x ≤ y) :
        bvIncomingLogResidual d.scalarRightFields w 0 y -
          bvIncomingLogResidual d.scalarRightFields w 0 x =
        bvIncomingLogResidual d.scalarRightFields w a y -
          bvIncomingLogResidual d.scalarRightFields w a x := by
      rw [bv_incoming_log_residual_increment h hD d le_rfl
          (ha.le.trans hx.1.le) hxy (hy.2.trans_le hw),
        bv_incoming_log_residual_increment h hD d ha.le hx.1.le hxy (hy.2.trans_le hw)]
    exact le_antisymm (variation_le_of_same_increments he)
      (variation_le_of_same_increments (fun x hx y hy hxy => (he x hx y hy hxy).symm))
  apply variation_le_of_positive_left_cutoffs
  intro a ha hav
  rw [hbase a v ha le_rfl]
  calc
    _ ≤ eVariationOn (bvIncomingLogResidual d.scalarRightFields b a) (Ioo a v) +
        bvAnalyticArea h hD d .phiAlphaLam (Ioo a v ×ˢ Icc v b) :=
      eq6_11a h hD d ha hav hvb
    _ = eVariationOn (bvIncomingLogResidual d.scalarRightFields b 0) (Ioo a v) +
        bvAnalyticArea h hD d .phiAlphaLam (Ioo a v ×ˢ Icc v b) := by
      rw [hbase a b ha hvb.le]
    _ ≤ _ := add_le_add (eVariationOn.mono _ (Ioo_subset_Ioo ha.le le_rfl))
      (measure_mono (Set.prod_mono (Ioo_subset_Ioo ha.le le_rfl) Subset.rfl))

/-- The incoming scalar residual tends to zero at every nonnegative axis
basepoint, including the initial endpoint. -/
theorem representatives_incoming_scalar_residual_tendsto
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Tendsto (fun v => eVariationOn (bvIncomingScalarResidual d.scalarRightFields v a)
      (Ioo a v)) (𝓝[>] a) (𝓝 0) := by
  let c := (a + b) / 2
  have hac : a < c := by dsimp only [c]; linarith only [hab]
  have hcb : c < b := by dsimp only [c]; linarith only [hab]
  have hf := (bv_incoming_scalar_residual_bv h hD d ha hac.le hcb).mono Ioo_subset_Icc_self
  have hfixed := bv_variation_right_tail_tendsto_zero hac hf
  have harea := bv_area_incoming_rectangle_tendsto h hD d .nuPhi (b := b) ha
  have hsum : Tendsto (fun v =>
      eVariationOn (bvIncomingScalarResidual d.scalarRightFields b a) (Ioo a v) +
        bvAnalyticArea h hD d .nuPhi (Ioo a v ×ˢ Ioo v b)) (𝓝[>] a) (𝓝 0) := by
    simpa only [add_zero] using hfixed.add harea
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [Ioo_mem_nhdsGT hab] with v hv
  rcases ha.eq_or_lt with rfl | ha
  · exact incoming_scalar_transport_zero h hD d hv.1 hv.2
  · exact eq6_10a h hD d ha hv.1 hv.2

/-- The incoming log residual tends to zero at every nonnegative axis
basepoint, including the initial endpoint. -/
theorem representatives_incoming_log_residual_tendsto
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Tendsto (fun v => eVariationOn (bvIncomingLogResidual d.scalarRightFields v a)
      (Ioo a v)) (𝓝[>] a) (𝓝 0) := by
  let c := (a + b) / 2
  have hac : a < c := by dsimp only [c]; linarith only [hab]
  have hcb : c < b := by dsimp only [c]; linarith only [hab]
  have hf := (bv_incoming_log_residual_bv h hD d ha hac.le hcb).mono Ioo_subset_Icc_self
  have hfixed := bv_variation_right_tail_tendsto_zero hac hf
  have harea := bv_area_incoming_closed_rectangle_tendsto h hD d .phiAlphaLam (b := b) ha
  have hsum : Tendsto (fun v =>
      eVariationOn (bvIncomingLogResidual d.scalarRightFields b a) (Ioo a v) +
        bvAnalyticArea h hD d .phiAlphaLam (Ioo a v ×ˢ Icc v b)) (𝓝[>] a) (𝓝 0) := by
    simpa only [add_zero] using hfixed.add harea
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [Ioo_mem_nhdsGT hab] with v hv
  rcases ha.eq_or_lt with rfl | ha
  · exact incoming_log_transport_zero h hD d hv.1 hv.2
  · exact eq6_11a h hD d ha hv.1 hv.2

/-- Both incoming quotient and logarithmic variations tend to zero for
all nonnegative basepoints under the existing universal threshold. -/
theorem representatives_incoming_corner
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (hsmall : D < ENNReal.ofReal epsilonChosen)
    {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun v => eVariationOn (fun t => d.scalarRightFields.beta t v /
      d.scalarRightFields.nu t v) (Ioo a v)) (𝓝[>] a) (𝓝 0) ∧
    Tendsto (fun v => eVariationOn (fun t => Real.log (-d.scalarRightFields.nu t v))
      (Ioo a v)) (𝓝[>] a) (𝓝 0) := by
  have hB (a v : ℝ) (ha : 0 ≤ a) (hav : a < v) :=
    And.intro (SourceInputsWeak.canonical_source_mass_ratio_in_interval_integrable h hD d ha hav)
      (SourceInputsWeak.canonical_source_mass_ratio_in_majorant h hD d ha hav)
  let S := d.scalarRightFields
  let κ := (10 : ℝ) ^ (65 : ℕ) * D.toReal
  have hκ := bv_absorption_coefficient_small hsmall
  have hfin := (bv_corner_variations_finite h hD d).2
  have hQfin : ∀ᶠ v in 𝓝[>] a, eVariationOn (fun t => S.beta t v / S.nu t v)
      (Ioo a v) ≠ ∞ := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact (hfin a v ha hv).1
  have hLfin : ∀ᶠ v in 𝓝[>] a,
      eVariationOn (fun t => Real.log (-S.nu t v)) (Ioo a v) ≠ ∞ := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact (hfin a v ha hv).2
  have hQ : ∀ᶠ v in 𝓝[>] a,
      eVariationOn (fun t => S.beta t v / S.nu t v) (Ioo a v) ≤
        3 * eVariationOn (bvIncomingScalarResidual S v a) (Ioo a v) +
          ENNReal.ofReal κ * eVariationOn (fun t => Real.log (-S.nu t v)) (Ioo a v) := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact bv_incoming_quotient_residual_bound h hD d ha hv
  have hL : ∀ᶠ v in 𝓝[>] a,
      eVariationOn (fun t => Real.log (-S.nu t v)) (Ioo a v) ≤
        eVariationOn (bvIncomingLogResidual S v a) (Ioo a v) +
          ENNReal.ofReal κ * eVariationOn (fun t => S.beta t v / S.nu t v) (Ioo a v) := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hg := bv_incoming_g_bound_of_mass_ratio_majorant h hD d ha hv
      (hB a v ha hv)
    have hh := bv_variation_le_residual_add_integral hv.le hg.1
      (fun x hx y hy hxy => bv_incoming_log_residual_increment h hD d
        ha hx.1.le hxy hy.2)
    have hqfinite := (hfin a v ha hv).1
    have hφq := ENNReal.toReal_mono hqfinite
      (bv_incoming_ratio_variation h hD d ha hv)
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
    (representatives_incoming_scalar_residual_tendsto h hD d ha (lt_add_one a))
    (representatives_incoming_log_residual_tendsto h hD d ha (lt_add_one a))

end ChristodoulouBV

end
