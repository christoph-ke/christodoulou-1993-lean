module

public import ChristodoulouBV.Existence.BVBasicRatios
import Mathlib.Tactic

/-!
# Axis-based weighted means for the canonical fields

The bounded-density endpoint lemmas for the source estimates justify the improper axis
integrals. Thus the ratio variation estimates concern the actual
weighted averages of the canonical representatives.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

/-- Universal small bounds for the two invariant normalized derivatives.
These are the shift-invariant amplitude inputs to the later residual
estimates; neither bound contains a scalar offset. -/
theorem bv_weighted_ratio_bounds
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain,
      |d.scalarRightFields.theta p.1 p.2 / d.scalarRightFields.lam p.1 p.2| ≤
        15 * D.toReal ∧
      |d.scalarRightFields.zeta p.1 p.2 / d.scalarRightFields.nu p.1 p.2| ≤
        24 * D.toReal := by
  intro p hp
  obtain ⟨hθ, hζ⟩ := bv_invariant_amplitudes h hD d p hp
  obtain ⟨hl0, _, hn0, _, _⟩ := scalar_right_fields_geometry h hD d p hp
  have hlpos : 0 < d.scalarRightFields.lam p.1 p.2 := by linarith only [hl0]
  have hnpos : 0 < -d.scalarRightFields.nu p.1 p.2 := by linarith only [hn0]
  constructor
  · rw [abs_div, abs_of_pos hlpos, div_le_iff₀ hlpos]
    have hm := mul_le_mul_of_nonneg_left hl0
      (show 0 ≤ 15 * D.toReal by positivity)
    nlinarith only [hm, hθ]
  · rw [abs_div, abs_of_neg (neg_pos.mp hnpos), div_le_iff₀ hnpos]
    have hm := mul_le_mul_of_nonneg_left hn0
      (show 0 ≤ 24 * D.toReal by positivity)
    nlinarith only [hm, hζ]

/-- One fixed scalar center works for the whole limit, with universal
amplitudes for the scalar and both normalized derivatives. No further
subsequence or convergence of the smooth centering constants is needed. -/
theorem bv_normalized_amplitudes
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∃ c : ℝ, ∀ p ∈ globalDomain,
      |d.scalarRightFields.phi p.1 p.2 - c| ≤ 12 * D.toReal ∧
      |d.scalarRightFields.alpha p.1 p.2 / d.scalarRightFields.lam p.1 p.2 - c| ≤
        27 * D.toReal ∧
      |d.scalarRightFields.beta p.1 p.2 / d.scalarRightFields.nu p.1 p.2 - c| ≤
        36 * D.toReal := by
  have href : ((0 : ℝ), (1 : ℝ)) ∈ globalDomain := ⟨le_rfl, zero_lt_one⟩
  refine ⟨d.scalarRightFields.phi 0 1, ?_⟩
  intro p hp
  have hlim := ((d.scalar_locally_uniform h).tendsto_at hp).sub
    ((d.scalar_locally_uniform h).tendsto_at href)
  have hphi : |d.scalarRightFields.phi p.1 p.2 - d.scalarRightFields.phi 0 1| ≤
      12 * D.toReal := by
    apply le_of_tendsto hlim.abs
    apply Eventually.of_forall
    intro n
    have hp' := (h (d.subsequence n)).amplitudes.centered_phi p hp
    have hq' := (h (d.subsequence n)).amplitudes.centered_phi (0, 1) href
    have he : (T (d.subsequence n)).phi p.1 p.2 - (T (d.subsequence n)).phi 0 1 =
        (smoothCenteredFields (T (d.subsequence n))).phi p.1 p.2 -
          (smoothCenteredFields (T (d.subsequence n))).phi 0 1 := by
      simp only [smoothCenteredFields, scalarShift]
      ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith only [hp', hq'])
  obtain ⟨hθ, hζ⟩ := bv_weighted_ratio_bounds h hD d p hp
  obtain ⟨hl0, _, hn0, _, _⟩ := scalar_right_fields_geometry h hD d p hp
  have hl : d.scalarRightFields.lam p.1 p.2 ≠ 0 := by linarith only [hl0]
  have hn : d.scalarRightFields.nu p.1 p.2 ≠ 0 := by linarith only [hn0]
  refine ⟨hphi, ?_, ?_⟩
  · have he : d.scalarRightFields.alpha p.1 p.2 / d.scalarRightFields.lam p.1 p.2 -
        d.scalarRightFields.phi 0 1 =
        d.scalarRightFields.theta p.1 p.2 / d.scalarRightFields.lam p.1 p.2 +
          (d.scalarRightFields.phi p.1 p.2 - d.scalarRightFields.phi 0 1) := by
      dsimp only [Fields.theta]
      field_simp [hl]
      ring
    rw [he]
    exact (abs_add_le _ _).trans (by linarith only [hθ, hphi])
  · have he : d.scalarRightFields.beta p.1 p.2 / d.scalarRightFields.nu p.1 p.2 -
        d.scalarRightFields.phi 0 1 =
        d.scalarRightFields.zeta p.1 p.2 / d.scalarRightFields.nu p.1 p.2 +
          (d.scalarRightFields.phi p.1 p.2 - d.scalarRightFields.phi 0 1) := by
      dsimp only [Fields.zeta]
      field_simp [hn]
      ring
    rw [he]
    exact (abs_add_le _ _).trans (by linarith only [hζ, hphi])

private theorem canonical_density_bounds
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ p ∈ globalDomain,
      |d.scalarRightFields.lam p.1 p.2| ≤ 1 ∧
      |d.scalarRightFields.nu p.1 p.2| ≤ 1 ∧
      |d.scalarRightFields.alpha p.1 p.2| ≤ 12 * D.toReal + 2 * C ∧
      |d.scalarRightFields.beta p.1 p.2| ≤ 12 * D.toReal + 2 * C := by
  intro p hp
  obtain ⟨hl0, hl1, hn0, hn1, _⟩ := scalar_right_fields_geometry h hD d p hp
  have hlpos : 0 < d.scalarRightFields.lam p.1 p.2 := by linarith only [hl0]
  have hnneg : d.scalarRightFields.nu p.1 p.2 < 0 := by linarith only [hn0]
  have hl : |d.scalarRightFields.lam p.1 p.2| ≤ 1 := by
    rw [abs_of_pos hlpos]
    linarith only [hl1]
  have hn : |d.scalarRightFields.nu p.1 p.2| ≤ 1 := by
    rw [abs_of_neg hnneg]
    linarith only [hn1]
  obtain ⟨hα, hβ⟩ := bv_ratio_amplitudes h hD d p hp
  refine ⟨hl, hn, ?_, ?_⟩
  · calc
      _ = |d.scalarRightFields.lam p.1 p.2| *
          |d.scalarRightFields.alpha p.1 p.2 / d.scalarRightFields.lam p.1 p.2| := by
        rw [← abs_mul, mul_div_cancel₀ _ hlpos.ne']
      _ ≤ 1 * (12 * D.toReal + 2 * C) :=
        mul_le_mul hl hα (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  · calc
      _ = |d.scalarRightFields.nu p.1 p.2| *
          |d.scalarRightFields.beta p.1 p.2 / d.scalarRightFields.nu p.1 p.2| := by
        rw [← abs_mul, mul_div_cancel₀ _ hnneg.ne]
      _ ≤ 1 * (12 * D.toReal + 2 * C) :=
        mul_le_mul hn hβ (abs_nonneg _) zero_le_one
      _ = _ := one_mul _

/-- Both canonical scalar values are the weighted means of the normalized
scalar derivatives from the axis. The incoming formula uses the signed
weight `ν`; both numerator and denominator have the same sign change.
This supplies the weighted identities for the scalar quotient variation estimates. -/
theorem bv_weighted_mean_identities
    {a : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∀ u v, (u, v) ∈ globalDomain →
      d.scalarRightFields.phi u v =
        (∫ t in u..v, d.scalarRightFields.lam u t *
          (d.scalarRightFields.alpha u t / d.scalarRightFields.lam u t)) /
          (∫ t in u..v, d.scalarRightFields.lam u t) ∧
      d.scalarRightFields.phi u v =
        (∫ t in u..v, d.scalarRightFields.nu t v *
          (d.scalarRightFields.beta t v / d.scalarRightFields.nu t v)) /
          (∫ t in u..v, d.scalarRightFields.nu t v) := by
  intro u v hp
  let S := d.scalarRightFields
  have H := transport_limit_is_solution h hD d
  have hb := canonical_density_bounds h hD d
  have hM : 0 ≤ 12 * D.toReal + 2 * C := by
    have := (h 0).offset_nonneg
    positivity
  have hout {x : ℝ} (hx : x ∈ Ioc u v) : outSeg u x v ⊆ globalDomain := by
    rintro ⟨s, t⟩ ⟨rfl, ht⟩
    exact ⟨hp.1, hx.1.trans_le ht.1⟩
  have hin {x : ℝ} (hx : x ∈ Ico u v) : inSeg v u x ⊆ globalDomain := by
    rintro ⟨s, t⟩ ⟨hs, rfl⟩
    exact ⟨hp.1.trans hs.1, hs.2.trans_lt hx.2⟩
  have hli : IntervalIntegrable (S.lam u) volume u v :=
    IsBVSolution.interval_integrable_of_bounded_left hp.2 zero_le_one
      (fun _ hx => (H.radius_out u _ v hx.2 (hout hx)).1)
      (fun t ht => (hb (u, t) ⟨hp.1, ht.1⟩).1)
  have hni : IntervalIntegrable (fun t => S.nu t v) volume u v :=
    IsBVSolution.interval_integrable_of_bounded_right hp.2 zero_le_one
      (fun _ hx => (H.radius_in v u _ hx.1 (hin hx)).1)
      (fun t ht => (hb (t, v) ⟨hp.1.trans ht.1, ht.2⟩).2.1)
  have hαi : IntervalIntegrable (S.alpha u) volume u v :=
    IsBVSolution.interval_integrable_of_bounded_left hp.2 hM
      (fun _ hx => (H.scalar_radius_out u _ v hx.2 (hout hx)).1)
      (fun t ht => (hb (u, t) ⟨hp.1, ht.1⟩).2.2.1)
  have hβi : IntervalIntegrable (fun t => S.beta t v) volume u v :=
    IsBVSolution.interval_integrable_of_bounded_right hp.2 hM
      (fun _ hx => (H.scalar_radius_in v u _ hx.1 (hin hx)).1)
      (fun t ht => (hb (t, v) ⟨hp.1.trans ht.1, ht.2⟩).2.2.2)
  have hr0 : Tendsto (fun t => d.radius (u, t)) (𝓝[>] u) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => d.radius (u, t)) :=
      d.radius_continuous.comp (continuous_const.prodMk continuous_id)
    have ht := hc.tendsto u
    rw [d.radius_axis h hp.1] at ht
    exact ht.mono_left inf_le_left
  have hN0 : Tendsto (fun t => d.scalarRadius (u, t)) (𝓝[>] u) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => d.scalarRadius (u, t)) :=
      d.scalarRadius_continuous.comp (continuous_const.prodMk continuous_id)
    have ht := hc.tendsto u
    rw [d.scalarRadius_axis h hp.1] at ht
    exact ht.mono_left inf_le_left
  have hr1 : Tendsto (fun t => d.radius (t, v)) (𝓝[<] v) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => d.radius (t, v)) :=
      d.radius_continuous.comp (continuous_id.prodMk continuous_const)
    have ht := hc.tendsto v
    rw [d.radius_axis h (hp.1.trans hp.2.le)] at ht
    exact ht.mono_left inf_le_left
  have hN1 : Tendsto (fun t => d.scalarRadius (t, v)) (𝓝[<] v) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => d.scalarRadius (t, v)) :=
      d.scalarRadius_continuous.comp (continuous_id.prodMk continuous_const)
    have ht := hc.tendsto v
    rw [d.scalarRadius_axis h (hp.1.trans hp.2.le)] at ht
    exact ht.mono_left inf_le_left
  have hrout := IsBVSolution.primitive_eq_integral_of_left_trace hp.2 hli
    (fun x hx => H.radius_out u x v hx.2.le (hout ⟨hx.1, hx.2.le⟩)) hr0
  have hrin := IsBVSolution.primitive_eq_integral_of_right_trace hp.2 hni
    (fun x hx => H.radius_in v u x hx.1.le (hin ⟨hx.1.le, hx.2⟩)) hr1
  have hNout := IsBVSolution.primitive_eq_integral_of_left_trace hp.2 hαi
    (fun x hx => (right_scalar_radius_primitive_limit h hD d).1 u x v hx.2.le
      (hout ⟨hx.1, hx.2.le⟩)) hN0
  have hNin := IsBVSolution.primitive_eq_integral_of_right_trace hp.2 hβi
    (fun x hx => (right_scalar_radius_primitive_limit h hD d).2 v u x hx.1.le
      (hin ⟨hx.1.le, hx.2⟩)) hN1
  change d.radius (u, v) = ∫ t in u..v, S.lam u t at hrout
  change d.radius (u, v) = -(∫ t in u..v, S.nu t v) at hrin
  have hlint : (∫ t in u..v, S.lam u t * (S.alpha u t / S.lam u t)) =
      ∫ t in u..v, S.alpha u t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with t ht
    rw [uIoc_of_le hp.2.le] at ht
    exact mul_div_cancel₀ _ (H.lam_pos (u, t) ⟨hp.1, ht.1⟩).ne'
  have hnint : (∫ t in u..v, S.nu t v * (S.beta t v / S.nu t v)) =
      ∫ t in u..v, S.beta t v := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume v] with t hne ht
    rw [uIoc_of_le hp.2.le] at ht
    have ht' : (t, v) ∈ globalDomain :=
      ⟨hp.1.trans ht.1.le, lt_of_le_of_ne ht.2 hne⟩
    have hn0 := (scalar_right_fields_geometry h hD d (t, v) ht').2.2.1
    have hn : S.nu t v ≠ 0 := by linarith only [hn0]
    exact mul_div_cancel₀ _ hn
  constructor
  · rw [hlint, ← hrout, ← hNout]
    rfl
  · rw [hnint, show (∫ t in u..v, S.nu t v) = -d.radius (u, v) by
        linarith only [hrin],
      show (∫ t in u..v, S.beta t v) = -d.scalarRadius (u, v) by linarith only [hNin],
      neg_div_neg_eq]
    rfl

end ChristodoulouBV

end
