module

public import ChristodoulouBV.Uniqueness.RadiusScalarBase

/-!
# Corrected incoming scalar difference

The incoming scalar primitive gives an absolute-value inequality with the
negative radius correction retained in the underlying identity.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- Corrected absolute incoming scalar estimate (3.6b). Its integrands are
genuine integrable functions; no small-variation assumption or representative
choice is needed. -/
theorem ComparisonData.phi_diff_incoming_abs_le (D : ComparisonData)
    (ha : D.a = 0) (hb : D.b = 1)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    |D.S₁.phi u v - D.S₂.phi u v| ≤
      (∫ s in u..v, |D.S₁.nu s v| *
        |D.S₁.beta s v / D.S₁.nu s v -
          D.S₂.beta s v / D.S₂.nu s v|) / D.S₁.r u v +
      (∫ s in u..v, |D.S₂.beta s v / D.S₂.nu s v| *
        |D.S₁.nu s v - D.S₂.nu s v|) / D.S₁.r u v +
      |D.S₁.r u v - D.S₂.r u v| / D.S₁.r u v *
        |D.S₂.phi u v| := by
  let f : ℝ → ℝ := fun s => |D.S₁.nu s v| *
    |D.S₁.beta s v / D.S₁.nu s v -
      D.S₂.beta s v / D.S₂.nu s v|
  let g : ℝ → ℝ := fun s => |D.S₂.beta s v / D.S₂.nu s v| *
    |D.S₁.nu s v - D.S₂.nu s v|
  have hT₁ : triangle D.a D.b ⊆ D.U₁ := fun p hp => (D.hT hp).1
  have hT₂ : triangle D.a D.b ⊆ D.U₂ := fun p hp => (D.hT hp).2
  have hβ₁ := beta_integrable_incoming_axis_of_triangle D.h₁ hT₁ huv
  have hβ₂ := beta_integrable_incoming_axis_of_triangle D.h₂ hT₂ huv
  have hν₁ := D.h₁.nu_integrable_incoming_axis_of_triangle hT₁ huv
  have hν₂ := D.h₂.nu_integrable_incoming_axis_of_triangle hT₂ huv
  have hab : u ≤ v := huv.2.1.le
  have hβ₁on := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hβ₁
  have hβ₂on := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hβ₂
  have hν₁on := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hν₁
  have hν₂on := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hν₂
  have hq₁ae : AEStronglyMeasurable
      (fun s => D.S₁.beta s v / D.S₁.nu s v)
      (volume.restrict (Ioc u v)) :=
    hβ₁on.aestronglyMeasurable.div₀ hν₁on.aestronglyMeasurable
  have hq₂ae : AEStronglyMeasurable
      (fun s => D.S₂.beta s v / D.S₂.nu s v)
      (volume.restrict (Ioc u v)) :=
    hβ₂on.aestronglyMeasurable.div₀ hν₂on.aestronglyMeasurable
  have hfae : AEStronglyMeasurable f
      (volume.restrict (Ioc u v)) := by
    have hh := hν₁on.aestronglyMeasurable.norm.mul
      (hq₁ae.sub hq₂ae).norm
    convert hh using 1
  have hgae : AEStronglyMeasurable g
      (volume.restrict (Ioc u v)) := by
    have hh := hq₂ae.norm.mul
      (hν₁on.aestronglyMeasurable.sub hν₂on.aestronglyMeasurable).norm
    convert hh using 1
  have hw : (D.a, (1 / 2 : ℝ)) ∈ triangle D.a D.b := by
    rw [ha, hb]
    exact initial_edge_of_triangle (by norm_num) (by norm_num)
  have href : (0, (1 / 2 : ℝ)) ∈ D.U₁ ∩ D.U₂ := by
    simpa only [ha] using D.hT hw
  have hdatum : D.S₁.phi 0 (1 / 2 : ℝ) = D.S₂.phi 0 (1 / 2 : ℝ) := by
    have hh := (D.hdata (1 / 2 : ℝ) (by rw [ha, hb]; constructor <;> norm_num)).2
    simpa only [ha] using hh
  obtain ⟨c, C, hc, hC, hcoeff⟩ :=
    D.h₁.preloc_coefficient_bounds D.h₂ href hdatum
  let K := C + C * C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let Q := K / c
  have hQ : 0 ≤ Q := div_nonneg hK hc.le
  have hfield (s : ℝ) (hs : s ∈ Ico u v)
      (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :=
    hcoeff D.a D.b s v D.hT
      ((mem_triangle).2 ⟨huv.1.trans hs.1, hs.2, huv.2.2⟩) S hS
  have hqbound (s : ℝ) (hs : s ∈ Ico u v)
      (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :
      |S.beta s v / S.nu s v| ≤ Q := by
    rcases hfield s hs S hS with
      ⟨_, _, hnuLo, hnuHi, hphi, _, hzeta⟩
    have hbeta : |S.beta s v| ≤ K := by
      have heq : S.beta s v = S.zeta s v + S.nu s v * S.phi s v := by
        dsimp [Fields.zeta]; ring
      rw [heq]
      calc
        |S.zeta s v + S.nu s v * S.phi s v| ≤
            |S.zeta s v| + |S.nu s v| * |S.phi s v| := by
          simpa only [abs_mul] using
            (abs_add_le (S.zeta s v) (S.nu s v * S.phi s v))
        _ ≤ C + C * C := by
          apply add_le_add hzeta
          exact (mul_le_mul_of_nonneg_right hnuHi (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hphi hC)
        _ = K := rfl
    rw [abs_div]
    have hpos : 0 < |S.nu s v| := hc.trans_le hnuLo
    apply (div_le_div_iff₀ hpos hc).2
    exact (mul_le_mul_of_nonneg_right hbeta hc.le).trans
      (mul_le_mul_of_nonneg_left hnuLo hK)
  have hfgbound (s : ℝ) (hs : s ∈ Ico u v) :
      |f s| ≤ 2 * C * Q ∧ |g s| ≤ 2 * C * Q := by
    have hn₁ := (hfield s hs D.S₁ (Or.inl rfl)).2.2.2.1
    have hn₂ := (hfield s hs D.S₂ (Or.inr rfl)).2.2.2.1
    have hq₁ := hqbound s hs D.S₁ (Or.inl rfl)
    have hq₂ := hqbound s hs D.S₂ (Or.inr rfl)
    have hqdiff : |D.S₁.beta s v / D.S₁.nu s v -
        D.S₂.beta s v / D.S₂.nu s v| ≤ 2 * Q := by
      calc
        _ ≤ |D.S₁.beta s v / D.S₁.nu s v| +
            |D.S₂.beta s v / D.S₂.nu s v| := abs_sub _ _
        _ ≤ Q + Q := add_le_add hq₁ hq₂
        _ = 2 * Q := by ring
    have hnudiff : |D.S₁.nu s v - D.S₂.nu s v| ≤ 2 * C := by
      calc
        _ ≤ |D.S₁.nu s v| + |D.S₂.nu s v| := abs_sub _ _
        _ ≤ C + C := add_le_add hn₁ hn₂
        _ = 2 * C := by ring
    constructor
    · dsimp [f]
      rw [abs_mul, abs_abs, abs_abs]
      exact (mul_le_mul_of_nonneg_left hqdiff (abs_nonneg _)).trans
        (by nlinarith [mul_nonneg hC hQ])
    · dsimp [g]
      rw [abs_mul, abs_abs, abs_abs]
      exact (mul_le_mul_of_nonneg_left hnudiff (abs_nonneg _)).trans
        (by nlinarith [mul_nonneg hC hQ])
  have hmeasure : volume (Ioc u v) < ⊤ :=
    (measure_mono Ioc_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top
  have haeV : ∀ᵐ s : ℝ ∂volume.restrict (Ioc u v), s ≠ v := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    have hne : ∀ᵐ s : ℝ ∂volume, s ≠ v := by simp [ae_iff]
    filter_upwards [hne] with s hs _
    exact hs
  have hfon : IntegrableOn f (Ioc u v) volume := by
    apply IntegrableOn.of_bound hmeasure hfae (2 * C * Q)
    filter_upwards [ae_restrict_mem measurableSet_Ioc, haeV] with s hs hsne
    have hmem : s ∈ Ico u v := ⟨hs.1.le, lt_of_le_of_ne hs.2 hsne⟩
    simpa only [Real.norm_eq_abs] using (hfgbound s hmem).1
  have hgon : IntegrableOn g (Ioc u v) volume := by
    apply IntegrableOn.of_bound hmeasure hgae (2 * C * Q)
    filter_upwards [ae_restrict_mem measurableSet_Ioc, haeV] with s hs hsne
    have hmem : s ∈ Ico u v := ⟨hs.1.le, lt_of_le_of_ne hs.2 hsne⟩
    simpa only [Real.norm_eq_abs] using (hfgbound s hmem).2
  have hfint : IntervalIntegrable f volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hfon
  have hgint : IntervalIntegrable g volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hgon
  have hβdiff : IntervalIntegrable
      (fun s => D.S₁.beta s v - D.S₂.beta s v) volume u v :=
    hβ₁.sub hβ₂
  have hpoint (s : ℝ) (hs : s ∈ Ico u v) :
      |D.S₁.beta s v - D.S₂.beta s v| ≤ f s + g s := by
    have heq := D.beta_diff_quotient_identity
      ((mem_triangle).2 ⟨huv.1.trans hs.1, hs.2, huv.2.2⟩)
    rw [heq]
    dsimp [f, g]
    simpa only [abs_mul] using
      (abs_add_le
        (D.S₁.nu s v * (D.S₁.beta s v / D.S₁.nu s v -
          D.S₂.beta s v / D.S₂.nu s v))
        ((D.S₂.beta s v / D.S₂.nu s v) *
          (D.S₁.nu s v - D.S₂.nu s v)))
  have hpointAE : ∀ᵐ s ∂volume.restrict (Ioc u v),
      |D.S₁.beta s v - D.S₂.beta s v| ≤ f s + g s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, haeV] with s hs hsne
    have hmem : s ∈ Ico u v := ⟨hs.1.le, lt_of_le_of_ne hs.2 hsne⟩
    exact hpoint s hmem
  have habsint : IntervalIntegrable
      (fun s => |D.S₁.beta s v - D.S₂.beta s v|) volume u v :=
    hβdiff.abs
  have hIntLe : |∫ s in u..v, D.S₁.beta s v - D.S₂.beta s v| ≤
      (∫ s in u..v, f s) + (∫ s in u..v, g s) := by
    calc
      |∫ s in u..v, D.S₁.beta s v - D.S₂.beta s v| ≤
          ∫ s in u..v, |D.S₁.beta s v - D.S₂.beta s v| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ s in u..v, f s + g s := by
        rw [intervalIntegral.integral_of_le hab,
          intervalIntegral.integral_of_le hab]
        exact integral_mono_ae
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp habsint)
          (hfon.add hgon) hpointAE
      _ = (∫ s in u..v, f s) + (∫ s in u..v, g s) :=
        intervalIntegral.integral_add hfint hgint
  have hp := D.hT huv
  have hr : 0 < D.S₁.r u v := D.h₁.solution.radius_pos (u, v) hp.1
  have hidentity := D.phi_diff_incoming_density_identity huv
  rw [hidentity]
  have hfirst : |-(∫ s in u..v, D.S₁.beta s v - D.S₂.beta s v) /
      D.S₁.r u v| ≤
      (∫ s in u..v, f s) / D.S₁.r u v +
        (∫ s in u..v, g s) / D.S₁.r u v := by
    rw [abs_div, abs_neg, abs_of_pos hr]
    calc
      |∫ s in u..v, D.S₁.beta s v - D.S₂.beta s v| /
          D.S₁.r u v ≤
          ((∫ s in u..v, f s) + (∫ s in u..v, g s)) /
            D.S₁.r u v :=
        div_le_div_of_nonneg_right hIntLe hr.le
      _ = (∫ s in u..v, f s) / D.S₁.r u v +
          (∫ s in u..v, g s) / D.S₁.r u v := add_div _ _ _
  have hsecond : |(D.S₁.r u v - D.S₂.r u v) /
      D.S₁.r u v * D.S₂.phi u v| =
      |D.S₁.r u v - D.S₂.r u v| / D.S₁.r u v *
        |D.S₂.phi u v| := by
    rw [abs_mul, abs_div, abs_of_pos hr]
  calc
    |-(∫ s in u..v, D.S₁.beta s v - D.S₂.beta s v) /
        D.S₁.r u v -
      (D.S₁.r u v - D.S₂.r u v) /
        D.S₁.r u v * D.S₂.phi u v| ≤
      |-(∫ s in u..v, D.S₁.beta s v - D.S₂.beta s v) /
        D.S₁.r u v| +
      |(D.S₁.r u v - D.S₂.r u v) /
        D.S₁.r u v * D.S₂.phi u v| := abs_sub _ _
    _ ≤ (∫ s in u..v, f s) / D.S₁.r u v +
        (∫ s in u..v, g s) / D.S₁.r u v +
      |D.S₁.r u v - D.S₂.r u v| /
        D.S₁.r u v * |D.S₂.phi u v| := by
      rw [hsecond]
      exact add_le_add hfirst le_rfl

end ChristodoulouBV.Uniqueness

end
