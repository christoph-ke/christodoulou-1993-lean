module

public import ChristodoulouBV.Uniqueness.OutgoingMassTransport
public import ChristodoulouBV.Uniqueness.ExpansionCoeffIntegrals

/-!
# The stable outgoing mass Hardy estimate

The good-v forcing estimate is integrated through the damped mass equation,
then Hardy's inequality controls the weighted mass norm by the outgoing
scalar variation.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The axis-zero damped equation and the good-v forcing bound give the
pointwise mass estimate used in (3.16). The estimate is valid at every
primary-field point because the forcing bound is integrated on a conull set. -/
theorem ComparisonData.mass_out_difference_le_I_goodV
    (D : ComparisonData) (ha : D.a = 0) (hb : D.b = 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 1 ≤ C ∧
      ((∀ u v, (u, v) ∈ triangle D.a D.b →
        ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
          (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀ ∧
          (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε₀) →
        ∀ V u v, D.a < V → V < D.b →
          (u, v) ∈ triangle D.a V →
          |D.S₁.m u v - D.S₂.m u v| ≤
            2 * C ^ 3 * (D.A V + D.L V) * D.I u v) := by
  obtain ⟨ε₀, hε₀, C, hC, hpoint⟩ :=
    D.outgoingMassForcing_goodV_le ha hb
  refine ⟨ε₀, hε₀, C, hC, ?_⟩
  intro hsmall V u v haV hVb huv
  have hfull : (u, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨huv.1, huv.2.1, huv.2.2.trans hVb⟩
  have hlt := huv.2.1
  let M := 2 * C ^ 3 * (D.A V + D.L V)
  have hA := D.A_nonneg V
  have hL := D.L_nonneg haV hVb
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hf : IntegrableOn
      (fun t => |D.S₁.theta u t| + |D.S₂.theta u t|)
      (Ioc u v) volume :=
    integrableOn_of_div_sub_integrable hlt
      (D.theta_sum_div_distance_integrable hfull)
  have hF := (D.outgoingMassForcing_integrable hfull).abs
  have hMF := hf.const_mul M
  have hAE : (fun t => |D.outgoingMassForcing u t|) ≤ᵐ[
      volume.restrict (Ioc u v)]
      (fun t => M * (|D.S₁.theta u t| + |D.S₂.theta u t|)) := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [(D.goodV_properties).1] with t htG ht
    have htT : (u, t) ∈ triangle D.a V :=
      (mem_triangle).2 ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩
    exact hpoint hsmall V u t haV hVb htT htG
  have hle := integral_mono_ae hF hMF hAE
  have hsum : (∫ t in Ioc u v,
      M * (|D.S₁.theta u t| + |D.S₂.theta u t|)) =
      M * D.I u v := by
    rw [← intervalIntegral.integral_of_le hlt.le,
      intervalIntegral.integral_const_mul]
    rfl
  rw [hsum] at hle
  calc
    |D.S₁.m u v - D.S₂.m u v| ≤
        ∫ t in u..v, |D.outgoingMassForcing u t| :=
      D.mass_out_difference_le_integral_forcing hfull
    _ = ∫ t in Ioc u v, |D.outgoingMassForcing u t| :=
      intervalIntegral.integral_of_le hlt.le
    _ ≤ M * D.I u v := hle

/-- The weighted mass difference on a complete outgoing ray is controlled by
the scalar Hardy integral at every compact comparison top. -/
theorem ComparisonData.outgoing_mass_weight_le_I_hardy
    (D : ComparisonData) (ha : D.a = 0) (hb : D.b = 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 1 ≤ C ∧
      ((∀ u v, (u, v) ∈ triangle D.a D.b →
        ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
          (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀ ∧
          (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε₀) →
        ∀ V, D.a < V → V < D.b → ∀ u ∈ Ico D.a V,
          (∫ t in Ioc u V,
            |D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2) ≤
            2 * C ^ 3 * (D.A V + D.L V) *
              (∫ t in u..V, D.I u t / (t - u) ^ 2)) := by
  obtain ⟨ε₀, hε₀, C, hC, hpoint⟩ := D.mass_out_difference_le_I_goodV ha hb
  refine ⟨ε₀, hε₀, C, hC, ?_⟩
  intro hsmall V haV hVb u hu
  have huv : (u, V) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨hu.1, hu.2, hVb⟩
  let M := 2 * C ^ 3 * (D.A V + D.L V)
  have hM : 0 ≤ M := by
    dsimp [M]
    have hA := D.A_nonneg V
    have hL := D.L_nonneg haV hVb
    positivity
  have hmass := D.outgoing_mass_diff_weight_integrable hVb hu
  have hI := (D.I_hardy_le huv).1
  have hMI := hI.const_mul M
  have hae : (fun t =>
      |D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2) ≤ᵐ[
        volume.restrict (Ioc u V)]
      (fun t => M * (D.I u t / (t - u) ^ 2)) := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    have hne : ∀ᵐ t : ℝ ∂volume, t ≠ V := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with t htne ht
    have htV : t < V := lt_of_le_of_ne ht.2 htne
    have htT : (u, t) ∈ triangle D.a V :=
      (mem_triangle).2 ⟨hu.1, ht.1, htV⟩
    have hden : 0 ≤ (t - u) ^ 2 := sq_nonneg _
    have hp := hpoint hsmall V u t haV hVb htT
    dsimp [M]
    calc
      |D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2 ≤
          (2 * C ^ 3 * (D.A V + D.L V) * D.I u t) /
            (t - u) ^ 2 := div_le_div_of_nonneg_right hp hden
      _ = 2 * C ^ 3 * (D.A V + D.L V) *
          (D.I u t / (t - u) ^ 2) := by ring
  have hle := integral_mono_ae hmass hMI hae
  have hIeq : (∫ t in Ioc u V, D.I u t / (t - u) ^ 2) =
      (∫ t in u..V, D.I u t / (t - u) ^ 2) :=
    (intervalIntegral.integral_of_le hu.2.le).symm
  rw [integral_const_mul, hIeq] at hle
  exact hle

/-- Stable replacement for (3.16): the outgoing weighted mass norm is
small compared with the good-ray scalar and radius norms. The coefficient
threshold and the final constant are fixed before the variation parameter
and are uniform as the compact top approaches the open top. -/
theorem ComparisonData.Gamma_le_epsilon_A_L
    (D : ComparisonData) (ha : D.a = 0) (hb : D.b = 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ε : ℝ, 0 ≤ ε →
      (∀ u v, (u, v) ∈ triangle D.a D.b →
        ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
          (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀ ∧
          (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε₀) →
      (∀ u v, (u, v) ∈ triangle D.a D.b →
        (eVariationOn (D.S₁.phi u) (Ioc u v)).toReal ≤ ε ∧
        (eVariationOn (D.S₂.phi u) (Ioc u v)).toReal ≤ ε) →
      ∀ V, D.a < V → V < D.b →
        (D.Gamma V).toReal ≤ C * ε * (D.A V + D.L V) := by
  obtain ⟨ε₀, hε₀, C₀, hC₀, hray⟩ :=
    D.outgoing_mass_weight_le_I_hardy ha hb
  obtain ⟨K, hK, hHardy⟩ := D.I_hardy_le_small_variation
  refine ⟨ε₀, hε₀, 2 * C₀ ^ 3 * K, ?_, ?_⟩
  · positivity
  intro ε hε hsmall hvar V haV hVb
  have hA : 0 ≤ D.A V := D.A_nonneg V
  have hL : 0 ≤ D.L V := D.L_nonneg haV hVb
  have hM : 0 ≤ 2 * C₀ ^ 3 * (D.A V + D.L V) := by positivity
  have htarget : 0 ≤ 2 * C₀ ^ 3 * K * ε * (D.A V + D.L V) := by
    positivity
  have hbound : ∀ u ∈ Ico D.a V,
      (∫ t in Ioc u V,
        |D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2) ≤
        2 * C₀ ^ 3 * K * ε * (D.A V + D.L V) := by
    intro u hu
    have huv : (u, V) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨hu.1, hu.2, hVb⟩
    calc
      (∫ t in Ioc u V,
          |D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2) ≤
          2 * C₀ ^ 3 * (D.A V + D.L V) *
            (∫ t in u..V, D.I u t / (t - u) ^ 2) :=
        hray hsmall V haV hVb u hu
      _ ≤ 2 * C₀ ^ 3 * (D.A V + D.L V) * (K * ε) :=
        mul_le_mul_of_nonneg_left (hHardy ε hε hvar u V huv) hM
      _ = 2 * C₀ ^ 3 * K * ε * (D.A V + D.L V) := by ring
  have hGamma : D.Gamma V ≤
      ENNReal.ofReal (2 * C₀ ^ 3 * K * ε * (D.A V + D.L V)) := by
    unfold ComparisonData.Gamma
    apply iSup_le
    intro u
    apply iSup_le
    intro hu
    have hint := D.outgoing_mass_diff_weight_integrable hVb hu
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc u V)]
        (fun t => |D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2) := by
      apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro t _
      exact div_nonneg (abs_nonneg _) (sq_nonneg _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
    exact ENNReal.ofReal_le_ofReal (hbound u hu)
  have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hGamma
  simpa only [ENNReal.toReal_ofReal htarget] using htoReal

end ChristodoulouBV.Uniqueness

end
