module

public import ChristodoulouBV.Uniqueness.UniformThresholdOutgoingCoeffIntegral
public import ChristodoulouBV.Uniqueness.ExpansionCoeffIntegrals

/-!
# Uniform outgoing coefficient difference integral

The integrated pointwise comparison uses coefficient and variation numbers
fixed by one package before the normalized data are selected.
-/

@[expose] public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- One constant controls the outgoing
absolute coefficient difference by `L + Γ` uniformly in the compact top. -/
theorem UniformThresholdBounds.nuCoeff_difference_integral_uniform
    (P : UniformThresholdBounds) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        P.VariationHoldsOne D.U₁ D.S₁ →
        P.VariationHoldsOne D.U₂ D.S₂ →
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ P.gapThreshold) →
        ∀ V, D.a < V → V < D.b →
          ∀ u ∈ Ico D.a V,
            (∫ t in u..V,
              |IsBVSolution.nuCoeff D.S₁ u t -
                IsBVSolution.nuCoeff D.S₂ u t|) ≤
              C * (D.L V + (D.Gamma V).toReal)) := by
  obtain ⟨C₁, hC₁, hpoint⟩ := P.expansion_coefficient_pointwise_uniform
  obtain ⟨M, hM, hcoeff⟩ := P.nuCoeff_integral_uniform_pair
  let F := C₁ ^ 2 + (C₁ ^ 2) ^ 2 + (C₁ ^ 2) ^ 4
  let B := 2 * (C₁ ^ 2) ^ 5
  let C := max (F * M) B + 1
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 1 ≤ C := by
    dsimp [C]
    have : 0 ≤ F * M := mul_nonneg hF hM
    linarith [le_max_left (F * M) B]
  refine ⟨C, hC, ?_⟩
  intro D ha hb hP hvar₁ hvar₂ hsmall V haV hVb u hu
  have hL : 0 ≤ D.L V := D.L_nonneg haV hVb
  have hΓ : 0 ≤ (D.Gamma V).toReal := ENNReal.toReal_nonneg
  have hK₁ : IntegrableOn (IsBVSolution.nuCoeff D.S₁ u) (Ioc u V) := by
    have hp := D.hT ((mem_triangle).2 ⟨hu.1, hu.2, hVb⟩)
    obtain ⟨Q, _, hQ⟩ := D.h₁.exists_theta_div_lam_bound_out hp.1
    exact D.h₁.nu_coeff_integrable_axis hp.1 hQ
  have hK₂ : IntegrableOn (IsBVSolution.nuCoeff D.S₂ u) (Ioc u V) := by
    have hp := D.hT ((mem_triangle).2 ⟨hu.1, hu.2, hVb⟩)
    obtain ⟨Q, _, hQ⟩ := D.h₂.exists_theta_div_lam_bound_out hp.2
    exact D.h₂.nu_coeff_integrable_axis hp.2 hQ
  have hdiff := D.nuCoeff_difference_integrable hVb hu
  have hmass := D.outgoing_mass_diff_weight_integrable hVb hu
  let mass : ℝ → ℝ := fun t =>
    |D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2
  have hRhs : IntegrableOn
      (fun t => F * D.L V * IsBVSolution.nuCoeff D.S₂ u t + B * mass t)
      (Ioc u V) volume :=
    (hK₂.const_mul (F * D.L V)).add (hmass.const_mul B)
  have hae : ∀ᵐ t ∂volume.restrict (Ioc u V),
      |IsBVSolution.nuCoeff D.S₁ u t -
        IsBVSolution.nuCoeff D.S₂ u t| ≤
      F * D.L V * IsBVSolution.nuCoeff D.S₂ u t + B * mass t := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    have hne : ∀ᵐ t : ℝ ∂volume, t ≠ V := by
      simp [ae_iff, measure_singleton]
    filter_upwards [(D.goodV_properties).1, hne] with t htG htne ht
    have htt : (u, t) ∈ triangle D.a V :=
      (mem_triangle).2 ⟨hu.1, ht.1, lt_of_le_of_ne ht.2 htne⟩
    exact (hpoint D ha hb hP hsmall V haV hVb u t htt htG).1
  have hle := integral_mono_ae hdiff hRhs hae
  have hsum : (∫ t in Ioc u V,
      F * D.L V * IsBVSolution.nuCoeff D.S₂ u t + B * mass t) =
      F * D.L V * (∫ t in Ioc u V,
        IsBVSolution.nuCoeff D.S₂ u t) +
      B * (∫ t in Ioc u V, mass t) := by
    rw [integral_add (hK₂.const_mul (F * D.L V))
      (hmass.const_mul B), integral_const_mul, integral_const_mul]
  have hKbound : (∫ t in Ioc u V,
      IsBVSolution.nuCoeff D.S₂ u t) ≤ M := by
    simpa only [intervalIntegral.integral_of_le hu.2.le] using
      (hcoeff D ha hb hP hvar₁ hvar₂ V haV hVb u hu).2
  have hmassbound : (∫ t in Ioc u V, mass t) ≤
      (D.Gamma V).toReal := D.outgoing_mass_diff_integral_le_Gamma haV hVb hu
  have hFM : F * M ≤ C := by
    dsimp [C]
    linarith [le_max_left (F * M) B]
  have hBC : B ≤ C := by dsimp [C]; linarith [le_max_right (F * M) B]
  have hstep₁ := mul_le_mul_of_nonneg_left hKbound (mul_nonneg hF hL)
  have hstep₂ := mul_le_mul_of_nonneg_left hmassbound hB
  have hstep₃ := mul_le_mul_of_nonneg_right hFM hL
  have hstep₄ := mul_le_mul_of_nonneg_right hBC hΓ
  rw [intervalIntegral.integral_of_le hu.2.le]
  calc
    (∫ t in Ioc u V,
      |IsBVSolution.nuCoeff D.S₁ u t -
        IsBVSolution.nuCoeff D.S₂ u t|) ≤
      F * D.L V * (∫ t in Ioc u V,
        IsBVSolution.nuCoeff D.S₂ u t) +
      B * (∫ t in Ioc u V, mass t) := by rw [← hsum]; exact hle
    _ ≤ F * D.L V * M + B * (D.Gamma V).toReal := by linarith
    _ ≤ C * (D.L V + (D.Gamma V).toReal) := by nlinarith


end ChristodoulouBV.Uniqueness

end
