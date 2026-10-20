module

public import ChristodoulouBV.Uniqueness.ExpansionCoeffUniformPointwise

/-!
# Uniform integrals of expansion coefficient differences

The coefficient differences are integrated only on their characteristic
carriers. The common good set is conull, and the weighted mass norms retain
their half-open axis endpoints.
-/

@[expose] public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- The good-ray outgoing expansion norm is nonnegative on a nontrivial
compact top. -/
theorem ComparisonData.L_nonneg (D : ComparisonData)
    {V : ℝ} (haV : D.a < V) (hVb : V < D.b) :
    0 ≤ D.L V := by
  let v := (D.a + V) / 2
  have hv : (D.a, v) ∈ triangle D.a V :=
    (mem_triangle).2 ⟨le_rfl, by dsimp [v]; linarith,
      by dsimp [v]; linarith⟩
  have hrad := D.radius_diff_le_L hVb.le hv
  have hd : 0 < v - D.a := by dsimp [v]; linarith
  nlinarith [abs_nonneg (D.S₁.r D.a v - D.S₂.r D.a v)]

/-- The good-ray incoming expansion norm is nonnegative on a nontrivial
compact top. -/
theorem ComparisonData.N_nonneg (D : ComparisonData)
    {V : ℝ} (haV : D.a < V) (hVb : V < D.b) :
    0 ≤ D.N V := by
  let v := (D.a + V) / 2
  have hv : (D.a, v) ∈ triangle D.a V :=
    (mem_triangle).2 ⟨le_rfl, by dsimp [v]; linarith,
      by dsimp [v]; linarith⟩
  have hrad := D.radius_diff_le_N hVb hv
  have hd : 0 < v - D.a := by dsimp [v]; linarith
  nlinarith [abs_nonneg (D.S₁.r D.a v - D.S₂.r D.a v)]

/-- The weighted outgoing mass difference is integrable on the full
axis-to-top characteristic. -/
theorem ComparisonData.outgoing_mass_diff_weight_integrable
    (D : ComparisonData) {V u : ℝ}
    (hVb : V < D.b) (hu : u ∈ Ico D.a V) :
    IntegrableOn (fun t =>
      |D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2) (Ioc u V) volume := by
  have hp := D.hT ((mem_triangle).2 ⟨hu.1, hu.2, hVb⟩)
  have h₁ := outgoing_mass_div_sq_integrable D.h₁ hp.1
  have h₂ := outgoing_mass_div_sq_integrable D.h₂ hp.2
  have heq : (fun t => |D.S₁.m u t / (t - u) ^ 2 -
      D.S₂.m u t / (t - u) ^ 2|) =
      (fun t => |D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2) := by
    funext t
    rw [← sub_div, abs_div]
    simp only [abs_of_nonneg (sq_nonneg (t - u))]
  rw [← heq]
  exact (h₁.sub h₂).abs

/-- The outgoing weighted mass integral on one characteristic lies below
the finite extended norm `Γ` at the same compact top. -/
theorem ComparisonData.outgoing_mass_diff_integral_le_Gamma
    (D : ComparisonData) {V u : ℝ}
    (haV : D.a < V) (hVb : V < D.b)
    (hu : u ∈ Ico D.a V) :
    (∫ t in Ioc u V,
      |D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2) ≤
      (D.Gamma V).toReal := by
  have hint := D.outgoing_mass_diff_weight_integrable hVb hu
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc u V)]
      (fun t => |D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro t _
    exact div_nonneg (abs_nonneg _) (sq_nonneg _)
  have hreal : 0 ≤ ∫ t in Ioc u V,
      |D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2 :=
    integral_nonneg_of_ae hnonneg
  have heq := ofReal_integral_eq_lintegral_ofReal hint hnonneg
  have hlin : (∫⁻ t in Ioc u V,
      ENNReal.ofReal
        (|D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2)) ≤
      D.Gamma V := by
    unfold ComparisonData.Gamma
    exact le_iSup_of_le u (le_iSup_of_le hu le_rfl)
  obtain ⟨M, _, hM⟩ := D.Gamma_uniform_bound
  have hfinite : D.Gamma V ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hM V haV hVb)
  have hle := ENNReal.toReal_mono hfinite (heq.trans_le hlin)
  rw [ENNReal.toReal_ofReal hreal] at hle
  exact hle

/-- The absolute outgoing coefficient difference is integrable on every
complete half-open outgoing characteristic. -/
theorem ComparisonData.nuCoeff_difference_integrable (D : ComparisonData)
    {V u : ℝ} (hVb : V < D.b) (hu : u ∈ Ico D.a V) :
    IntegrableOn (fun t =>
      |IsBVSolution.nuCoeff D.S₁ u t -
        IsBVSolution.nuCoeff D.S₂ u t|) (Ioc u V) volume := by
  have hp := D.hT ((mem_triangle).2 ⟨hu.1, hu.2, hVb⟩)
  obtain ⟨Q₁, _, hQ₁⟩ := D.h₁.exists_theta_div_lam_bound_out hp.1
  obtain ⟨Q₂, _, hQ₂⟩ := D.h₂.exists_theta_div_lam_bound_out hp.2
  exact (D.h₁.nu_coeff_integrable_axis hp.1 hQ₁ |>.sub
    (D.h₂.nu_coeff_integrable_axis hp.2 hQ₂)).abs

/-- One constant controls the outgoing
absolute coefficient difference by `L + Γ` uniformly in the compact top. -/
theorem ComparisonData.nuCoeff_difference_integral_uniform
    (D : ComparisonData) (ha : D.a = 0) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∃ C₁ : ℝ, 4 ≤ C₁ ∧ ∃ C : ℝ, 1 ≤ C ∧
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀ ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε₀) →
        ∀ V, D.a < V → V < D.b →
          ∀ u ∈ Ico D.a V,
            (∫ t in u..V,
              |IsBVSolution.nuCoeff D.S₁ u t -
                IsBVSolution.nuCoeff D.S₂ u t|) ≤
              C * (D.L V + (D.Gamma V).toReal)) := by
  obtain ⟨C₀, hC₀, ε₀, hε₀, C₁, hC₁, hpoint⟩ :=
    D.expansion_coefficient_pointwise_uniform ha
  obtain ⟨M, hM, hcoeff⟩ := D.nuCoeff_integral_uniform_pair
  let F := C₁ ^ 2 + (C₁ ^ 2) ^ 2 + (C₁ ^ 2) ^ 4
  let B := 2 * (C₁ ^ 2) ^ 5
  let C := max (F * M) B + 1
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 1 ≤ C := by
    dsimp [C]
    have : 0 ≤ F * M := mul_nonneg hF hM
    linarith [le_max_left (F * M) B]
  refine ⟨C₀, hC₀, ε₀, hε₀, C₁, hC₁, C, hC, ?_⟩
  intro hsmall V haV hVb u hu
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
    exact (hpoint hsmall V haV hVb u t htt htG).1
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
      (hcoeff V haV hVb u hu).2
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
