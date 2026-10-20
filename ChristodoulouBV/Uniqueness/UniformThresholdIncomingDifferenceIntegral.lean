module

public import ChristodoulouBV.Uniqueness.UniformThresholdIncomingCoeffIntegral
public import ChristodoulouBV.Uniqueness.ExpansionCoeffIncomingIntegral

/-!
# Uniform incoming coefficient difference integral

The pointwise coefficient and incoming transport constants are selected from
one numerical package before the normalized comparison data.
-/

@[expose] public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- The absolute incoming coefficient
difference is controlled by `ε N + Γ*` on every good incoming ray. The
constant is fixed before the final variation size and compact cutoff. -/
theorem UniformThresholdBounds.incomingCoeff_difference_integral_uniform
    (P : UniformThresholdBounds) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ P.gapThreshold →
          (∀ u v, (u, v) ∈ triangle D.a D.b →
            ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
              (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε ∧
              (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε) →
          ∀ V, D.a < V → V < D.b →
            ∀ v ∈ Ioo D.a V, v ∈ D.goodV →
              (∫ s in D.a..v,
                |IsBVSolution.incomingCoeff D.S₁ s v -
                  IsBVSolution.incomingCoeff D.S₂ s v|) ≤
                C * (ε * D.N V + (D.GammaStar V).toReal) := by
  obtain ⟨J, hJ, husable⟩ := P.incomingCoeff_integral_small
  obtain ⟨C₁, hC₁, hpoint⟩ := P.expansion_coefficient_pointwise_uniform
  let F := C₁ ^ 2 + (C₁ ^ 2) ^ 2 + (C₁ ^ 2) ^ 4
  let B := 2 * (C₁ ^ 2) ^ 5
  let C := max (F * J) B + 1
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 1 ≤ C := by
    dsimp [C]
    have : 0 ≤ F * J := mul_nonneg hF hJ
    linarith [le_max_left (F * J) B]
  refine ⟨C, hC, ?_⟩
  intro D ha hb hP ε hε hεle hsmall V haV hVb v hv hvG
  have hvb : v < D.b := hv.2.trans hVb
  have hpre : ∀ u v, (u, v) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ P.gapThreshold := by
    intro u' v' hp S hS
    exact (hsmall u' v' hp S hS).1.trans hεle
  have hN : 0 ≤ D.N V := D.N_nonneg haV hVb
  have hΓ : 0 ≤ (D.GammaStar V).toReal := ENNReal.toReal_nonneg
  have hK := D.incomingCoeff_integrable_pair ha v ⟨hv.1, hvb⟩
  have hK₁ := hK.1
  have hK₂ := hK.2
  have hdiff : IntegrableOn (fun s =>
      |IsBVSolution.incomingCoeff D.S₁ s v -
        IsBVSolution.incomingCoeff D.S₂ s v|) (Ioc D.a v) volume :=
    (hK₁.sub hK₂).abs
  have hmassIco := D.incoming_mass_diff_weight_integrable hv.1 hvb
  let mass : ℝ → ℝ := fun s =>
    |D.S₁.m s v - D.S₂.m s v| / (v - s) ^ 2
  have hmass : IntegrableOn mass (Ioc D.a v) volume := by
    change Integrable mass (volume.restrict (Ioc D.a v))
    rw [← restrict_Ico_eq_restrict_Ioc]
    exact hmassIco
  have hRhs : IntegrableOn (fun s =>
      F * D.N V * (-IsBVSolution.incomingCoeff D.S₂ s v) +
        B * mass s) (Ioc D.a v) volume :=
    (hK₂.neg.const_mul (F * D.N V)).add (hmass.const_mul B)
  have hneg : IntegrableOn (fun s =>
      -IsBVSolution.incomingCoeff D.S₂ s v) (Ioc D.a v) volume := hK₂.neg
  have hae : ∀ᵐ s ∂volume.restrict (Ioc D.a v),
      |IsBVSolution.incomingCoeff D.S₁ s v -
        IsBVSolution.incomingCoeff D.S₂ s v| ≤
      F * D.N V * (-IsBVSolution.incomingCoeff D.S₂ s v) +
        B * mass s := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    have hne : ∀ᵐ s : ℝ ∂volume, s ≠ v := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with s hsne hs
    have hst : (s, v) ∈ triangle D.a V :=
      (mem_triangle).2 ⟨hs.1.le, lt_of_le_of_ne hs.2 hsne, hv.2⟩
    exact (hpoint D ha hb hP hpre V haV hVb s v hst hvG).2
  have hle := integral_mono_ae hdiff hRhs hae
  have hsum : (∫ s in Ioc D.a v,
      F * D.N V * (-IsBVSolution.incomingCoeff D.S₂ s v) +
        B * mass s) =
      F * D.N V * (∫ s in Ioc D.a v,
        -IsBVSolution.incomingCoeff D.S₂ s v) +
      B * (∫ s in Ioc D.a v, mass s) := by
    rw [integral_add (hneg.const_mul (F * D.N V))
      (hmass.const_mul B), integral_const_mul, integral_const_mul]
  have hpointv : (D.a, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨le_rfl, hv.1, hvb⟩
  have hY := (hsmall D.a v hpointv D.S₂ (Or.inr rfl)).2
  have hcoef : (∫ s in Ioc D.a v,
      -IsBVSolution.incomingCoeff D.S₂ s v) ≤ J * ε := by
    have hh := husable D ha hb hP ε hε D.a v hpointv
      D.S₂ (Or.inr rfl) hY
    rw [intervalIntegral.integral_of_le hv.1.le] at hh
    rw [integral_neg]
    exact hh
  have hmassbound : (∫ s in Ioc D.a v, mass s) ≤
      (D.GammaStar V).toReal :=
    D.incoming_mass_diff_integral_le_GammaStar hv hVb
  have hFJ : F * J ≤ C := by
    dsimp [C]
    linarith [le_max_left (F * J) B]
  have hBC : B ≤ C := by dsimp [C]; linarith [le_max_right (F * J) B]
  have hstep₁ := mul_le_mul_of_nonneg_left hcoef (mul_nonneg hF hN)
  have hstep₂ := mul_le_mul_of_nonneg_left hmassbound hB
  have hεN : 0 ≤ ε * D.N V := mul_nonneg hε hN
  have hstep₃ := mul_le_mul_of_nonneg_right hFJ hεN
  have hstep₄ := mul_le_mul_of_nonneg_right hBC hΓ
  rw [intervalIntegral.integral_of_le hv.1.le]
  calc
    (∫ s in Ioc D.a v,
      |IsBVSolution.incomingCoeff D.S₁ s v -
        IsBVSolution.incomingCoeff D.S₂ s v|) ≤
      F * D.N V * (∫ s in Ioc D.a v,
        -IsBVSolution.incomingCoeff D.S₂ s v) +
      B * (∫ s in Ioc D.a v, mass s) := by rw [← hsum]; exact hle
    _ ≤ F * D.N V * (J * ε) +
        B * (D.GammaStar V).toReal := by linarith
    _ ≤ C * (ε * D.N V + (D.GammaStar V).toReal) := by nlinarith


end ChristodoulouBV.Uniqueness

end
