module

public import ChristodoulouBV.Uniqueness.UniformThresholdQuotientSecond
public import ChristodoulouBV.Uniqueness.UniformThresholdScalarCombined
public import ChristodoulouBV.Uniqueness.UniformThresholdQuotientIncomingSegment
public import ChristodoulouBV.Uniqueness.UniformThresholdIncomingDifferenceIntegral
public import ChristodoulouBV.Uniqueness.QuotientAlphaNorm

/-!
# Package-uniform incoming quotient norm
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The quotient transport coefficient is selected from the package. -/
theorem UniformThresholdBounds.alpha_ratio_goodV_integral_bound
    (P : UniformThresholdBounds) :
    ∃ Cscalar : ℝ, 4 ≤ Cscalar ∧
      ∃ Q : ℝ, 1 ≤ Q ∧
      ∃ Ccoeff : ℝ, 1 ≤ Ccoeff ∧
      ∃ J : ℝ, 0 ≤ J ∧
        ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
          P.Holds D.S₁ D.S₂ →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ P.gapThreshold →
          (∀ x y, (x, y) ∈ triangle D.a D.b →
            ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
              (eVariationOn (S.phi x) (Ioc x y)).toReal ≤ ε ∧
              (eVariationOn (fun s => S.phi s y) (Ico x y)).toReal ≤ ε) →
          ∀ V, D.a < V → V < D.b →
            D.A V ≤
              (D.A V + Cscalar * (D.A V + D.L V)) * (J * ε) +
              Q * Ccoeff * (ε * D.N V + (D.GammaStar V).toReal) := by
  have hnorm := P.quotient_differences_le_norms
  obtain ⟨Cscalar, hCs, hscalar⟩ := P.radius_scalar_goodV_bounds
  obtain ⟨Q, hQ, hquot⟩ := P.quotient_second_uniform_bounds
  obtain ⟨Ccoeff, hCcoeff, hcoeff⟩ :=
    P.incomingCoeff_difference_integral_uniform
  obtain ⟨J, hJ, hJseg⟩ := P.incomingCoeff_initial_segment_small
  refine ⟨Cscalar, hCs, Q, hQ, Ccoeff, hCcoeff, J, hJ, ?_⟩
  intro D ha hb hP ε hε hε₀le hsmall V haV hVb
  have hpre : ∀ x y, (x, y) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        (eVariationOn (S.phi x) (Ioc x y)).toReal ≤ P.gapThreshold := by
    intro x y hxy S hS
    exact (hsmall x y hxy S hS).1.trans hε₀le
  have hpreBoth : ∀ x y, (x, y) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        (eVariationOn (S.phi x) (Ioc x y)).toReal ≤ P.gapThreshold ∧
        (eVariationOn (fun s => S.phi s y) (Ico x y)).toReal ≤ P.gapThreshold := by
    intro x y hxy S hS
    obtain ⟨ho, hi⟩ := hsmall x y hxy S hS
    exact ⟨ho.trans hε₀le, hi.trans hε₀le⟩
  have hA : 0 ≤ D.A V := D.A_nonneg V
  have hL : 0 ≤ D.L V := D.L_nonneg haV hVb
  have hN : 0 ≤ D.N V := D.N_nonneg haV hVb
  have hΓ : 0 ≤ (D.GammaStar V).toReal := ENNReal.toReal_nonneg
  have hM : 0 ≤ D.A V + Cscalar * (D.A V + D.L V) := by
    have : 0 ≤ Cscalar := by linarith
    positivity
  have hR : 0 ≤
      (D.A V + Cscalar * (D.A V + D.L V)) * (J * ε) +
        Q * Ccoeff * (ε * D.N V + (D.GammaStar V).toReal) := by
    have : 0 ≤ Q := by linarith
    have : 0 ≤ Ccoeff := by linarith
    positivity
  change D.goodVNorm V
    (fun u v => D.S₁.alpha u v / D.S₁.lam u v -
      D.S₂.alpha u v / D.S₂.lam u v) ≤ _
  apply D.goodVNorm_le hR
  intro u v huv hvG
  have hfull : (u, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨huv.1, huv.2.1, huv.2.2.trans hVb⟩
  have hvab : v ∈ Ioo D.a D.b :=
    ⟨huv.1.trans_lt huv.2.1, huv.2.2.trans hVb⟩
  have hvV : v ∈ Ioo D.a V :=
    ⟨huv.1.trans_lt huv.2.1, huv.2.2⟩
  have hApt : ∀ s ∈ Icc D.a u,
      |D.S₁.alpha s v / D.S₁.lam s v -
        D.S₂.alpha s v / D.S₂.lam s v| ≤ D.A V := by
    intro s hs
    have hst : (s, v) ∈ triangle D.a V :=
      (mem_triangle).2 ⟨hs.1, hs.2.trans_lt huv.2.1, huv.2.2⟩
    exact (hnorm D ha hb hP hpreBoth V haV hVb s v hst).1 hvG
  have hPpt : ∀ s ∈ Icc D.a u,
      |D.S₁.phi s v - D.S₂.phi s v| ≤
        Cscalar * (D.A V + D.L V) := by
    intro s hs
    have hst : (s, v) ∈ triangle D.a V :=
      (mem_triangle).2 ⟨hs.1, hs.2.trans_lt huv.2.1, huv.2.2⟩
    exact (hscalar D ha hb hP hpreBoth V s v hVb hst).2.2.1
  have hQpt : ∀ s ∈ Icc D.a u,
      |D.S₂.theta s v / D.S₂.lam s v| ≤ Q := by
    intro s hs
    have hst : (s, v) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨hs.1, hs.2.trans_lt huv.2.1,
        huv.2.2.trans hVb⟩
    exact (hquot D ha hb hP hpreBoth s v hst).1
  have hraw := D.alpha_ratio_le_coefficient_integrals ha hfull
    hvG hApt hPpt hQpt
  have hpoint : (D.a, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨le_rfl, hvab.1, hvab.2⟩
  have hvar := (hsmall D.a v hpoint D.S₁ (Or.inl rfl)).2
  have hseg := hJseg D ha hb hP ε hε u v hfull hvar
  have hdiffFull := hcoeff D ha hb hP ε hε hε₀le hsmall V haV hVb v hvV hvG
  have hK := D.incomingCoeff_integrable_pair ha v hvab
  have hInt : IntervalIntegrable
      (fun s => |IsBVSolution.incomingCoeff D.S₁ s v -
        IsBVSolution.incomingCoeff D.S₂ s v|)
      volume D.a v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hvab.1.le).2
      (hK.1.sub hK.2).abs
  have hmono := intervalIntegral.integral_mono_interval
    le_rfl huv.1 huv.2.1.le
    (Filter.Eventually.of_forall (fun s => abs_nonneg _)) hInt
  have hdiff : (∫ s in D.a..u,
      |IsBVSolution.incomingCoeff D.S₁ s v -
        IsBVSolution.incomingCoeff D.S₂ s v|) ≤
      Ccoeff * (ε * D.N V + (D.GammaStar V).toReal) :=
    hmono.trans hdiffFull
  have hQnonneg : 0 ≤ Q := by linarith
  have hstep₁ := mul_le_mul_of_nonneg_left hseg hM
  have hstep₂ := mul_le_mul_of_nonneg_left hdiff hQnonneg
  calc
    |D.S₁.alpha u v / D.S₁.lam u v -
      D.S₂.alpha u v / D.S₂.lam u v| ≤
        (D.A V + Cscalar * (D.A V + D.L V)) *
          (∫ s in D.a..u, -IsBVSolution.incomingCoeff D.S₁ s v) +
        Q * (∫ s in D.a..u,
          |IsBVSolution.incomingCoeff D.S₁ s v -
            IsBVSolution.incomingCoeff D.S₂ s v|) := hraw
    _ ≤ (D.A V + Cscalar * (D.A V + D.L V)) * (J * ε) +
        Q * Ccoeff * (ε * D.N V + (D.GammaStar V).toReal) := by
      nlinarith only [hstep₁, hstep₂]

end ChristodoulouBV.Uniqueness

end
