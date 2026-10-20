module

public import ChristodoulouBV.Uniqueness.QuotientAlpha
public import ChristodoulouBV.Uniqueness.ScalarCombined

/-!
# Good-ray incoming quotient norm
-/

@[expose] public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- The coefficient in the incoming scalar quotient equation has an
`O(ε)` integral on every initial subsegment of a full incoming ray. -/
theorem ComparisonData.incomingCoeff_initial_segment_small
    (D : ComparisonData) (ha : D.a = 0) :
    ∃ J : ℝ, 0 ≤ J ∧
      ∀ ε : ℝ, 0 ≤ ε → ∀ u v,
        (u, v) ∈ triangle D.a D.b →
        (eVariationOn (fun s => D.S₁.phi s v) (Ico D.a v)).toReal ≤ ε →
        (∫ s in D.a..u, -IsBVSolution.incomingCoeff D.S₁ s v) ≤
          J * ε := by
  let w := (D.a + D.b) / 2
  have hw : w ∈ Ioo D.a D.b := by
    dsimp [w]
    constructor <;> linarith [D.hab]
  have href : (0, w) ∈ D.U₁ ∩ D.U₂ := by
    simpa only [ha] using D.hT
      ((mem_triangle).2 ⟨le_rfl, hw.1, hw.2⟩)
  have hdata : D.S₁.phi 0 w = D.S₂.phi 0 w := by
    simpa only [ha] using (D.hdata w hw).2
  obtain ⟨J, hJ, hcoef⟩ := D.h₁.eq3_12_usable D.h₂ href hdata
  refine ⟨J, hJ, ?_⟩
  intro ε hε u v huv hvar
  have hvab : v ∈ Ioo D.a D.b :=
    ⟨huv.1.trans_lt huv.2.1, huv.2.2⟩
  have hpoint : (D.a, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨le_rfl, hvab.1, hvab.2⟩
  have hfull := hcoef ε hε D.a D.b D.a v D.hT hpoint
    D.S₁ (Or.inl rfl) hvar
  change -(∫ s in D.a..v,
    IsBVSolution.incomingCoeff D.S₁ s v) ≤ J * ε at hfull
  have hK := (D.incomingCoeff_integrable_pair ha v hvab).1
  have hInt : IntervalIntegrable
      (fun s => -IsBVSolution.incomingCoeff D.S₁ s v)
      volume D.a v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hvab.1.le).2 hK.neg
  have hpos : 0 ≤ᵐ[volume.restrict (Ioc D.a v)]
      (fun s => -IsBVSolution.incomingCoeff D.S₁ s v) := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    have hne : ∀ᵐ s : ℝ ∂volume, s ≠ v := by simp [ae_iff]
    filter_upwards [hne] with s hsne hs
    have hst : (s, v) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨hs.1.le, lt_of_le_of_ne hs.2 hsne, hvab.2⟩
    exact neg_nonneg.mpr (D.h₁.incomingCoeff_nonpos (D.hT hst).1)
  have hmono := intervalIntegral.integral_mono_interval
    le_rfl huv.1 huv.2.1.le hpos hInt
  calc
    (∫ s in D.a..u, -IsBVSolution.incomingCoeff D.S₁ s v) ≤
      ∫ s in D.a..v, -IsBVSolution.incomingCoeff D.S₁ s v := hmono
    _ = -(∫ s in D.a..v, IsBVSolution.incomingCoeff D.S₁ s v) :=
      intervalIntegral.integral_neg
    _ ≤ J * ε := hfull

/-- The incoming scalar quotient estimate on the good initial rays. All
coefficients are fixed before the variation parameter and compact top. -/
theorem ComparisonData.alpha_ratio_goodV_integral_bound
    (D : ComparisonData) (ha : D.a = 0) (hb : D.b = 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∃ Cscalar : ℝ, 4 ≤ Cscalar ∧
      ∃ Q : ℝ, 1 ≤ Q ∧
      ∃ Ccoeff : ℝ, 1 ≤ Ccoeff ∧
      ∃ J : ℝ, 0 ≤ J ∧
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
          (∀ x y, (x, y) ∈ triangle D.a D.b →
            ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
              (eVariationOn (S.phi x) (Ioc x y)).toReal ≤ ε ∧
              (eVariationOn (fun s => S.phi s y) (Ico x y)).toReal ≤ ε) →
          ∀ V, D.a < V → V < D.b →
            D.A V ≤
              (D.A V + Cscalar * (D.A V + D.L V)) * (J * ε) +
              Q * Ccoeff * (ε * D.N V + (D.GammaStar V).toReal) := by
  obtain ⟨εn, hεn, hnorm⟩ := D.quotient_differences_le_norms ha
  obtain ⟨_, _, εs, hεs, Cscalar, hCs, hscalar⟩ :=
    D.radius_scalar_goodV_bounds ha hb
  obtain ⟨εq, hεq, Q, hQ, hquot⟩ :=
    D.quotient_second_uniform_bounds ha
  obtain ⟨_, _, εk, hεk, _, _, Ccoeff, hCcoeff, hcoeff⟩ :=
    D.incomingCoeff_difference_integral_uniform ha
  obtain ⟨J, hJ, hJseg⟩ := D.incomingCoeff_initial_segment_small ha
  let ε₀ := min εn (min εs (min εq εk))
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    exact lt_min hεn (lt_min hεs (lt_min hεq hεk))
  refine ⟨ε₀, hε₀, Cscalar, hCs, Q, hQ,
    Ccoeff, hCcoeff, J, hJ, ?_⟩
  intro ε hε hε₀le hsmall V haV hVb
  have hεnle : ε ≤ εn := hε₀le.trans (min_le_left _ _)
  have hεsle : ε ≤ εs :=
    hε₀le.trans (min_le_right _ _) |>.trans (min_le_left _ _)
  have hεqle : ε ≤ εq :=
    hε₀le.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans
      (min_le_left _ _)
  have hεkle : ε ≤ εk :=
    hε₀le.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans
      (min_le_right _ _)
  have hshrink (δ : ℝ) (hεδ : ε ≤ δ) :
      ∀ x y, (x, y) ∈ triangle D.a D.b →
        ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
          (eVariationOn (S.phi x) (Ioc x y)).toReal ≤ δ ∧
          (eVariationOn (fun s => S.phi s y) (Ico x y)).toReal ≤ δ := by
    intro x y hxy S hS
    have hh := hsmall x y hxy S hS
    exact ⟨hh.1.trans hεδ, hh.2.trans hεδ⟩
  have hsmallN := hshrink εn hεnle
  have hsmallS := hshrink εs hεsle
  have hsmallQ := hshrink εq hεqle
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
    exact (hnorm hsmallN V haV hVb s v hst).1 hvG
  have hPpt : ∀ s ∈ Icc D.a u,
      |D.S₁.phi s v - D.S₂.phi s v| ≤
        Cscalar * (D.A V + D.L V) := by
    intro s hs
    have hst : (s, v) ∈ triangle D.a V :=
      (mem_triangle).2 ⟨hs.1, hs.2.trans_lt huv.2.1, huv.2.2⟩
    exact (hscalar hsmallS V s v hVb hst).2.2.1
  have hQpt : ∀ s ∈ Icc D.a u,
      |D.S₂.theta s v / D.S₂.lam s v| ≤ Q := by
    intro s hs
    have hst : (s, v) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨hs.1, hs.2.trans_lt huv.2.1,
        huv.2.2.trans hVb⟩
    exact (hquot hsmallQ s v hst).1
  have hraw := D.alpha_ratio_le_coefficient_integrals ha hfull
    hvG hApt hPpt hQpt
  have hpoint : (D.a, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨le_rfl, hvab.1, hvab.2⟩
  have hvar := (hsmall D.a v hpoint D.S₁ (Or.inl rfl)).2
  have hseg := hJseg ε hε u v hfull hvar
  have hdiffFull := hcoeff ε hε hεkle hsmall V haV hVb v hvV hvG
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
