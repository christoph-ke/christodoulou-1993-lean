module

public import ChristodoulouBV.Uniqueness.UniformThresholdQuotientAxis
public import ChristodoulouBV.Uniqueness.UniformThresholdQuotientSegment
public import ChristodoulouBV.Uniqueness.UniformThresholdQuotientSecond
public import ChristodoulouBV.Uniqueness.UniformThresholdScalarCombined
public import ChristodoulouBV.Uniqueness.UniformThresholdOutgoingDifferenceIntegral
public import ChristodoulouBV.Uniqueness.QuotientBetaNorm

/-!
# Package-uniform outgoing quotient norm
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The quotient transport coefficient is selected from the package. -/
theorem UniformThresholdBounds.beta_ratio_goodV_integral_bound
    (P : UniformThresholdBounds) :
    ∃ Cscalar : ℝ, 4 ≤ Cscalar ∧
      ∃ Q₁ : ℝ, 1 ≤ Q₁ ∧
      ∃ Q₂ : ℝ, 1 ≤ Q₂ ∧
      ∃ Ccoeff : ℝ, 1 ≤ Ccoeff ∧
        ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
          P.Holds D.S₁ D.S₂ →
          P.VariationHoldsOne D.U₁ D.S₁ →
          P.VariationHoldsOne D.U₂ D.S₂ →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ P.gapThreshold →
          (∀ x y, (x, y) ∈ triangle D.a D.b →
            ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
              (eVariationOn (S.phi x) (Ioc x y)).toReal ≤ ε ∧
              (eVariationOn (fun s => S.phi s y) (Ico x y)).toReal ≤ ε) →
          ∀ V, D.a < V → V < D.b →
            D.B V ≤ D.A V +
              (D.B V + Cscalar * (D.B V + D.N V)) * (Q₁ * ε) +
              Q₂ * Ccoeff * (D.L V + (D.Gamma V).toReal) := by
  have hnorm := P.quotient_differences_le_norms
  obtain ⟨Cscalar, hCs, hscalar⟩ := P.radius_scalar_goodV_bounds
  obtain ⟨Q₂, hQ₂, hquot⟩ := P.quotient_second_uniform_bounds
  obtain ⟨Q₁, hQ₁, hseg⟩ := P.nuCoeff_outgoing_segment_small
  obtain ⟨Ccoeff, hCcoeff, hcoeff⟩ :=
    P.nuCoeff_difference_integral_uniform
  have haxis := P.beta_ratio_axis_le_A
  refine ⟨Cscalar, hCs, Q₁, hQ₁, Q₂, hQ₂, Ccoeff, hCcoeff, ?_⟩
  intro D ha hb hP hvar₁ hvar₂ ε hε hε₀le hsmall V haV hVb
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
  have hB : 0 ≤ D.B V := D.B_nonneg ha hVb.le
  have hN : 0 ≤ D.N V := D.N_nonneg haV hVb
  have hA : 0 ≤ D.A V := D.A_nonneg V
  have hL : 0 ≤ D.L V := D.L_nonneg haV hVb
  have hΓ : 0 ≤ (D.Gamma V).toReal := ENNReal.toReal_nonneg
  have hM : 0 ≤ D.B V + Cscalar * (D.B V + D.N V) := by
    have : 0 ≤ Cscalar := by linarith
    positivity
  have hR : 0 ≤ D.A V +
      (D.B V + Cscalar * (D.B V + D.N V)) * (Q₁ * ε) +
      Q₂ * Ccoeff * (D.L V + (D.Gamma V).toReal) := by
    have : 0 ≤ Q₁ := by linarith
    have : 0 ≤ Q₂ := by linarith
    have : 0 ≤ Ccoeff := by linarith
    positivity
  change D.goodVNorm V
    (fun u v => D.S₁.beta u v / D.S₁.nu u v -
      D.S₂.beta u v / D.S₂.nu u v) ≤ _
  apply D.goodVNorm_le hR
  intro u v huv _hvG
  have hfull : (u, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨huv.1, huv.2.1, huv.2.2.trans hVb⟩
  have hu : u ∈ Ico D.a V := ⟨huv.1, huv.2.1.trans huv.2.2⟩
  obtain ⟨l, htrace, htraceA⟩ := haxis D ha hb hP hpreBoth V haV hVb u hu
  let f : ℝ → ℝ := fun t =>
    D.S₁.beta u t / D.S₁.nu u t -
      D.S₂.beta u t / D.S₂.nu u t
  let R : ℝ :=
    (D.B V + Cscalar * (D.B V + D.N V)) * (Q₁ * ε) +
      Q₂ * Ccoeff * (D.L V + (D.Gamma V).toReal)
  have hlim : Tendsto (fun x => |f v - f x|) (𝓝[>] u)
      (𝓝 |f v - l|) := by
    exact (tendsto_const_nhds.sub htrace).abs
  have hlimBound : |f v - l| ≤ R := by
    apply le_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT huv.2.1] with x hx
    have hBpt : ∀ t ∈ Icc x v, |f t| ≤ D.B V := by
      intro t ht
      have hpt : (u, t) ∈ triangle D.a V :=
        (mem_triangle).2 ⟨huv.1, hx.1.trans_le ht.1,
          ht.2.trans_lt huv.2.2⟩
      exact (hnorm D ha hb hP hpreBoth V haV hVb u t hpt).2
    have hPpt : ∀ t ∈ Icc x v,
        |D.S₁.phi u t - D.S₂.phi u t| ≤
          Cscalar * (D.B V + D.N V) := by
      intro t ht
      have hpt : (u, t) ∈ triangle D.a V :=
        (mem_triangle).2 ⟨huv.1, hx.1.trans_le ht.1,
          ht.2.trans_lt huv.2.2⟩
      exact (hscalar D ha hb hP hpreBoth V u t hVb hpt).2.2.2
    have hQpt : ∀ t ∈ Icc x v,
        |D.S₂.zeta u t / D.S₂.nu u t| ≤ Q₂ := by
      intro t ht
      have hpt : (u, t) ∈ triangle D.a D.b :=
        (mem_triangle).2 ⟨huv.1, hx.1.trans_le ht.1,
          ht.2.trans_lt (huv.2.2.trans hVb)⟩
      exact (hquot D ha hb hP hpreBoth u t hpt).2
    have hraw := D.beta_ratio_le_coefficient_integrals
      hfull hx.1 hx.2.le hBpt hPpt hQpt
    have hsmallCoeff := hseg D ha hb hP ε hε hε₀le hsmall u x v hfull
      hx.1 hx.2.le
    have hdiffFull := hcoeff D ha hb hP hvar₁ hvar₂ hpre V haV hVb u hu
    have hInt : IntervalIntegrable
        (fun t => |IsBVSolution.nuCoeff D.S₁ u t -
          IsBVSolution.nuCoeff D.S₂ u t|)
        volume u V :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hu.2.le).2
        (D.nuCoeff_difference_integrable hVb hu)
    have hmono := intervalIntegral.integral_mono_interval
      hx.1.le hx.2.le huv.2.2.le
      (Filter.Eventually.of_forall (fun t => abs_nonneg _)) hInt
    have hdiff : (∫ t in x..v,
        |IsBVSolution.nuCoeff D.S₁ u t -
          IsBVSolution.nuCoeff D.S₂ u t|) ≤
        Ccoeff * (D.L V + (D.Gamma V).toReal) :=
      hmono.trans hdiffFull
    have hQ₂nonneg : 0 ≤ Q₂ := by linarith
    have hstep₁ := mul_le_mul_of_nonneg_left hsmallCoeff hM
    have hstep₂ := mul_le_mul_of_nonneg_left hdiff hQ₂nonneg
    change |f v - f x| ≤ _ at hraw
    dsimp [R]
    nlinarith only [hraw, hstep₁, hstep₂]
  have htri : |f v| ≤ |f v - l| + |l| := by
    simpa only [sub_add_cancel] using abs_add_le (f v - l) l
  have hresult : |f v| ≤ D.A V + R := by
    linarith only [htri, hlimBound, htraceA]
  simpa only [f, R, add_assoc] using hresult

end ChristodoulouBV.Uniqueness

end
