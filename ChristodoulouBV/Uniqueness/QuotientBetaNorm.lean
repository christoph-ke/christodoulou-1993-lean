module

public import ChristodoulouBV.Uniqueness.QuotientBeta
public import ChristodoulouBV.Uniqueness.QuotientAxis

/-!
# Axis based outgoing scalar quotient norm
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Interval Topology

namespace ChristodoulouBV.Uniqueness

/-- The outgoing expansion coefficient has a small integral on every
subsegment after the preliminary coefficient choice. -/
theorem ComparisonData.nuCoeff_outgoing_segment_small
    (D : ComparisonData) (ha : D.a = 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Q : ℝ, 1 ≤ Q ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
        (∀ p q, (p, q) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi p) (Ioc p q)).toReal ≤ ε ∧
            (eVariationOn (fun s => S.phi s q) (Ico p q)).toReal ≤ ε) →
        ∀ u x v, (u, v) ∈ triangle D.a D.b →
          u < x → x ≤ v →
          (∫ t in x..v, IsBVSolution.nuCoeff D.S₁ u t) ≤ Q * ε := by
  let w := (D.a + D.b) / 2
  have hw : w ∈ Ioo D.a D.b := by
    dsimp [w]
    constructor <;> linarith [D.hab]
  have href : (0, w) ∈ D.U₁ ∩ D.U₂ := by
    simpa only [ha] using D.hT
      ((mem_triangle).2 ⟨le_rfl, hw.1, hw.2⟩)
  have hdata : D.S₁.phi 0 w = D.S₂.phi 0 w := by
    simpa only [ha] using (D.hdata w hw).2
  obtain ⟨_, _, ε₀, hε₀, Q, hQ, hcoef⟩ :=
    D.h₁.coefficient_bounds D.h₂ href hdata
  refine ⟨ε₀, hε₀, Q, by linarith, ?_⟩
  intro ε hε hε₀le hsmall u x v huv hux hxv
  have hpre : ∀ p q, (p, q) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        (eVariationOn (S.phi p) (Ioc p q)).toReal ≤ ε₀ ∧
        (eVariationOn (fun s => S.phi s q) (Ico p q)).toReal ≤ ε₀ := by
    intro p q hpq S hS
    have hh := hsmall p q hpq S hS
    exact ⟨hh.1.trans hε₀le, hh.2.trans hε₀le⟩
  have hM : ∀ t ∈ Ioc u v,
      |D.S₁.theta u t / D.S₁.lam u t| ≤ Q := by
    intro t ht
    have hut : (u, t) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩
    rcases hcoef D.a D.b D.hT hpre u t hut D.S₁ (Or.inl rfl) with
      ⟨_, _, _, _, _, _, _, _, _, _, _, hθ,
        _, _, _, _, _, _, _, _⟩
    exact hθ
  have hfull := D.h₁.eq3_1a_nuCoeff (D.hT huv).1 hM
  have hvar := (hsmall u v huv D.S₁ (Or.inl rfl)).1
  have hK := D.h₁.nu_coeff_integrable_axis (D.hT huv).1 hM
  have hInt : IntervalIntegrable (IsBVSolution.nuCoeff D.S₁ u)
      volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).2 hK
  have hpos : 0 ≤ᵐ[volume.restrict (Ioc u v)]
      IsBVSolution.nuCoeff D.S₁ u := by
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro t ht
    have hut : (u, t) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩
    exact IsBVSolution.nu_coeff_nonneg
      D.h₁.solution.development D.h₁ (D.hT hut).1
  have hmono := intervalIntegral.integral_mono_interval
    hux.le hxv le_rfl hpos hInt
  exact hmono.trans (hfull.trans (mul_le_mul_of_nonneg_left hvar
    (by linarith : 0 ≤ Q)))

/-- The outgoing quotient estimate uses the axis trace as its initial
value. All coefficients are fixed before the variation parameter and top. -/
theorem ComparisonData.beta_ratio_goodV_integral_bound
    (D : ComparisonData) (ha : D.a = 0) (hb : D.b = 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∃ Cscalar : ℝ, 4 ≤ Cscalar ∧
      ∃ Q₁ : ℝ, 1 ≤ Q₁ ∧
      ∃ Q₂ : ℝ, 1 ≤ Q₂ ∧
      ∃ Ccoeff : ℝ, 1 ≤ Ccoeff ∧
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
          (∀ x y, (x, y) ∈ triangle D.a D.b →
            ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
              (eVariationOn (S.phi x) (Ioc x y)).toReal ≤ ε ∧
              (eVariationOn (fun s => S.phi s y) (Ico x y)).toReal ≤ ε) →
          ∀ V, D.a < V → V < D.b →
            D.B V ≤ D.A V +
              (D.B V + Cscalar * (D.B V + D.N V)) * (Q₁ * ε) +
              Q₂ * Ccoeff * (D.L V + (D.Gamma V).toReal) := by
  obtain ⟨εn, hεn, hnorm⟩ := D.quotient_differences_le_norms ha
  obtain ⟨_, _, εs, hεs, Cscalar, hCs, hscalar⟩ :=
    D.radius_scalar_goodV_bounds ha hb
  obtain ⟨εq, hεq, Q₂, hQ₂, hquot⟩ :=
    D.quotient_second_uniform_bounds ha
  obtain ⟨εk, hεk, Q₁, hQ₁, hseg⟩ :=
    D.nuCoeff_outgoing_segment_small ha
  obtain ⟨_, _, εd, hεd, _, _, Ccoeff, hCcoeff, hcoeff⟩ :=
    D.nuCoeff_difference_integral_uniform ha
  obtain ⟨εa, hεa, haxis⟩ := D.beta_ratio_axis_le_A ha
  let ε₀ := min εn (min εs (min εq (min εk (min εd εa))))
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    exact lt_min hεn (lt_min hεs (lt_min hεq
      (lt_min hεk (lt_min hεd hεa))))
  refine ⟨ε₀, hε₀, Cscalar, hCs, Q₁, hQ₁,
    Q₂, hQ₂, Ccoeff, hCcoeff, ?_⟩
  intro ε hε hε₀le hsmall V haV hVb
  have hεnle : ε ≤ εn := hε₀le.trans (min_le_left _ _)
  have hεsle : ε ≤ εs :=
    hε₀le.trans (min_le_right _ _) |>.trans (min_le_left _ _)
  have hεqle : ε ≤ εq :=
    hε₀le.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans
      (min_le_left _ _)
  have hεkle : ε ≤ εk :=
    hε₀le.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans
      (min_le_right _ _) |>.trans (min_le_left _ _)
  have hεdle : ε ≤ εd :=
    hε₀le.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans
      (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans
        (min_le_left _ _)
  have hεale : ε ≤ εa :=
    hε₀le.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans
      (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans
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
  have hsmallA := hshrink εa hεale
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
  obtain ⟨l, htrace, htraceA⟩ := haxis hsmallA V haV hVb u hu
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
      exact (hnorm hsmallN V haV hVb u t hpt).2
    have hPpt : ∀ t ∈ Icc x v,
        |D.S₁.phi u t - D.S₂.phi u t| ≤
          Cscalar * (D.B V + D.N V) := by
      intro t ht
      have hpt : (u, t) ∈ triangle D.a V :=
        (mem_triangle).2 ⟨huv.1, hx.1.trans_le ht.1,
          ht.2.trans_lt huv.2.2⟩
      exact (hscalar hsmallS V u t hVb hpt).2.2.2
    have hQpt : ∀ t ∈ Icc x v,
        |D.S₂.zeta u t / D.S₂.nu u t| ≤ Q₂ := by
      intro t ht
      have hpt : (u, t) ∈ triangle D.a D.b :=
        (mem_triangle).2 ⟨huv.1, hx.1.trans_le ht.1,
          ht.2.trans_lt (huv.2.2.trans hVb)⟩
      exact (hquot hsmallQ u t hpt).2
    have hraw := D.beta_ratio_le_coefficient_integrals
      hfull hx.1 hx.2.le hBpt hPpt hQpt
    have hsmallCoeff := hseg ε hε hεkle hsmall u x v hfull
      hx.1 hx.2.le
    have hdiffFull := hcoeff (hshrink εd hεdle) V haV hVb u hu
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
