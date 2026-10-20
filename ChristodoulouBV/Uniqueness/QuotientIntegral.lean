module

public import ChristodoulouBV.Uniqueness.QuotientNormPoints

/-!
# Integrating an almost-everywhere quotient transport bound
-/

@[expose] public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- An absolutely continuous quotient difference is bounded by an integrable
majorant for its almost-everywhere derivative. -/
theorem quotient_transport_abs_le_integral
    {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : IntervalIntegrable g volume a b)
    (hbound : ∀ᵐ t ∂volume, t ∈ Icc a b → |deriv f t| ≤ g t) :
    |f b - f a| ≤ ∫ t in a..b, g t := by
  have hfi : IntervalIntegrable (deriv f) volume a b :=
    hf.intervalIntegrable_deriv
  have hfiabs : IntegrableOn (fun t => |deriv f t|) (Ioc a b) volume :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hfi).abs
  have hgi : IntegrableOn g (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hg
  have hAE : ∀ᵐ t ∂volume.restrict (Ioc a b),
      |deriv f t| ≤ g t := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [hbound] with t ht hmem
    exact ht ⟨hmem.1.le, hmem.2⟩
  calc
    |f b - f a| = |∫ t in a..b, deriv f t| := by
      rw [hf.integral_deriv_eq_sub]
    _ ≤ ∫ t in a..b, |deriv f t| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, g t := by
      rw [intervalIntegral.integral_of_le hab,
        intervalIntegral.integral_of_le hab]
      exact integral_mono_ae hfiabs hgi hAE

/-- The scalar density quotient difference is the primitive quotient
difference minus the scalar difference. -/
theorem ComparisonData.theta_ratio_diff_eq (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    D.S₁.theta u v / D.S₁.lam u v -
        D.S₂.theta u v / D.S₂.lam u v =
      (D.S₁.alpha u v / D.S₁.lam u v -
        D.S₂.alpha u v / D.S₂.lam u v) -
      (D.S₁.phi u v - D.S₂.phi u v) := by
  have hp := D.hT huv
  have h₁ := (D.h₁.solution.lam_pos (u, v) hp.1).ne'
  have h₂ := (D.h₂.solution.lam_pos (u, v) hp.2).ne'
  dsimp [Fields.theta]
  field_simp [h₁, h₂]
  ring

/-- The incoming scalar density quotient has the analogous identity. -/
theorem ComparisonData.zeta_ratio_diff_eq (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    D.S₁.zeta u v / D.S₁.nu u v -
        D.S₂.zeta u v / D.S₂.nu u v =
      (D.S₁.beta u v / D.S₁.nu u v -
        D.S₂.beta u v / D.S₂.nu u v) -
      (D.S₁.phi u v - D.S₂.phi u v) := by
  have hp := D.hT huv
  obtain ⟨c₁, hc₁, hlam₁⟩ := D.h₁.lam_bounded_below
  obtain ⟨c₂, hc₂, hlam₂⟩ := D.h₂.lam_bounded_below
  have hn₁ : D.S₁.nu u v ≠ 0 :=
    ne_of_lt ((D.h₁.nu_le_neg_lower hc₁ hlam₁ hp.1).trans_lt
      (neg_lt_zero.mpr hc₁))
  have hn₂ : D.S₂.nu u v ≠ 0 :=
    ne_of_lt ((D.h₂.nu_le_neg_lower hc₂ hlam₂ hp.2).trans_lt
      (neg_lt_zero.mpr hc₂))
  dsimp [Fields.zeta]
  field_simp [hn₁, hn₂]
  ring

/-- A pointwise incoming transport majorant using only the quotient,
scalar, and second solution coefficient bounds. -/
theorem ComparisonData.alpha_ratio_forcing_abs_le (D : ComparisonData)
    {u v A P Q : ℝ} (huv : (u, v) ∈ triangle D.a D.b)
    (hA : |D.S₁.alpha u v / D.S₁.lam u v -
      D.S₂.alpha u v / D.S₂.lam u v| ≤ A)
    (hP : |D.S₁.phi u v - D.S₂.phi u v| ≤ P)
    (hQ : |D.S₂.theta u v / D.S₂.lam u v| ≤ Q) :
    |alphaRatioForcing D u v| ≤
      (-IsBVSolution.incomingCoeff D.S₁ u v) * (A + P) +
        Q * |IsBVSolution.incomingCoeff D.S₁ u v -
          IsBVSolution.incomingCoeff D.S₂ u v| := by
  have hk := D.h₁.incomingCoeff_nonpos (D.hT huv).1
  have hk0 : 0 ≤ -IsBVSolution.incomingCoeff D.S₁ u v := by linarith
  have hD : |D.S₁.theta u v / D.S₁.lam u v -
      D.S₂.theta u v / D.S₂.lam u v| ≤ A + P := by
    rw [D.theta_ratio_diff_eq huv]
    exact (abs_sub _ _).trans (add_le_add hA hP)
  rw [D.alpha_ratio_forcing_factor huv]
  calc
    |-IsBVSolution.incomingCoeff D.S₁ u v *
        (D.S₁.theta u v / D.S₁.lam u v -
          D.S₂.theta u v / D.S₂.lam u v) -
        (IsBVSolution.incomingCoeff D.S₁ u v -
          IsBVSolution.incomingCoeff D.S₂ u v) *
          (D.S₂.theta u v / D.S₂.lam u v)| ≤
      (-IsBVSolution.incomingCoeff D.S₁ u v) *
        |D.S₁.theta u v / D.S₁.lam u v -
          D.S₂.theta u v / D.S₂.lam u v| +
      |IsBVSolution.incomingCoeff D.S₁ u v -
          IsBVSolution.incomingCoeff D.S₂ u v| *
        |D.S₂.theta u v / D.S₂.lam u v| := by
      calc
        _ ≤ |-IsBVSolution.incomingCoeff D.S₁ u v *
            (D.S₁.theta u v / D.S₁.lam u v -
              D.S₂.theta u v / D.S₂.lam u v)| +
            |(IsBVSolution.incomingCoeff D.S₁ u v -
              IsBVSolution.incomingCoeff D.S₂ u v) *
              (D.S₂.theta u v / D.S₂.lam u v)| := abs_sub _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hk0]
    _ ≤ (-IsBVSolution.incomingCoeff D.S₁ u v) * (A + P) +
        Q * |IsBVSolution.incomingCoeff D.S₁ u v -
          IsBVSolution.incomingCoeff D.S₂ u v| := by
      have h₁ := mul_le_mul_of_nonneg_left hD hk0
      have h₂ := mul_le_mul_of_nonneg_left hQ
        (abs_nonneg (IsBVSolution.incomingCoeff D.S₁ u v -
          IsBVSolution.incomingCoeff D.S₂ u v))
      nlinarith only [h₁, h₂]

/-- The outgoing quotient transport has a parallel pointwise majorant. -/
theorem ComparisonData.beta_ratio_forcing_abs_le (D : ComparisonData)
    {u v B P Q : ℝ} (huv : (u, v) ∈ triangle D.a D.b)
    (hB : |D.S₁.beta u v / D.S₁.nu u v -
      D.S₂.beta u v / D.S₂.nu u v| ≤ B)
    (hP : |D.S₁.phi u v - D.S₂.phi u v| ≤ P)
    (hQ : |D.S₂.zeta u v / D.S₂.nu u v| ≤ Q) :
    |betaRatioForcing D u v| ≤
      IsBVSolution.nuCoeff D.S₁ u v * (B + P) +
        Q * |IsBVSolution.nuCoeff D.S₁ u v -
          IsBVSolution.nuCoeff D.S₂ u v| := by
  have hk := IsBVSolution.nu_coeff_nonneg D.h₁.solution.development D.h₁
    (D.hT huv).1
  have hD : |D.S₁.zeta u v / D.S₁.nu u v -
      D.S₂.zeta u v / D.S₂.nu u v| ≤ B + P := by
    rw [D.zeta_ratio_diff_eq huv]
    exact (abs_sub _ _).trans (add_le_add hB hP)
  rw [D.beta_ratio_forcing_factor huv]
  calc
    |-IsBVSolution.nuCoeff D.S₁ u v *
        (D.S₁.zeta u v / D.S₁.nu u v -
          D.S₂.zeta u v / D.S₂.nu u v) -
        (IsBVSolution.nuCoeff D.S₁ u v -
          IsBVSolution.nuCoeff D.S₂ u v) *
          (D.S₂.zeta u v / D.S₂.nu u v)| ≤
      IsBVSolution.nuCoeff D.S₁ u v *
        |D.S₁.zeta u v / D.S₁.nu u v -
          D.S₂.zeta u v / D.S₂.nu u v| +
      |IsBVSolution.nuCoeff D.S₁ u v -
          IsBVSolution.nuCoeff D.S₂ u v| *
        |D.S₂.zeta u v / D.S₂.nu u v| := by
      calc
        _ ≤ |-IsBVSolution.nuCoeff D.S₁ u v *
            (D.S₁.zeta u v / D.S₁.nu u v -
              D.S₂.zeta u v / D.S₂.nu u v)| +
            |(IsBVSolution.nuCoeff D.S₁ u v -
              IsBVSolution.nuCoeff D.S₂ u v) *
              (D.S₂.zeta u v / D.S₂.nu u v)| := abs_sub _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hk]
    _ ≤ IsBVSolution.nuCoeff D.S₁ u v * (B + P) +
        Q * |IsBVSolution.nuCoeff D.S₁ u v -
          IsBVSolution.nuCoeff D.S₂ u v| := by
      have h₁ := mul_le_mul_of_nonneg_left hD hk
      have h₂ := mul_le_mul_of_nonneg_left hQ
        (abs_nonneg (IsBVSolution.nuCoeff D.S₁ u v -
          IsBVSolution.nuCoeff D.S₂ u v))
      nlinarith only [h₁, h₂]

/-- A single preliminary variation choice gives a uniform bound for the
second solution's two scalar density quotients on the full triangle. -/
theorem ComparisonData.quotient_second_uniform_bounds (D : ComparisonData)
    (ha : D.a = 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Q : ℝ, 1 ≤ Q ∧
      ((∀ x y, (x, y) ∈ triangle D.a D.b →
        ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
          (eVariationOn (S.phi x) (Ioc x y)).toReal ≤ ε₀ ∧
          (eVariationOn (fun s => S.phi s y) (Ico x y)).toReal ≤ ε₀) →
        ∀ u v, (u, v) ∈ triangle D.a D.b →
          |D.S₂.theta u v / D.S₂.lam u v| ≤ Q ∧
          |D.S₂.zeta u v / D.S₂.nu u v| ≤ Q) := by
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
  intro hsmall u v huv
  rcases hcoef D.a D.b D.hT hsmall u v huv D.S₂ (Or.inr rfl) with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hθ, hζ,
      _, _, _, _, _, _, _⟩
  exact ⟨hθ, hζ⟩

end ChristodoulouBV.Uniqueness

end
