module

public import ChristodoulouBV.Uniqueness.UniformThresholdQuotientAbsorption
public import ChristodoulouBV.Uniqueness.LocalContraction

/-!
# Package-uniform local contraction

One variation threshold works for every normalized comparison satisfying the
same numeric bound package.
-/

@[expose] public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- All six norms vanish under one package-dependent threshold. -/
theorem UniformThresholdBounds.goodV_norms_zero
    (P : UniformThresholdBounds) :
    ∃ εfinal : ℝ, 0 < εfinal ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        P.VariationHoldsOne D.U₁ D.S₁ →
        P.VariationHoldsOne D.U₂ D.S₂ →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ εfinal →
        (∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε) →
        ∀ V, D.a < V → V < D.b →
          D.A V = 0 ∧ D.B V = 0 ∧ D.L V = 0 ∧ D.N V = 0 ∧
          D.Gamma V = 0 ∧ D.GammaStar V = 0 := by
  obtain ⟨εq, hεq, Cq, hCq, hq⟩ := P.stable_quotient_estimates
  obtain ⟨εm, hεm, Cm, hCm, hm⟩ := P.mass_norms_after_absorption
  let εfinal := min εq (min εm (1 / (2 * Cq ^ 2)))
  have hCqpos : 0 < Cq := by linarith
  have hden : 0 < 2 * Cq ^ 2 := by positivity
  have hεfinal : 0 < εfinal := by
    dsimp [εfinal]
    exact lt_min hεq (lt_min hεm (one_div_pos.mpr hden))
  refine ⟨εfinal, hεfinal, ?_⟩
  intro D ha hb hP hvar₁ hvar₂ ε hε hεle hsmall V haV hVb
  obtain ⟨Mg, hMg, hGfinite⟩ := D.Gamma_uniform_bound
  obtain ⟨Mj, hMj, hJfinite⟩ := D.GammaStar_uniform_bound
  have hεqle : ε ≤ εq := hεle.trans (min_le_left _ _)
  have hεmle : ε ≤ εm :=
    hεle.trans (min_le_right _ _) |>.trans (min_le_left _ _)
  have hεden : ε ≤ 1 / (2 * Cq ^ 2) :=
    hεle.trans (min_le_right _ _) |>.trans (min_le_right _ _)
  have hcoeff : Cq ^ 2 * ε ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hεden (sq_nonneg Cq)
    have heq : Cq ^ 2 * (1 / (2 * Cq ^ 2)) = 1 / 2 := by
      field_simp [hCqpos.ne']
    rw [heq] at hh
    exact hh
  obtain ⟨hAq, hBq⟩ :=
    hq D ha hb hP hvar₁ hvar₂ ε hε hεqle hsmall V haV hVb
  have hA0 : 0 ≤ D.A V := D.A_nonneg V
  have hB0 : 0 ≤ D.B V := D.B_nonneg ha hVb.le
  have hmul := mul_le_mul_of_nonneg_left hBq (mul_nonneg hCqpos.le hε)
  have hAfeedback : D.A V ≤ Cq ^ 2 * ε * D.A V := by
    nlinarith only [hAq, hmul]
  have hhalf := mul_le_mul_of_nonneg_right hcoeff hA0
  have hAz : D.A V = 0 := by
    nlinarith only [hA0, hAfeedback, hhalf]
  have hBz : D.B V = 0 := by
    rw [hAz] at hBq
    nlinarith only [hB0, hBq]
  obtain ⟨hG, hJ, hL, hN⟩ := hm D ha hb hP hvar₁ hvar₂ ε hε hεmle hsmall V haV hVb
  have hLz : D.L V = 0 := by
    rw [hAz, hBz] at hL
    have hL0 := D.L_nonneg haV hVb
    nlinarith only [hL, hL0]
  have hNz : D.N V = 0 := by
    rw [hAz, hBz] at hN
    have hN0 := D.N_nonneg haV hVb
    nlinarith only [hN, hN0]
  have hGzReal : (D.Gamma V).toReal = 0 := by
    rw [hAz, hBz] at hG
    exact le_antisymm (by nlinarith only [hG]) ENNReal.toReal_nonneg
  have hJzReal : (D.GammaStar V).toReal = 0 := by
    rw [hAz, hBz] at hJ
    exact le_antisymm (by nlinarith only [hJ]) ENNReal.toReal_nonneg
  have hGtop : D.Gamma V ≠ ⊤ :=
    (lt_of_le_of_lt (hGfinite V haV hVb) ENNReal.ofReal_lt_top).ne
  have hJtop : D.GammaStar V ≠ ⊤ :=
    (lt_of_le_of_lt (hJfinite V haV hVb) ENNReal.ofReal_lt_top).ne
  have hGz : D.Gamma V = 0 := by
    rw [← ENNReal.ofReal_toReal hGtop, hGzReal, ENNReal.ofReal_zero]
  have hJz : D.GammaStar V = 0 := by
    rw [← ENNReal.ofReal_toReal hJtop, hJzReal, ENNReal.ofReal_zero]
  exact ⟨hAz, hBz, hLz, hNz, hGz, hJz⟩


/-- Package-uniform pointwise uniqueness of radius, scalar and mass. -/
theorem UniformThresholdBounds.local_unique
    (P : UniformThresholdBounds) :
    ∃ εfinal : ℝ, 0 < εfinal ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        P.VariationHoldsOne D.U₁ D.S₁ →
        P.VariationHoldsOne D.U₂ D.S₂ →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ εfinal →
        (∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε) →
        ∀ u v, (u, v) ∈ triangle D.a D.b →
          D.S₁.r u v = D.S₂.r u v ∧
          D.S₁.phi u v = D.S₂.phi u v ∧
          D.S₁.m u v = D.S₂.m u v := by
  obtain ⟨εc, hεc, hcontract⟩ := P.goodV_norms_zero
  refine ⟨εc, hεc, ?_⟩
  intro D ha hb hP hvar₁ hvar₂ ε hε hεle hsmall u v huv
  exact D.pointwise_of_goodV_norms_zero ha hb
    (hcontract D ha hb hP hvar₁ hvar₂ ε hε hεle hsmall) u v huv


end ChristodoulouBV.Uniqueness

end
