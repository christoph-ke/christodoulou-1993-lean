module

public import ChristodoulouBV.Uniqueness.QuotientAbsorption

/-!
# Intermediate stable quotient inequalities

These are the unsimplified good-ray estimates before the final mass and
expansion substitutions. Their constants are fixed before variation and top.
-/

@[expose] public section

open Set MeasureTheory

namespace ChristodoulouBV.Uniqueness

private theorem alpha_raw_le
    {A L N H e Cs J Q K : ℝ}
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hN : 0 ≤ N) (hH : 0 ≤ H)
    (he : 0 ≤ e) (heone : e ≤ 1)
    (hCs : 0 ≤ Cs) (hJ : 0 ≤ J) (hQ : 0 ≤ Q) (hK : 0 ≤ K) :
    let C := 1 + J * (1 + Cs) + Q * K
    (A + Cs * (A + L)) * (J * e) + Q * K * (e * N + H) ≤
      C * (e * A + L + N + H) := by
  let C := 1 + J * (1 + Cs) + Q * K
  have hC₁ : J * (1 + Cs) ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hQ hK]
  have hC₂ : J * Cs ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hQ hK]
  have hC₃ : Q * K ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hJ (by linarith : 0 ≤ 1 + Cs)]
  have heL : e * L ≤ L := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right heone hL
  have heN : e * N ≤ N := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right heone hN
  have hAL := mul_le_mul_of_nonneg_right hC₁ (mul_nonneg he hA)
  have hLL := mul_le_mul_of_nonneg_right hC₂ hL
  have hNN := mul_le_mul_of_nonneg_right hC₃ hN
  have hHH := mul_le_mul_of_nonneg_right hC₃ hH
  have hεL := mul_le_mul_of_nonneg_left heL (mul_nonneg hJ hCs)
  have hεN := mul_le_mul_of_nonneg_left heN (mul_nonneg hQ hK)
  dsimp [C]
  nlinarith only [hAL, hLL, hNN, hHH, hεL, hεN]

private theorem beta_raw_le
    {A B L N G e Ct Qt Rt Cd : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hN : 0 ≤ N) (hG : 0 ≤ G)
    (he : 0 ≤ e) (heone : e ≤ 1)
    (hCt : 0 ≤ Ct) (hQt : 0 ≤ Qt)
    (hRt : 0 ≤ Rt) (hCd : 0 ≤ Cd) :
    let C := 1 + Qt * (1 + Ct) + Rt * Cd
    A + (B + Ct * (B + N)) * (Qt * e) +
      Rt * Cd * (L + G) ≤
        C * (A + e * B + L + N + G) := by
  let C := 1 + Qt * (1 + Ct) + Rt * Cd
  have hC₀ : 1 ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hQt (by linarith : 0 ≤ 1 + Ct),
      mul_nonneg hRt hCd]
  have hC₁ : Qt * (1 + Ct) ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hRt hCd]
  have hC₂ : Qt * Ct ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hRt hCd]
  have hC₃ : Rt * Cd ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hQt (by linarith : 0 ≤ 1 + Ct)]
  have heN : e * N ≤ N := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right heone hN
  have hAA := mul_le_mul_of_nonneg_right hC₀ hA
  have hBB := mul_le_mul_of_nonneg_right hC₁ (mul_nonneg he hB)
  have hNN := mul_le_mul_of_nonneg_right hC₂ hN
  have hLL := mul_le_mul_of_nonneg_right hC₃ hL
  have hGG := mul_le_mul_of_nonneg_right hC₃ hG
  have hεN := mul_le_mul_of_nonneg_left heN (mul_nonneg hQt hCt)
  dsimp [C]
  nlinarith only [hAA, hBB, hNN, hLL, hGG, hεN]

/-- The good-ray incoming quotient estimate before mass and expansion
substitution: `A ≤ C(ε A + L + N + Γ*)`. -/
theorem ComparisonData.alpha_ratio_goodV_bound
    (D : ComparisonData) (ha : D.a = 0) (hb : D.b = 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
        (∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε) →
        ∀ V, D.a < V → V < D.b →
          D.A V ≤ C * (ε * D.A V + D.L V + D.N V +
            (D.GammaStar V).toReal) := by
  obtain ⟨εraw, hεraw, Cs, hCs, Q, hQ, Ck, hCk, J, hJ, hraw⟩ :=
    D.alpha_ratio_goodV_integral_bound ha hb
  let ε₀ := min εraw 1
  have hε₀ : 0 < ε₀ := lt_min hεraw (by norm_num)
  let C := 1 + J * (1 + Cs) + Q * Ck
  have hC : 1 ≤ C := by
    dsimp [C]
    have hJs : 0 ≤ J * (1 + Cs) :=
      mul_nonneg hJ (by linarith)
    have hQC : 0 ≤ Q * Ck :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  refine ⟨ε₀, hε₀, C, hC, ?_⟩
  intro ε hε hε₀le hsmall V haV hVb
  have heone : ε ≤ 1 := hε₀le.trans (min_le_right _ _)
  have hεrawle : ε ≤ εraw := hε₀le.trans (min_le_left _ _)
  have hrawV := hraw ε hε hεrawle hsmall V haV hVb
  have hbound := alpha_raw_le (D.A_nonneg V)
    (D.L_nonneg haV hVb) (D.N_nonneg haV hVb)
    (show 0 ≤ (D.GammaStar V).toReal from ENNReal.toReal_nonneg) hε heone
    (by linarith : 0 ≤ Cs)
    hJ (by linarith : 0 ≤ Q) (by linarith : 0 ≤ Ck)
  dsimp [C] at hbound ⊢
  exact hrawV.trans hbound

/-- The outgoing quotient estimate before mass and expansion substitution:
`B ≤ C(A + ε B + L + N + Γ)`. -/
theorem ComparisonData.beta_ratio_goodV_bound
    (D : ComparisonData) (ha : D.a = 0) (hb : D.b = 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
        (∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε) →
        ∀ V, D.a < V → V < D.b →
          D.B V ≤ C * (D.A V + ε * D.B V + D.L V + D.N V +
            (D.Gamma V).toReal) := by
  obtain ⟨εraw, hεraw, Ct, hCt, Qt, hQt, Rt, hRt, Cd, hCd, hraw⟩ :=
    D.beta_ratio_goodV_integral_bound ha hb
  let ε₀ := min εraw 1
  have hε₀ : 0 < ε₀ := lt_min hεraw (by norm_num)
  let C := 1 + Qt * (1 + Ct) + Rt * Cd
  have hC : 1 ≤ C := by
    dsimp [C]
    have hQt : 0 ≤ Qt * (1 + Ct) :=
      mul_nonneg (by linarith) (by linarith)
    have hRC : 0 ≤ Rt * Cd :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  refine ⟨ε₀, hε₀, C, hC, ?_⟩
  intro ε hε hε₀le hsmall V haV hVb
  have heone : ε ≤ 1 := hε₀le.trans (min_le_right _ _)
  have hεrawle : ε ≤ εraw := hε₀le.trans (min_le_left _ _)
  have hrawV := hraw ε hε hεrawle hsmall V haV hVb
  have hbound := beta_raw_le (D.A_nonneg V)
    (D.B_nonneg ha hVb.le) (D.L_nonneg haV hVb)
    (D.N_nonneg haV hVb)
    (show 0 ≤ (D.Gamma V).toReal from ENNReal.toReal_nonneg)
    hε heone (by linarith : 0 ≤ Ct)
    (by linarith : 0 ≤ Qt) (by linarith : 0 ≤ Rt)
    (by linarith : 0 ≤ Cd)
  dsimp [C] at hbound ⊢
  exact hrawV.trans hbound

end ChristodoulouBV.Uniqueness

end
