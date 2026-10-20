module

public import ChristodoulouBV.Uniqueness.QuotientBetaNorm
public import ChristodoulouBV.Uniqueness.QuotientMassAbsorption

/-!
# Final finite dimensional quotient absorption
-/

@[expose] public section

open Set MeasureTheory

namespace ChristodoulouBV.Uniqueness

private def quotientFeedbackK
    (M Cs Js Q Ck Ct Qt Rt Cd : ℝ) : ℝ :=
  max 1 (max
    (Js * (1 + Cs * (1 + M)) + 2 * Q * Ck * M)
    (Qt * (1 + Ct * (1 + M)) + 2 * Rt * Cd * M))

private theorem quotient_feedback
    {A B L N G H e M Cs Js Q Ck Ct Qt Rt Cd : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 0 ≤ N)
    (he : 0 ≤ e) (heone : e ≤ 1)
    (hM : 1 ≤ M) (hCs : 0 ≤ Cs) (hJs : 0 ≤ Js)
    (hQ : 0 ≤ Q) (hCk : 0 ≤ Ck)
    (hCt : 0 ≤ Ct) (hQt : 0 ≤ Qt)
    (hRt : 0 ≤ Rt) (hCd : 0 ≤ Cd)
    (hLmass : L ≤ M * e * (A + B))
    (hNmass : N ≤ M * e * (A + B))
    (hGmass : G ≤ M * e * (A + B))
    (hHmass : H ≤ M * e * (A + B))
    (hAraw : A ≤ (A + Cs * (A + L)) * (Js * e) +
      Q * Ck * (e * N + H))
    (hBraw : B ≤ A + (B + Ct * (B + N)) * (Qt * e) +
      Rt * Cd * (L + G)) :
    let K := quotientFeedbackK M Cs Js Q Ck Ct Qt Rt Cd
    A ≤ K * e * (A + B) ∧
      B ≤ A + K * e * (A + B) := by
  let S := A + B
  have hS : 0 ≤ S := add_nonneg hA hB
  have hM0 : 0 ≤ M := by linarith
  have heS : e * S ≤ S := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right heone hS
  have hAS : A ≤ S := by dsimp [S]; linarith
  have hBS : B ≤ S := by dsimp [S]; linarith
  have hLS : L ≤ M * S := by
    have hh := mul_le_mul_of_nonneg_left heS hM0
    nlinarith only [hLmass, hh]
  have hNS : N ≤ M * S := by
    have hh := mul_le_mul_of_nonneg_left heS hM0
    nlinarith only [hNmass, hh]
  have heN : e * N ≤ N := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right heone hN
  have hNH : e * N + H ≤ 2 * M * e * S := by
    dsimp [S]
    nlinarith only [heN, hNmass, hHmass]
  have hLG : L + G ≤ 2 * M * e * S := by
    dsimp [S]
    nlinarith only [hLmass, hGmass]
  have hAinner : A + Cs * (A + L) ≤
      (1 + Cs * (1 + M)) * S := by
    have hAL : A + L ≤ (1 + M) * S := by
      nlinarith only [hAS, hLS]
    have hh := mul_le_mul_of_nonneg_left hAL hCs
    nlinarith only [hAS, hh]
  have hBinner : B + Ct * (B + N) ≤
      (1 + Ct * (1 + M)) * S := by
    have hBN : B + N ≤ (1 + M) * S := by
      nlinarith only [hBS, hNS]
    have hh := mul_le_mul_of_nonneg_left hBN hCt
    nlinarith only [hBS, hh]
  let KA := Js * (1 + Cs * (1 + M)) + 2 * Q * Ck * M
  let KB := Qt * (1 + Ct * (1 + M)) + 2 * Rt * Cd * M
  let K := quotientFeedbackK M Cs Js Q Ck Ct Qt Rt Cd
  have hKdef : K = max 1 (max KA KB) := rfl
  have hK : 1 ≤ K := hKdef ▸ le_max_left _ _
  have hKA0 : 0 ≤ KA := by
    dsimp [KA]
    positivity
  have hKB0 : 0 ≤ KB := by
    dsimp [KB]
    positivity
  have hKA : KA ≤ K := hKdef ▸
    (le_max_left KA KB).trans (le_max_right 1 _)
  have hKB : KB ≤ K := hKdef ▸
    (le_max_right KA KB).trans (le_max_right 1 _)
  have hAfb : A ≤ KA * e * S := by
    have hfac : 0 ≤ Js * e := mul_nonneg hJs he
    have hprod := mul_le_mul_of_nonneg_right hAinner hfac
    have hfac₂ : 0 ≤ Q * Ck := mul_nonneg hQ hCk
    have hprod₂ := mul_le_mul_of_nonneg_left hNH hfac₂
    calc
      A ≤ (A + Cs * (A + L)) * (Js * e) +
        Q * Ck * (e * N + H) := hAraw
      _ ≤ ((1 + Cs * (1 + M)) * S) * (Js * e) +
        Q * Ck * (2 * M * e * S) := add_le_add hprod hprod₂
      _ = KA * e * S := by dsimp [KA]; ring
  have hBfb : B ≤ A + KB * e * S := by
    have hfac : 0 ≤ Qt * e := mul_nonneg hQt he
    have hprod := mul_le_mul_of_nonneg_right hBinner hfac
    have hfac₂ : 0 ≤ Rt * Cd := mul_nonneg hRt hCd
    have hprod₂ := mul_le_mul_of_nonneg_left hLG hfac₂
    calc
      B ≤ A + (B + Ct * (B + N)) * (Qt * e) +
        Rt * Cd * (L + G) := hBraw
      _ ≤ A + ((1 + Ct * (1 + M)) * S) * (Qt * e) +
        Rt * Cd * (2 * M * e * S) := by linarith only [hprod, hprod₂]
      _ = A + KB * e * S := by dsimp [KB]; ring
  have heS0 : 0 ≤ e * S := mul_nonneg he hS
  have hAK := mul_le_mul_of_nonneg_right hKA heS0
  have hBK := mul_le_mul_of_nonneg_right hKB heS0
  change A ≤ K * e * (A + B) ∧
    B ≤ A + K * e * (A + B)
  constructor
  · dsimp [S] at hAfb ⊢
    nlinarith only [hAfb, hAK]
  · dsimp [S] at hBfb ⊢
    nlinarith only [hBfb, hBK]

private theorem quotient_feedback_absorb
    {A B e K : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (_he : 0 ≤ e) (_hK : 1 ≤ K)
    (hsmall : 2 * K * e ≤ 1)
    (hAf : A ≤ K * e * (A + B))
    (hBf : B ≤ A + K * e * (A + B)) :
    A ≤ 2 * K * e * B ∧ B ≤ 3 * A := by
  have hKe : K * e ≤ 1 / 2 := by linarith only [hsmall]
  have hKA := mul_le_mul_of_nonneg_right hKe hA
  have hKB := mul_le_mul_of_nonneg_right hKe hB
  constructor
  · nlinarith only [hAf, hKA]
  · nlinarith only [hBf, hKA, hKB]

/-- Stable forms of (3.20) and (3.21). The preliminary coefficient choices,
the absorption threshold, and the final constant are independent of the
compact top. The full triangle supplies the axis trace and the coefficient absorption hypotheses. -/
theorem ComparisonData.stable_quotient_estimates
    (D : ComparisonData) (ha : D.a = 0) (hb : D.b = 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
        (∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε) →
        ∀ V, D.a < V → V < D.b →
          D.A V ≤ C * ε * D.B V ∧ D.B V ≤ C * D.A V := by
  obtain ⟨εA, hεA, Cs, hCs, Q, hQ, Ck, hCk, Js, hJs, hAest⟩ :=
    D.alpha_ratio_goodV_integral_bound ha hb
  obtain ⟨εB, hεB, Ct, hCt, Qt, hQt, Rt, hRt, Cd, hCd, hBest⟩ :=
    D.beta_ratio_goodV_integral_bound ha hb
  obtain ⟨εm, hεm, Cm, hCm, hmass⟩ :=
    D.mass_norms_after_absorption ha hb
  let M := max 1 Cm
  have hM : 1 ≤ M := le_max_left _ _
  have hCmM : Cm ≤ M := le_max_right _ _
  have hCm0 : 0 ≤ Cm := by linarith
  let K := quotientFeedbackK M Cs Js Q Ck Ct Qt Rt Cd
  have hK : 1 ≤ K := by
    dsimp [K, quotientFeedbackK]
    exact le_max_left _ _
  have hKpos : 0 < K := by linarith
  let C := max (2 * K) 3
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith [le_max_right (2 * K) 3]
  have hCleft : 2 * K ≤ C := le_max_left _ _
  have hCright : 3 ≤ C := le_max_right _ _
  let ε₀ := min εA (min εB (min εm (min 1 (1 / (2 * K)))))
  have hden : 0 < 2 * K := by positivity
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    exact lt_min hεA (lt_min hεB (lt_min hεm
      (lt_min (by norm_num) (one_div_pos.mpr hden))))
  refine ⟨ε₀, hε₀, C, hC, ?_⟩
  intro ε hε hε₀le hsmall V haV hVb
  have hεAle : ε ≤ εA := hε₀le.trans (min_le_left _ _)
  have hεBle : ε ≤ εB :=
    hε₀le.trans (min_le_right _ _) |>.trans (min_le_left _ _)
  have hεmle : ε ≤ εm :=
    hε₀le.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans
      (min_le_left _ _)
  have heone : ε ≤ 1 :=
    hε₀le.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans
      (min_le_right _ _) |>.trans (min_le_left _ _)
  have hεK : ε ≤ 1 / (2 * K) :=
    hε₀le.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans
      (min_le_right _ _) |>.trans (min_le_right _ _)
  have hAraw := hAest ε hε hεAle hsmall V haV hVb
  have hBraw := hBest ε hε hεBle hsmall V haV hVb
  obtain ⟨hG, hH, hL, hN⟩ := hmass ε hε hεmle hsmall V haV hVb
  have hA : 0 ≤ D.A V := D.A_nonneg V
  have hB : 0 ≤ D.B V := D.B_nonneg ha hVb.le
  have hN0 : 0 ≤ D.N V := D.N_nonneg haV hVb
  have hS : 0 ≤ D.A V + D.B V := add_nonneg hA hB
  have hES : 0 ≤ ε * (D.A V + D.B V) := mul_nonneg hε hS
  have hCmStep := mul_le_mul_of_nonneg_right hCmM hES
  have hMassL : D.L V ≤ M * ε * (D.A V + D.B V) := by
    nlinarith only [hL, hCmStep]
  have hMassN : D.N V ≤ M * ε * (D.A V + D.B V) := by
    nlinarith only [hN, hCmStep]
  have hAε : ε * D.A V ≤ D.A V := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right heone hA
  have hBε : ε * D.B V ≤ D.B V := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right heone hB
  have hGinner : D.A V + ε * D.B V ≤ D.A V + D.B V := by
    linarith only [hBε]
  have hHinner : ε * D.A V + D.B V ≤ D.A V + D.B V := by
    linarith only [hAε]
  have hCmε : 0 ≤ Cm * ε := mul_nonneg hCm0 hε
  have hMassG : (D.Gamma V).toReal ≤
      M * ε * (D.A V + D.B V) := by
    have hh := mul_le_mul_of_nonneg_left hGinner hCmε
    nlinarith only [hG, hh, hCmStep]
  have hMassH : (D.GammaStar V).toReal ≤
      M * ε * (D.A V + D.B V) := by
    have hh := mul_le_mul_of_nonneg_left hHinner hCmε
    nlinarith only [hH, hh, hCmStep]
  have hfeedback := quotient_feedback hA hB hN0 hε heone hM
    (by linarith : 0 ≤ Cs) hJs (by linarith : 0 ≤ Q)
    (by linarith : 0 ≤ Ck) (by linarith : 0 ≤ Ct)
    (by linarith : 0 ≤ Qt) (by linarith : 0 ≤ Rt)
    (by linarith : 0 ≤ Cd)
    hMassL hMassN hMassG hMassH hAraw hBraw
  have hsmallK : 2 * K * ε ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hεK hden.le
    have hneq : 2 * K ≠ 0 := ne_of_gt hden
    have hval : (1 / (2 * K)) * (2 * K) = 1 := by
      field_simp [hneq]
    nlinarith only [hh, hval]
  have hfinal := quotient_feedback_absorb hA hB hε hK
    hsmallK hfeedback.1 hfeedback.2
  constructor
  · have hbound := mul_le_mul_of_nonneg_right hCleft
      (mul_nonneg hε hB)
    nlinarith only [hfinal.1, hbound]
  · have hbound := mul_le_mul_of_nonneg_right hCright hA
    nlinarith only [hfinal.2, hbound]

end ChristodoulouBV.Uniqueness

end
