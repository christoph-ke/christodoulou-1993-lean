module

public import ChristodoulouBV.Uniqueness.IncomingMassHardy
public import ChristodoulouBV.Uniqueness.OutgoingMassHardy
public import ChristodoulouBV.Uniqueness.ExpansionFirstAbsorption

/-!
# Mass and expansion absorption before quotient transport

The Hardy and expansion constants are chosen first. A subsequent positive
variation threshold absorbs the feedback, uniformly in the compact top.
-/

@[expose] public section

open Set MeasureTheory

namespace ChristodoulouBV.Uniqueness

/-- Finite dimensional absorption of the two mass and two expansion estimates. -/
private theorem absorb
    {A B L N G J e H K : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hL : 0 ≤ L) (_hN : 0 ≤ N)
    (hG : 0 ≤ G) (hJ : 0 ≤ J) (he : 0 ≤ e) (heone : e ≤ 1)
    (hH : 1 ≤ H) (hK : 1 ≤ K) (hsmall : 4 * K * H * e ≤ 1)
    (hGbound : G ≤ H * e * (A + L))
    (hJbound : J ≤ H * e * (B + N))
    (hLbound : L ≤ K * (G + J))
    (hNbound : N ≤ K * (G + J)) :
    G ≤ H * (1 + 2 * K * H) * e * (A + e * B) ∧
    J ≤ H * (1 + 2 * K * H) * e * (e * A + B) ∧
    L ≤ 2 * K * H * e * (A + B) ∧
    N ≤ 2 * K * H * e * (A + B) := by
  have hHp : 0 ≤ H := by linarith
  have hKp : 0 ≤ K := by linarith
  have hT : G + J ≤ 2 * H * e * (A + B) := by
    have hsum : G + J ≤ H * e * (A + B + L + N) := by
      nlinarith [mul_nonneg (mul_nonneg hHp he) _hL,
        mul_nonneg (mul_nonneg hHp he) _hN]
    have hLN : L + N ≤ 2 * K * (G + J) := by linarith only [hLbound, hNbound]
    have hcoeff : 2 * K * H * e ≤ 1 / 2 := by linarith only [hsmall]
    have hprod := mul_le_mul_of_nonneg_left hLN (mul_nonneg hHp he)
    have hfactor : 0 ≤ G + J := add_nonneg hG hJ
    have hfactor2 := mul_le_mul_of_nonneg_right hcoeff hfactor
    nlinarith only [hsum, hprod, hfactor2]
  have hLm : L ≤ 2 * K * H * e * (A + B) := by
    calc
      L ≤ K * (G + J) := hLbound
      _ ≤ K * (2 * H * e * (A + B)) := mul_le_mul_of_nonneg_left hT hKp
      _ = 2 * K * H * e * (A + B) := by ring
  have hNm : N ≤ 2 * K * H * e * (A + B) := by
    calc
      N ≤ K * (G + J) := hNbound
      _ ≤ K * (2 * H * e * (A + B)) := mul_le_mul_of_nonneg_left hT hKp
      _ = 2 * K * H * e * (A + B) := by ring
  have hGM : G ≤ H * (1 + 2 * K * H) * e * (A + e * B) := by
    have hstep := mul_le_mul_of_nonneg_left hLm (mul_nonneg hHp he)
    have hX : 0 ≤ 2 * K * H := by positivity
    have hAprod := mul_le_mul_of_nonneg_left heone hA
    have hAprod2 := mul_le_mul_of_nonneg_left hAprod (mul_nonneg (mul_nonneg hHp hX) he)
    nlinarith only [hGbound, hstep, hAprod2, mul_nonneg (mul_nonneg (mul_nonneg hHp he) he) hB]
  have hJM : J ≤ H * (1 + 2 * K * H) * e * (e * A + B) := by
    have hstep := mul_le_mul_of_nonneg_left hNm (mul_nonneg hHp he)
    have hX : 0 ≤ 2 * K * H := by positivity
    have hBprod := mul_le_mul_of_nonneg_left heone hB
    have hBprod2 := mul_le_mul_of_nonneg_left hBprod (mul_nonneg (mul_nonneg hHp hX) he)
    nlinarith only [hJbound, hstep, hBprod2, mul_nonneg (mul_nonneg (mul_nonneg hHp he) he) hA]
  exact ⟨hGM, hJM, hLm, hNm⟩

/-- Stable forms of (3.18) and (3.19). The mass and expansion constants are
fixed before the small variation parameter and are uniform in the compact
top. The full incoming axis and both zero mass traces used in the incoming
Hardy theorem follow from `D.hT`. -/
theorem ComparisonData.mass_norms_after_absorption (D : ComparisonData)
    (ha : D.a = 0) (hb : D.b = 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
        (∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε) →
        ∀ V, D.a < V → V < D.b →
          (D.Gamma V).toReal ≤ C * ε * (D.A V + ε * D.B V) ∧
          (D.GammaStar V).toReal ≤ C * ε * (ε * D.A V + D.B V) ∧
          D.L V ≤ C * ε * (D.A V + D.B V) ∧
          D.N V ≤ C * ε * (D.A V + D.B V) := by
  obtain ⟨εout, hεout, Cout, hCout, hout⟩ :=
    D.Gamma_le_epsilon_A_L ha hb
  obtain ⟨_, _, εin, hεin, Cin, hCin, hin⟩ :=
    D.GammaStar_le_epsilon_B_N ha hb
  obtain ⟨_, _, _, _, _, _, Cexp, hCexp, εexp, hεexp, hexp⟩ :=
    D.expansion_norms_le_mass_norms ha
  let H := max Cout (max Cin 1)
  let K := 2 * Cexp ^ 2
  have hH : 1 ≤ H := (le_max_right Cin 1).trans (le_max_right Cout _)
  have hK : 1 ≤ K := by dsimp [K]; nlinarith [sq_nonneg (Cexp - 1)]
  have hKpos : 0 < K := by linarith
  have hHpos : 0 < H := by linarith
  have hCoutH : Cout ≤ H := le_max_left _ _
  have hCinH : Cin ≤ H := (le_max_left Cin 1).trans (le_max_right Cout _)
  let C := max 1 (max (H * (1 + 2 * K * H)) (2 * K * H))
  have hC : 1 ≤ C := le_max_left _ _
  have hCmass : H * (1 + 2 * K * H) ≤ C :=
    (le_max_left _ _).trans (le_max_right 1 _)
  have hCexp : 2 * K * H ≤ C :=
    (le_max_right _ _).trans (le_max_right 1 _)
  let ε₀ := min εout (min εin (min εexp (min 1 (1 / (4 * K * H)))))
  have hden : 0 < 4 * K * H := by positivity
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    exact lt_min hεout (lt_min hεin (lt_min hεexp
      (lt_min (by norm_num) (one_div_pos.mpr hden))))
  refine ⟨ε₀, hε₀, C, hC, ?_⟩
  intro ε hε hε₀le hsmall V haV hVb
  have hεoutLe : ε ≤ εout := hε₀le.trans (min_le_left _ _)
  have hεinLe : ε ≤ εin :=
    hε₀le.trans (min_le_right _ _) |>.trans (min_le_left _ _)
  have hεexpLe : ε ≤ εexp :=
    hε₀le.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans
      (min_le_left _ _)
  have hεone : ε ≤ 1 :=
    hε₀le.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans
      (min_le_right _ _) |>.trans (min_le_left _ _)
  have hεden : ε ≤ 1 / (4 * K * H) :=
    hε₀le.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans
      (min_le_right _ _) |>.trans (min_le_right _ _)
  have hεsmall : 4 * K * H * ε ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hεden hden.le
    have heq : 4 * K * H * (1 / (4 * K * H)) = 1 := by
      field_simp [hden.ne']
    rw [heq] at hh
    exact hh
  have hsmallOut : ∀ u v, (u, v) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ εout ∧
        (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ εout := by
    intro u v huv S hS
    obtain ⟨ho, hi⟩ := hsmall u v huv S hS
    exact ⟨ho.trans hεoutLe, hi.trans hεoutLe⟩
  have hsmallExp : ∀ u v, (u, v) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε ∧
        (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε := hsmall
  have hvar : ∀ u v, (u, v) ∈ triangle D.a D.b →
      (eVariationOn (D.S₁.phi u) (Ioc u v)).toReal ≤ ε ∧
      (eVariationOn (D.S₂.phi u) (Ioc u v)).toReal ≤ ε := by
    intro u v huv
    exact ⟨(hsmall u v huv D.S₁ (Or.inl rfl)).1,
      (hsmall u v huv D.S₂ (Or.inr rfl)).1⟩
  have hGout := hout ε hε hsmallOut hvar V haV hVb
  have hGin := (hin ε hε hεinLe hsmall V haV hVb).1
  have hJin : (D.GammaStar V).toReal ≤
      Cin * ε * (D.B V + D.N V) := by
    have hB : 0 ≤ D.B V := D.B_nonneg ha hVb.le
    have hN : 0 ≤ D.N V := D.N_nonneg haV hVb
    have htarget : 0 ≤ Cin * ε * (D.B V + D.N V) := by positivity
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hGin
    simpa only [ENNReal.toReal_ofReal htarget] using hh
  obtain ⟨_, _, hLexp, hNexp⟩ :=
    hexp ε hε hεexpLe hsmallExp V haV hVb
  have hA : 0 ≤ D.A V := D.A_nonneg V
  have hB : 0 ≤ D.B V := D.B_nonneg ha hVb.le
  have hG : 0 ≤ (D.Gamma V).toReal := ENNReal.toReal_nonneg
  have hJ : 0 ≤ (D.GammaStar V).toReal := ENNReal.toReal_nonneg
  have hGbound : (D.Gamma V).toReal ≤
      H * ε * (D.A V + D.L V) := by
    have hsum : 0 ≤ ε * (D.A V + D.L V) :=
      mul_nonneg hε (add_nonneg hA (D.L_nonneg haV hVb))
    calc
      (D.Gamma V).toReal ≤ Cout * ε * (D.A V + D.L V) := hGout
      _ = Cout * (ε * (D.A V + D.L V)) := by ring
      _ ≤ H * (ε * (D.A V + D.L V)) :=
        mul_le_mul_of_nonneg_right hCoutH hsum
      _ = H * ε * (D.A V + D.L V) := by ring
  have hJbound : (D.GammaStar V).toReal ≤
      H * ε * (D.B V + D.N V) := by
    have hsum : 0 ≤ ε * (D.B V + D.N V) :=
      mul_nonneg hε (add_nonneg hB (D.N_nonneg haV hVb))
    calc
      (D.GammaStar V).toReal ≤ Cin * ε * (D.B V + D.N V) := hJin
      _ = Cin * (ε * (D.B V + D.N V)) := by ring
      _ ≤ H * (ε * (D.B V + D.N V)) :=
        mul_le_mul_of_nonneg_right hCinH hsum
      _ = H * ε * (D.B V + D.N V) := by ring
  have hLbound : D.L V ≤ K * ((D.Gamma V).toReal +
      (D.GammaStar V).toReal) := by simpa only [K] using hLexp
  have hNbound : D.N V ≤ K * ((D.Gamma V).toReal +
      (D.GammaStar V).toReal) := by simpa only [K] using hNexp
  obtain ⟨hGfinal, hJfinal, hLfinal, hNfinal⟩ :=
    absorb hA hB (D.L_nonneg haV hVb) (D.N_nonneg haV hVb)
      hG hJ hε hεone hH hK hεsmall
      hGbound hJbound hLbound hNbound
  have hAB : 0 ≤ D.A V + D.B V := add_nonneg hA hB
  have hAeB : 0 ≤ D.A V + ε * D.B V :=
    add_nonneg hA (mul_nonneg hε hB)
  have heAB : 0 ≤ ε * D.A V + D.B V :=
    add_nonneg (mul_nonneg hε hA) hB
  constructor
  · calc
      (D.Gamma V).toReal ≤
          H * (1 + 2 * K * H) * ε * (D.A V + ε * D.B V) := hGfinal
      _ = (H * (1 + 2 * K * H)) * (ε * (D.A V + ε * D.B V)) := by ring
      _ ≤ C * (ε * (D.A V + ε * D.B V)) :=
        mul_le_mul_of_nonneg_right hCmass (mul_nonneg hε hAeB)
      _ = C * ε * (D.A V + ε * D.B V) := by ring
  constructor
  · calc
      (D.GammaStar V).toReal ≤
          H * (1 + 2 * K * H) * ε * (ε * D.A V + D.B V) := hJfinal
      _ = (H * (1 + 2 * K * H)) * (ε * (ε * D.A V + D.B V)) := by ring
      _ ≤ C * (ε * (ε * D.A V + D.B V)) :=
        mul_le_mul_of_nonneg_right hCmass (mul_nonneg hε heAB)
      _ = C * ε * (ε * D.A V + D.B V) := by ring
  constructor
  · calc
      D.L V ≤ 2 * K * H * ε * (D.A V + D.B V) := hLfinal
      _ = (2 * K * H) * (ε * (D.A V + D.B V)) := by ring
      _ ≤ C * (ε * (D.A V + D.B V)) :=
        mul_le_mul_of_nonneg_right hCexp (mul_nonneg hε hAB)
      _ = C * ε * (D.A V + D.B V) := by ring
  · calc
      D.N V ≤ 2 * K * H * ε * (D.A V + D.B V) := hNfinal
      _ = (2 * K * H) * (ε * (D.A V + D.B V)) := by ring
      _ ≤ C * (ε * (D.A V + D.B V)) :=
        mul_le_mul_of_nonneg_right hCexp (mul_nonneg hε hAB)
      _ = C * ε * (D.A V + D.B V) := by ring

end ChristodoulouBV.Uniqueness

end
