module

public import ChristodoulouBV.Uniqueness.QuotientTransport
public import ChristodoulouBV.Uniqueness.RadiusScalar
public import ChristodoulouBV.Uniqueness.OutgoingMassHardy
public import ChristodoulouBV.Uniqueness.GammaFinite
public import ChristodoulouBV.Uniqueness.ScalarOutgoingIdentity

/-!
# Contraction on a small BV comparison triangle

The cutoff-independent estimates are contracted on each compact top. The
pointwise conclusion concerns the continuous primary fields only; it makes
no assertion about values of the BV density representatives at exceptional
incoming coordinates.
-/

@[expose] public section

open Set
open MeasureTheory
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- All six stable comparison norms vanish on every compact top once the
variation is below a single strictly positive threshold. The four real
suprema and both extended mass suprema are finite at that threshold. -/
theorem ComparisonData.goodV_norms_zero (D : ComparisonData)
    (ha : D.a = 0) (hb : D.b = 1) :
    ∃ εfinal : ℝ, 0 < εfinal ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ εfinal →
        (∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε) →
        ∀ V, D.a < V → V < D.b →
          D.A V = 0 ∧ D.B V = 0 ∧ D.L V = 0 ∧ D.N V = 0 ∧
          D.Gamma V = 0 ∧ D.GammaStar V = 0 := by
  obtain ⟨εq, hεq, Cq, hCq, hq⟩ := D.quotient_norms_absorb ha hb
  obtain ⟨εm, hεm, Cm, hCm, hm⟩ := D.mass_norms_after_absorption ha hb
  obtain ⟨_, _, εf, hεf, _, _, hfinite⟩ := D.finite_goodV_norms ha hb
  obtain ⟨Mg, hMg, hGfinite⟩ := D.Gamma_uniform_bound
  obtain ⟨Mj, hMj, hJfinite⟩ := D.GammaStar_uniform_bound
  let εfinal := min εq (min εm (min εf (1 / (2 * Cq ^ 2))))
  have hCqpos : 0 < Cq := by linarith
  have hden : 0 < 2 * Cq ^ 2 := by positivity
  have hεfinal : 0 < εfinal := by
    dsimp [εfinal]
    exact lt_min hεq (lt_min hεm (lt_min hεf (one_div_pos.mpr hden)))
  refine ⟨εfinal, hεfinal, ?_⟩
  intro ε hε hεle hsmall V haV hVb
  have hεqle : ε ≤ εq := hεle.trans (min_le_left _ _)
  have hεmle : ε ≤ εm :=
    hεle.trans (min_le_right _ _) |>.trans (min_le_left _ _)
  have hεfle : ε ≤ εf :=
    hεle.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans
      (min_le_left _ _)
  have hεden : ε ≤ 1 / (2 * Cq ^ 2) :=
    hεle.trans (min_le_right _ _) |>.trans (min_le_right _ _) |>.trans
      (min_le_right _ _)
  have hcoeff : Cq ^ 2 * ε ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hεden (sq_nonneg Cq)
    have heq : Cq ^ 2 * (1 / (2 * Cq ^ 2)) = 1 / 2 := by
      field_simp [hCqpos.ne']
    rw [heq] at hh
    exact hh
  have hsmallF : ∀ u v, (u, v) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ εf ∧
        (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ εf := by
    intro u v huv S hS
    obtain ⟨ho, hi⟩ := hsmall u v huv S hS
    exact ⟨ho.trans hεfle, hi.trans hεfle⟩
  have hfiniteV := hfinite hsmallF V haV hVb
  obtain ⟨hAq, hBq⟩ := hq ε hε hεqle hsmall V haV hVb
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
  obtain ⟨hG, hJ, hL, hN⟩ := hm ε hε hεmle hsmall V haV hVb
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

private theorem ComparisonData.lambda_diff_le_L_good (D : ComparisonData)
    (ha : D.a = 0) (hb : D.b = 1)
    {V u v : ℝ} (hVb : V ≤ D.b)
    (huv : (u, v) ∈ triangle D.a V) (hvG : v ∈ D.goodV) :
    |D.S₁.lam u v - D.S₂.lam u v| ≤ D.L V := by
  have hw : (D.a, (1 / 2 : ℝ)) ∈ triangle D.a D.b := by
    rw [ha, hb]
    exact initial_edge_of_triangle (by norm_num) (by norm_num)
  have href : (0, (1 / 2 : ℝ)) ∈ D.U₁ ∩ D.U₂ := by
    simpa only [ha] using D.hT hw
  have hdatum : D.S₁.phi 0 (1 / 2 : ℝ) =
      D.S₂.phi 0 (1 / 2 : ℝ) := by
    simpa only [ha] using (D.hdata (1 / 2 : ℝ)
      (by rw [ha, hb]; constructor <;> norm_num)).2
  obtain ⟨c, C, hc, hC, hfield⟩ :=
    D.h₁.preloc_coefficient_bounds D.h₂ href hdatum
  have hbound (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V)
      (_hyG : y ∈ D.goodV) :
      |D.S₁.lam x y - D.S₂.lam x y| ≤ 2 * C := by
    have hfull : (x, y) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨hxy.1, hxy.2.1, hxy.2.2.trans_le hVb⟩
    have hp := D.hT hfull
    have hlam₁ := (hfield D.a D.b x y D.hT hfull D.S₁ (Or.inl rfl)).2.1
    have hlam₂ := (hfield D.a D.b x y D.hT hfull D.S₂ (Or.inr rfl)).2.1
    have hp₁ := D.h₁.solution.lam_pos (x,y) hp.1
    have hp₂ := D.h₂.solution.lam_pos (x,y) hp.2
    calc
      |D.S₁.lam x y - D.S₂.lam x y| ≤
          |D.S₁.lam x y| + |D.S₂.lam x y| := abs_sub _ _
      _ ≤ C + C := by simpa only [abs_of_pos hp₁, abs_of_pos hp₂] using
        (add_le_add hlam₁ hlam₂)
      _ = 2 * C := by ring
  exact D.le_goodVNorm (by positivity : 0 ≤ 2 * C) hbound huv hvG

private theorem ComparisonData.alpha_ratio_diff_le_A_good (D : ComparisonData)
    (ha : D.a = 0) (hb : D.b = 1)
    {V u v : ℝ} (hVb : V ≤ D.b)
    (huv : (u, v) ∈ triangle D.a V) (hvG : v ∈ D.goodV) :
    |D.S₁.alpha u v / D.S₁.lam u v -
      D.S₂.alpha u v / D.S₂.lam u v| ≤ D.A V := by
  have hw : (D.a, (1 / 2 : ℝ)) ∈ triangle D.a D.b := by
    rw [ha, hb]
    exact initial_edge_of_triangle (by norm_num) (by norm_num)
  have href : (0, (1 / 2 : ℝ)) ∈ D.U₁ ∩ D.U₂ := by
    simpa only [ha] using D.hT hw
  have hdatum : D.S₁.phi 0 (1 / 2 : ℝ) =
      D.S₂.phi 0 (1 / 2 : ℝ) := by
    simpa only [ha] using (D.hdata (1 / 2 : ℝ)
      (by rw [ha, hb]; constructor <;> norm_num)).2
  obtain ⟨c, C, hc, hC, hfield⟩ :=
    D.h₁.preloc_coefficient_bounds D.h₂ href hdatum
  let K := C + C * C
  let Q := K / c
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hQ : 0 ≤ Q := div_nonneg hK hc.le
  have hratio (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V)
      (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :
      |S.alpha x y / S.lam x y| ≤ Q := by
    have hfull : (x, y) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨hxy.1, hxy.2.1, hxy.2.2.trans_le hVb⟩
    obtain ⟨hlamLo, hlamHi, _, _, hphi, htheta, _⟩ :=
      hfield D.a D.b x y D.hT hfull S hS
    have hα : |S.alpha x y| ≤ K := by
      have heq : S.alpha x y = S.theta x y + S.lam x y * S.phi x y := by
        dsimp [Fields.theta]; ring
      rw [heq]
      calc
        |S.theta x y + S.lam x y * S.phi x y| ≤
            |S.theta x y| + |S.lam x y| * |S.phi x y| := by
          simpa only [abs_mul] using
            (abs_add_le (S.theta x y) (S.lam x y * S.phi x y))
        _ ≤ C + C * C := by
          have hlamPos : 0 < S.lam x y := hc.trans_le hlamLo
          rw [abs_of_pos hlamPos]
          exact add_le_add htheta
            ((mul_le_mul_of_nonneg_right hlamHi (abs_nonneg _)).trans
              (mul_le_mul_of_nonneg_left hphi hC))
        _ = K := rfl
    have hlamPos : 0 < S.lam x y := hc.trans_le hlamLo
    rw [abs_div, abs_of_pos hlamPos]
    apply (div_le_iff₀ hlamPos).2
    calc
      |S.alpha x y| ≤ K := hα
      _ = Q * c := by dsimp [Q]; field_simp [hc.ne']
      _ ≤ Q * S.lam x y := mul_le_mul_of_nonneg_left hlamLo hQ
  have hbound (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V)
      (_hyG : y ∈ D.goodV) :
      |D.S₁.alpha x y / D.S₁.lam x y -
        D.S₂.alpha x y / D.S₂.lam x y| ≤ 2 * Q := by
    calc
      _ ≤ |D.S₁.alpha x y / D.S₁.lam x y| +
          |D.S₂.alpha x y / D.S₂.lam x y| := abs_sub _ _
      _ ≤ Q + Q := add_le_add
        (hratio x y hxy D.S₁ (Or.inl rfl))
        (hratio x y hxy D.S₂ (Or.inr rfl))
      _ = 2 * Q := by ring
  exact D.le_goodVNorm (by positivity : 0 ≤ 2 * Q) hbound huv hvG

/-- Zero stable norms recover the three continuous primary fields at every
point of the open-top comparison triangle, including exceptional incoming
coordinates and the initial edge. -/
theorem ComparisonData.pointwise_of_goodV_norms_zero (D : ComparisonData)
    (ha : D.a = 0) (hb : D.b = 1) :
    (∀ V, D.a < V → V < D.b →
      D.A V = 0 ∧ D.B V = 0 ∧ D.L V = 0 ∧ D.N V = 0 ∧
      D.Gamma V = 0 ∧ D.GammaStar V = 0) →
    ∀ u v, (u, v) ∈ triangle D.a D.b →
      D.S₁.r u v = D.S₂.r u v ∧
      D.S₁.phi u v = D.S₂.phi u v ∧
      D.S₁.m u v = D.S₂.m u v := by
  intro hzero
  have hprimary (u v : ℝ) (huv : (u, v) ∈ triangle D.a D.b) :
      D.S₁.r u v = D.S₂.r u v ∧
      D.S₁.phi u v = D.S₂.phi u v := by
    let V := (v + D.b) / 2
    have hvV : v < V := by dsimp [V]; linarith [huv.2.2]
    have hVb : V < D.b := by dsimp [V]; linarith [huv.2.2]
    have haV : D.a < V := huv.1.trans_lt (huv.2.1.trans hvV)
    have hut : (u, v) ∈ triangle D.a V :=
      (mem_triangle).2 ⟨huv.1, huv.2.1, hvV⟩
    obtain ⟨hAz, _, hLz, _, _, _⟩ := hzero V haV hVb
    have hr := D.radius_diff_le_L hVb.le hut
    rw [hLz] at hr
    have hrz : D.S₁.r u v = D.S₂.r u v := by
      have hh : |D.S₁.r u v - D.S₂.r u v| ≤ 0 := by
        simpa only [mul_zero] using hr
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))
    have hboth : ∀ᵐ t ∂volume, t ∈ Ι u v →
        D.S₁.alpha u t / D.S₁.lam u t -
          D.S₂.alpha u t / D.S₂.lam u t = 0 ∧
        D.S₁.lam u t - D.S₂.lam u t = 0 := by
      filter_upwards [(D.goodV_properties).1] with t htG htI
      have ht : t ∈ Ioc u v := by
        simpa [uIoc_of_le huv.2.1.le] using htI
      have htT : (u, t) ∈ triangle D.a V :=
        (mem_triangle).2 ⟨huv.1, ht.1, ht.2.trans_lt hvV⟩
      have hq := D.alpha_ratio_diff_le_A_good ha hb hVb.le htT htG
      have hl := D.lambda_diff_le_L_good ha hb hVb.le htT htG
      rw [hAz] at hq
      rw [hLz] at hl
      exact ⟨abs_eq_zero.mp (le_antisymm hq (abs_nonneg _)),
        abs_eq_zero.mp (le_antisymm hl (abs_nonneg _))⟩
    have hfzero :
        (∫ t in u..v, D.S₁.lam u t *
          (D.S₁.alpha u t / D.S₁.lam u t -
            D.S₂.alpha u t / D.S₂.lam u t)) = 0 := by
      calc
        _ = ∫ t in u..v, (0 : ℝ) := by
          apply intervalIntegral.integral_congr_ae'
          · filter_upwards [hboth] with t ht htI
            have hI : t ∈ Ι u v := by
              simpa [uIoc_of_le huv.2.1.le] using htI
            simp only [(ht hI).1, mul_zero]
          · exact Filter.Eventually.of_forall (fun t ht =>
              (not_lt_of_ge huv.2.1.le (ht.1.trans_le ht.2)).elim)
        _ = 0 := by simp
    have hgzero :
        (∫ t in u..v,
          (D.S₂.alpha u t / D.S₂.lam u t) *
            (D.S₁.lam u t - D.S₂.lam u t)) = 0 := by
      calc
        _ = ∫ t in u..v, (0 : ℝ) := by
          apply intervalIntegral.integral_congr_ae'
          · filter_upwards [hboth] with t ht htI
            have hI : t ∈ Ι u v := by
              simpa [uIoc_of_le huv.2.1.le] using htI
            simp only [(ht hI).2, mul_zero]
          · exact Filter.Eventually.of_forall (fun t ht =>
              (not_lt_of_ge huv.2.1.le (ht.1.trans_le ht.2)).elim)
        _ = 0 := by simp
    have hid := D.phi_diff_outgoing_identity ha hb huv
    rw [hfzero, hgzero, hrz] at hid
    have hphi : D.S₁.phi u v = D.S₂.phi u v := by
      apply sub_eq_zero.mp
      simpa using hid
    exact ⟨hrz, hphi⟩
  intro u v huv
  obtain ⟨hr, hphi⟩ := hprimary u v huv
  let V := (v + D.b) / 2
  have hvV : v < V := by dsimp [V]; linarith [huv.2.2]
  have hVb : V < D.b := by dsimp [V]; linarith [huv.2.2]
  have hUV : (u, V) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨huv.1, huv.2.1.trans hvV, hVb⟩
  have hp := D.hT hUV
  have hdata : ∀ t, u < t → t ≤ V →
      D.S₁.r u t = D.S₂.r u t ∧
      D.S₁.phi u t = D.S₂.phi u t := by
    intro t hut htV
    exact hprimary u t ((mem_triangle).2
      ⟨huv.1, hut, htV.trans_lt hVb⟩)
  have hm := D.h₁.initial_mass_eq D.h₂ hp.1 hp.2 hdata
  exact ⟨hr, hphi, hm v ⟨huv.2.1, hvV.le⟩⟩

/-- Small variation uniqueness for two frozen BV solutions on a normalized
augmented local triangle. The threshold is chosen before the variation size
and is independent of the point or compact cutoff. -/
theorem ComparisonData.local_unique (D : ComparisonData)
    (ha : D.a = 0) (hb : D.b = 1) :
    ∃ εfinal : ℝ, 0 < εfinal ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ εfinal →
        (∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε) →
        ∀ u v, (u, v) ∈ triangle D.a D.b →
          D.S₁.r u v = D.S₂.r u v ∧
          D.S₁.phi u v = D.S₂.phi u v ∧
          D.S₁.m u v = D.S₂.m u v := by
  obtain ⟨εc, hεc, hcontract⟩ := D.goodV_norms_zero ha hb
  refine ⟨εc, hεc, ?_⟩
  intro ε hε hεle hsmall u v huv
  exact D.pointwise_of_goodV_norms_zero ha hb
    (hcontract ε hε hεle hsmall) u v huv

end ChristodoulouBV.Uniqueness

end
