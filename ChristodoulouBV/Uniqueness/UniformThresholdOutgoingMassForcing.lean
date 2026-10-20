module

public import ChristodoulouBV.Uniqueness.UniformThresholdThetaGood
public import ChristodoulouBV.Uniqueness.OutgoingMassTransport

/-!
# Package-uniform outgoing mass forcing

The forcing weight is selected from the shared field and radius bounds before
normalized comparison data are selected.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- On good incoming rays, the source of the damped mass equation is bounded
by the stable quotient and expansion norms times the outgoing θ amplitude.
All constants are chosen before the final smallness parameter. -/
theorem UniformThresholdBounds.outgoingMassForcing_goodV_le
    (P : UniformThresholdBounds) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ P.gapThreshold) →
        ∀ V u t, D.a < V → V < D.b →
          (u, t) ∈ triangle D.a V → t ∈ D.goodV →
          |D.outgoingMassForcing u t| ≤
            2 * C ^ 3 * (D.A V + D.L V) *
              (|D.S₁.theta u t| + |D.S₂.theta u t|)) := by
  obtain ⟨Cθ, hCθ, hθgood⟩ := P.theta_diff_goodV_le
  let c₁ := P.c
  let c₂ := P.c
  let cR := P.radiusLower
  let B := P.C
  have hc₁ : 0 < c₁ := P.c_pos
  have hc₂ : 0 < c₂ := P.c_pos
  have hcR : 0 < cR := P.radiusLower_pos
  let C := max 1 (max Cθ (max B (max (1 / c₁) (max (1 / c₂) (1 / cR)))))
  have hC : 1 ≤ C := le_max_left _ _
  have hCθ' : Cθ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hB : B ≤ C :=
    (le_max_left _ _).trans (le_max_right _ _) |>.trans (le_max_right _ _)
  have hc₁inv : 1 / c₁ ≤ C := by
    exact (le_max_left _ _).trans (le_max_right _ _) |>.trans
      (le_max_right _ _) |>.trans (le_max_right _ _)
  have hc₂inv : 1 / c₂ ≤ C := by
    exact (le_max_left _ _).trans (le_max_right _ _) |>.trans
      (le_max_right _ _) |>.trans (le_max_right _ _) |>.trans
      (le_max_right _ _)
  have hcRinv : 1 / cR ≤ C := by
    exact (le_max_right _ _).trans (le_max_right _ _) |>.trans
      (le_max_right _ _) |>.trans (le_max_right _ _) |>.trans
      (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro D ha hb hP hsmall V u t haV hVb hut htG
  have hfull : (u, t) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨hut.1, hut.2.1, hut.2.2.trans hVb⟩
  have hp := D.hT hfull
  have hfull' : (u, t) ∈ triangle 0 1 := by
    simpa only [ha, hb] using hfull
  obtain ⟨hlam₁, _, _, _, _, _, _, hradloP, _⟩ :=
    hP u t hfull' D.S₁ (Or.inl rfl)
  obtain ⟨hlam₂, _, _, _, _, htheta₂, _, _, _⟩ :=
    hP u t hfull' D.S₂ (Or.inr rfl)
  have hd : 0 < t - u := sub_pos.mpr hut.2.1
  have hr : 0 < D.S₁.r u t := D.h₁.solution.radius_pos (u, t) hp.1
  have hl₁ : 0 < D.S₁.lam u t := D.h₁.solution.lam_pos (u, t) hp.1
  have hl₂ : 0 < D.S₂.lam u t := D.h₂.solution.lam_pos (u, t) hp.2
  have hL : 0 ≤ D.L V := D.L_nonneg haV hVb
  have hA : 0 ≤ D.A V := D.A_nonneg V
  have hAL : 0 ≤ D.A V + D.L V := add_nonneg hA hL
  have hC0 : 0 ≤ C := by linarith
  have hmu₁ := D.h₁.mass_ratio_bounds hp.1
  have hmu₂ := D.h₂.mass_ratio_bounds hp.2
  change 0 ≤ IsBVSolution.mu D.S₁ u t ∧
    IsBVSolution.mu D.S₁ u t < 1 at hmu₁
  change 0 ≤ IsBVSolution.mu D.S₂ u t ∧
    IsBVSolution.mu D.S₂ u t < 1 at hmu₂
  have hR0 : 0 ≤ (1 - IsBVSolution.mu D.S₁ u t) / D.S₁.lam u t :=
    div_nonneg (by linarith [hmu₁.2]) hl₁.le
  have hRle : (1 - IsBVSolution.mu D.S₁ u t) / D.S₁.lam u t ≤ C := by
    have hgap : 1 - IsBVSolution.mu D.S₁ u t ≤ 1 := by linarith [hmu₁.1]
    have hdiv : (1 - IsBVSolution.mu D.S₁ u t) / D.S₁.lam u t ≤
        1 / D.S₁.lam u t :=
      div_le_div_of_nonneg_right hgap hl₁.le
    have hrec : 1 / D.S₁.lam u t ≤ 1 / c₁ :=
      one_div_le_one_div_of_le hc₁ hlam₁
    exact hdiv.trans (hrec.trans hc₁inv)
  have hq0 : 0 ≤ D.S₂.theta u t ^ 2 / D.S₂.lam u t :=
    div_nonneg (sq_nonneg _) hl₂.le
  have hqle : D.S₂.theta u t ^ 2 / D.S₂.lam u t ≤
      C ^ 2 * |D.S₂.theta u t| := by
    have hθB : |D.S₂.theta u t| ≤ B := htheta₂
    have hθC : |D.S₂.theta u t| ≤ C := hθB.trans hB
    have hnum : D.S₂.theta u t ^ 2 ≤ C * |D.S₂.theta u t| := by
      calc
        D.S₂.theta u t ^ 2 = |D.S₂.theta u t| * |D.S₂.theta u t| := by
          rw [← sq_abs]
          ring
        _ ≤ C * |D.S₂.theta u t| :=
          mul_le_mul_of_nonneg_right hθC (abs_nonneg _)
    have hrec : 1 / D.S₂.lam u t ≤ C :=
      (one_div_le_one_div_of_le hc₂ hlam₂).trans hc₂inv
    calc
      D.S₂.theta u t ^ 2 / D.S₂.lam u t ≤
          (C * |D.S₂.theta u t|) / D.S₂.lam u t :=
        div_le_div_of_nonneg_right hnum hl₂.le
      _ = (C * |D.S₂.theta u t|) * (1 / D.S₂.lam u t) := by ring
      _ ≤ (C * |D.S₂.theta u t|) * C :=
        mul_le_mul_of_nonneg_left hrec (mul_nonneg hC0 (abs_nonneg _))
      _ = C ^ 2 * |D.S₂.theta u t| := by ring
  have hradlo : cR * (t - u) ≤ D.S₁.r u t := hradloP
  have hΔr := D.radius_diff_le_L hVb.le hut
  have hΔlam := D.lam_diff_le_L_good hVb.le hut htG
  have hrterm : IsBVSolution.mu D.S₂ u t *
      |D.S₁.r u t - D.S₂.r u t| / D.S₁.r u t ≤ C * D.L V := by
    have hradquot : |D.S₁.r u t - D.S₂.r u t| / D.S₁.r u t ≤
        D.L V / cR := by
      have h₁ : |D.S₁.r u t - D.S₂.r u t| / D.S₁.r u t ≤
          ((t - u) * D.L V) / D.S₁.r u t :=
        div_le_div_of_nonneg_right hΔr hr.le
      have h₂ : ((t - u) * D.L V) / D.S₁.r u t ≤
          ((t - u) * D.L V) / (cR * (t - u)) :=
        div_le_div_of_nonneg_left (mul_nonneg hd.le hL)
          (mul_pos hcR hd) hradlo
      have h₃ : ((t - u) * D.L V) / (cR * (t - u)) =
          D.L V / cR := by field_simp [hcR.ne', hd.ne']
      exact h₁.trans (h₂.trans_eq h₃)
    have hrec : D.L V / cR ≤ C * D.L V := by
      have hh := mul_le_mul_of_nonneg_right hcRinv hL
      simpa only [div_eq_mul_inv, one_div, one_mul, mul_one, mul_comm] using hh
    have hm : IsBVSolution.mu D.S₂ u t ≤ 1 := hmu₂.2.le
    calc
      IsBVSolution.mu D.S₂ u t *
          |D.S₁.r u t - D.S₂.r u t| / D.S₁.r u t =
          IsBVSolution.mu D.S₂ u t *
            (|D.S₁.r u t - D.S₂.r u t| / D.S₁.r u t) := by ring
      _ ≤ 1 * (|D.S₁.r u t - D.S₂.r u t| / D.S₁.r u t) :=
        mul_le_mul_of_nonneg_right hm
          (div_nonneg (abs_nonneg _) hr.le)
      _ ≤ C * D.L V := by simpa using hradquot.trans hrec
  have hlterm : ((1 - IsBVSolution.mu D.S₁ u t) / D.S₁.lam u t) *
      |D.S₁.lam u t - D.S₂.lam u t| ≤ C * D.L V := by
    exact (mul_le_mul_of_nonneg_right hRle (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hΔlam hC0)
  have hT : |IsBVSolution.mu D.S₂ u t *
      ((D.S₁.r u t - D.S₂.r u t) / D.S₁.r u t) -
      ((1 - IsBVSolution.mu D.S₁ u t) / D.S₁.lam u t) *
        (D.S₁.lam u t - D.S₂.lam u t)| ≤ 2 * C * D.L V := by
    calc
      _ ≤ |IsBVSolution.mu D.S₂ u t *
          ((D.S₁.r u t - D.S₂.r u t) / D.S₁.r u t)| +
        |((1 - IsBVSolution.mu D.S₁ u t) / D.S₁.lam u t) *
          (D.S₁.lam u t - D.S₂.lam u t)| := abs_sub _ _
      _ ≤ C * D.L V + C * D.L V := by
        have hterm₁ : |IsBVSolution.mu D.S₂ u t *
            ((D.S₁.r u t - D.S₂.r u t) / D.S₁.r u t)| =
            IsBVSolution.mu D.S₂ u t *
              |D.S₁.r u t - D.S₂.r u t| / D.S₁.r u t := by
          rw [abs_mul, abs_div, abs_of_nonneg hmu₂.1, abs_of_pos hr]
          ring
        have hterm₂ : |((1 - IsBVSolution.mu D.S₁ u t) / D.S₁.lam u t) *
            (D.S₁.lam u t - D.S₂.lam u t)| =
            ((1 - IsBVSolution.mu D.S₁ u t) / D.S₁.lam u t) *
              |D.S₁.lam u t - D.S₂.lam u t| := by
          rw [abs_mul, abs_of_nonneg hR0]
        rw [hterm₁, hterm₂]
        exact add_le_add hrterm hlterm
      _ = 2 * C * D.L V := by ring
  have hθdiff := hθgood D ha hb hP hsmall V u t hVb hut htG
  have hθdiffC : |D.S₁.theta u t - D.S₂.theta u t| ≤
      C * (D.A V + D.L V) :=
    hθdiff.trans (mul_le_mul_of_nonneg_right hCθ' hAL)
  have hbound := outgoing_forcing_algebra hC hA hL
    ⟨hq0, hqle⟩ ⟨hR0, hRle⟩ hT hθdiffC
  exact hbound


end ChristodoulouBV.Uniqueness

end
