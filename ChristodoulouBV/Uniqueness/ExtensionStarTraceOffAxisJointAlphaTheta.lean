module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisJointQuotient
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisJointScalar
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisJointLambdaFloor
import ChristodoulouBV.Uniqueness.ExtensionIncomingWeighted
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Joint terminal values of alpha and theta

The outgoing scalar derivative and its axis-renormalized part are algebraic
combinations of the joint `λ`, `α/λ`, and `φ` traces.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The compatible outgoing scalar fields `α` and `θ` have jointly continuous
terminal traces on each closed off-axis rectangle. The same construction
retains a positive floor for `λ`. -/
theorem exists_alpha_theta_terminal_traces_on_rectangle
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε a vBar : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε1 : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ lamTrace hTrace alphaTrace thetaTrace : ℝ × ℝ → ℝ,
      ContinuousOn lamTrace (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ContinuousOn hTrace (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ContinuousOn alphaTrace (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ContinuousOn thetaTrace (Icc 0 a ×ˢ Icc vBar vStar) ∧
      (∀ u ∈ Icc 0 a, ∀ v ∈ Icc vBar vStar, c ≤ lamTrace (u, v)) ∧
      (∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar b,
          lamTrace (u, v) = (S b).lam u v ∧
          hTrace (u, v) = (S b).alpha u v / (S b).lam u v ∧
          alphaTrace (u, v) = (S b).alpha u v ∧
          thetaTrace (u, v) = (S b).theta u v) := by
  have hεlt : ε < 1 := by
    obtain ⟨ε₁, heq, _, hε₁one, _, _, _, _⟩ := universal_epsilon_choice
    exact (show ε < ε₁ by simpa only [heq] using hε1).trans hε₁one
  have hIncoming := incoming_weighted_bound_before_star
    hu₀.1 hu₀.2 hεlt (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hα hfamily htail
  obtain ⟨c, hc, lamTrace, hlamC, hlamFloor, hlamMatch⟩ :=
    exists_lam_terminal_trace_with_floor_on_rectangle_of_incoming_bddAbove
      hu₀ ha haBar hBarStar hα hfamily hε1 htail hIncoming
  obtain ⟨hTrace, hhC, hhMatch⟩ :=
    exists_outgoing_quotient_terminal_trace_on_rectangle
      hu₀ ha haBar hBarStar hα hfamily hε1 htail
  obtain ⟨_, phiTrace, _, _, hphiC, _, hscalarMatch⟩ :=
    exists_nu_phi_zeta_terminal_traces_on_rectangle
      hu₀ ha haBar hBarStar hα hfamily hε1 htail
  let alphaTrace : ℝ × ℝ → ℝ := fun p => lamTrace p * hTrace p
  let thetaTrace : ℝ × ℝ → ℝ :=
    fun p => lamTrace p * (hTrace p - phiTrace p)
  refine ⟨c, hc, lamTrace, hTrace, alphaTrace, thetaTrace,
    hlamC, hhC, hlamC.mul hhC, hlamC.mul (hhC.sub hphiC),
    hlamFloor, ?_⟩
  intro b hb u hu v hv
  have hp : (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hu.1, hu.2.trans_lt (haBar.trans_le hv.1), hv.2⟩
  have hlpos : 0 < (S b).lam u v :=
    (hfamily b hb).1.solution.lam_pos (u, v) hp
  have hl := hlamMatch b hb u hu v hv
  have hh := hhMatch b hb u hu v hv
  have hφ := (hscalarMatch b hb u hu v hv).2.1
  refine ⟨hl, hh, ?_, ?_⟩
  · change lamTrace (u, v) * hTrace (u, v) = _
    rw [hl, hh]
    exact mul_div_cancel₀ _ (ne_of_gt hlpos)
  · change lamTrace (u, v) * (hTrace (u, v) - phiTrace (u, v)) = _
    rw [hl, hh, hφ]
    simp only [Fields.theta]
    field_simp

end ChristodoulouBV.Uniqueness

end
