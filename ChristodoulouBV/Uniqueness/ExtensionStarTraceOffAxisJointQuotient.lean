module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisJointGeneric
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceAllPrime
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceUnconditional
import ChristodoulouBV.Uniqueness.ExtensionIncomingSigns
import ChristodoulouBV.Uniqueness.ExtensionFamily
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Joint terminal trace of the outgoing scalar quotient

The unweighted `α′` estimate controls the vertical derivative of `α/λ`.
The generic terminal rectangle lemma then supplies a jointly continuous
quotient trace, including the initial edge.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- On every closed off-axis rectangle the compatible quotient `α/λ` has a
jointly continuous terminal trace. The incoming strip estimates give its incoming bound. -/
theorem exists_outgoing_quotient_terminal_trace_on_rectangle
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
    ∃ hTrace : ℝ × ℝ → ℝ,
      ContinuousOn hTrace (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar b,
          hTrace (u, v) = (S b).alpha u v / (S b).lam u v := by
  have hεlt : ε < 1 := by
    obtain ⟨ε₁, heq, _, hε₁one, _, _, _, _⟩ := universal_epsilon_choice
    exact (show ε < ε₁ by simpa only [heq] using hε1).trans hε₁one
  have hIncoming := incoming_weighted_bound_before_star
    hu₀.1 hu₀.2 hεlt (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hα hfamily htail
  have hε0 : 0 ≤ ε := tail_mass_upper_nonneg hu₀ hfamily htail
  obtain ⟨B, hB, hprime⟩ :=
    exists_uniform_alphaPrime_bound_on_old_union_of_incoming_bddAbove
      hu₀ hα hfamily hε0 hε1 htail hIncoming
  have hM : 0 ≤ B / 2 := div_nonneg hB (by norm_num)
  apply exists_joint_terminal_trace_of_compatible_c1_family
    (F := fun b p => (S b).alpha p.1 p.2 / (S b).lam p.1 p.2)
    ha haBar hBarStar hM
  · intro b₁ hb₁ b₂ hb₂ u hu v hv
    have hp₁ : (u, v) ∈ developmentWithInitialEdge b₁ :=
      ⟨hu.1, hu.2.trans_lt (haBar.trans_le hv.1),
        hv.2.trans_le (min_le_left _ _)⟩
    have hp₂ : (u, v) ∈ developmentWithInitialEdge b₂ :=
      ⟨hu.1, hu.2.trans_lt (haBar.trans_le hv.1),
        hv.2.trans_le (min_le_right _ _)⟩
    have hfields := family_fields_eq_on_common_development
      hfamily hb₁ hb₂ ⟨hp₁, hp₂⟩
    rw [hfields.2.2.2.2.2.1, hfields.2.2.2.1]
  · intro b hb T hT hTb
    exact C1Solution.alpha_div_lam_contDiffOn hT hTb (hfamily b hb).1
  · intro b hb u hu v hv
    let H := (hfamily b hb).1
    have hp : (u, v) ∈ developmentWithInitialEdge b :=
      ⟨hu.1.le, hu.2.trans_lt (haBar.trans hv.1), hv.2⟩
    have hlam : 0 < (S b).lam u v := H.solution.lam_pos (u, v) hp
    have hlamHalf : (S b).lam u v ≤ 1 / 2 :=
      lam_le_half_of_initial_gauge H
        (fun w hw => ((hfamily b hb).2 w hw).1)
        hu.1.le (hu.2.trans_lt (haBar.trans hv.1)) hv.2
    have hpoint := hprime b hb u v hu.1
      (hu.2.trans_lt (haBar.trans hv.1)) hv.2
    have hidentity :
        |deriv (fun t => (S b).alpha u t / (S b).lam u t) v| =
          |deriv (fun t => (S b).alpha u t / (S b).lam u t) v /
            (S b).lam u v| * (S b).lam u v := by
      rw [abs_div, abs_of_pos hlam]
      field_simp [ne_of_gt hlam]
    rw [hidentity]
    calc
      |deriv (fun t => (S b).alpha u t / (S b).lam u t) v /
          (S b).lam u v| * (S b).lam u v ≤ B * (S b).lam u v :=
        mul_le_mul_of_nonneg_right hpoint hlam.le
      _ ≤ B / 2 := by nlinarith only [hlamHalf, hB]

end ChristodoulouBV.Uniqueness

end
