module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.CompatibleFamilyTerminalRectangle
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceUniformLambdaV
import ChristodoulouBV.Uniqueness.ExtensionFamily
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# Jointly continuous off-axis terminal trace of lambda

The uniform outgoing derivative estimate and finite-member C¹ regularity
give one lambda trace on a closed rectangle up to `vStar`.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The old compatible family has a jointly continuous `λ` trace on every
closed off-axis rectangle below the terminal corner. -/
theorem exists_lam_terminal_trace_on_rectangle_of_incoming_bddAbove
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
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε)
    (hIncoming : BddAbove
      (incomingWeightedAlphaPrimeValues u₀ vStar ((1 : ℝ) / 2) S)) :
    ∃ lamTrace : ℝ × ℝ → ℝ,
      ContinuousOn lamTrace (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar b,
          lamTrace (u, v) = (S b).lam u v := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_uniform_lambda_v_bound_before_star_of_incoming_bddAbove
      hu₀ hα hfamily hε1 htail hIncoming
  apply exists_compatible_family_terminal_rectangle
    (le_refl 0) ha.le haBar hBarStar hM
    (F := fun b p => (S b).lam p.1 p.2)
  · intro b₁ hb₁ b₂ hb₂ u hu v hv
    have hp₁ : (u, v) ∈ developmentWithInitialEdge b₁ :=
      ⟨hu.1, hu.2.trans_lt (haBar.trans_le hv.1), hv.2.trans_le (min_le_left _ _)⟩
    have hp₂ : (u, v) ∈ developmentWithInitialEdge b₂ :=
      ⟨hu.1, hu.2.trans_lt (haBar.trans_le hv.1), hv.2.trans_le (min_le_right _ _)⟩
    exact (family_fields_eq_on_common_development hfamily hb₁ hb₂
      ⟨hp₁, hp₂⟩).2.2.2.1
  · intro b hb t ht
    have hH := (hfamily b hb).1
    apply hH.lam_c1.continuousOn.mono
    intro p hp
    apply subset_closure
    exact ⟨hp.1.1, hp.1.2.trans_lt (haBar.trans_le hp.2.1), hp.2.2.trans_lt ht.2⟩
  · intro b hb u hu v hv
    let H := (hfamily b hb).1
    let T : ℝ := (v + b) / 2
    have hv0 : 0 < v := ha.trans (haBar.trans hv.1)
    have hT : 0 < T := by dsimp [T]; linarith only [hv0, hv.2]
    have hTb : T < b := by dsimp [T]; linarith only [hv.2]
    have hvT : v < T := by dsimp [T]; linarith only [hv.2]
    have hF := (C1Solution.five_fields_contDiffOn hT hTb H).1
    exact (vertical_hasDerivAt_of_closed_jet hF hu.1
      (hu.2.trans_lt (haBar.trans hv.1)) hvT
      (g := (fderivWithin ℝ
        (fun p : ℝ × ℝ => (S b).lam p.1 p.2)
        (closedCoordTriangle 0 T) (u, v)) (0, 1)) rfl).differentiableAt
  · intro b hb u hu v hv
    exact hbound b hb u v hu.1
      (hu.2.trans_lt (haBar.trans hv.1)) hv.2

end ChristodoulouBV.Uniqueness

end
