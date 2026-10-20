module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisJointLambda
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceFamilyExpansion
import Mathlib.Tactic.Linarith

/-!
# Positive lambda floor on an off-axis terminal rectangle

The cutoff-independent lower bound for the old expansion passes to its
jointly continuous terminal trace.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The jointly continuous terminal `λ` trace retains one positive lower
bound on the entire closed rectangle, including `v = vStar`. -/
theorem exists_lam_terminal_trace_with_floor_on_rectangle_of_incoming_bddAbove
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
    ∃ c : ℝ, 0 < c ∧ ∃ lamTrace : ℝ × ℝ → ℝ,
      ContinuousOn lamTrace (Icc 0 a ×ˢ Icc vBar vStar) ∧
      (∀ u ∈ Icc 0 a, ∀ v ∈ Icc vBar vStar, c ≤ lamTrace (u, v)) ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar b,
          lamTrace (u, v) = (S b).lam u v := by
  obtain ⟨G, hG, hGmatch⟩ :=
    exists_lam_terminal_trace_on_rectangle_of_incoming_bddAbove
      hu₀ ha haBar hBarStar hα hfamily hε1 htail hIncoming
  obtain ⟨c, hc, hfloor⟩ :=
    exists_expansion_floor_before_star hu₀ hα hfamily hε1 htail
  refine ⟨c, hc, G, hG, ?_, hGmatch⟩
  intro u hu v hv
  have hslice : ContinuousOn (fun w => G (u, w)) (Icc vBar vStar) :=
    hG.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun w hw => ⟨hu, hw⟩)
  have hmap : MapsTo (fun w => G (u, w)) (Ico vBar vStar) (Ici c) := by
    intro w hw
    let b : ℝ := (w + vStar) / 2
    have hwb : w < b := by dsimp [b]; linarith only [hw.2]
    have hbStar : b < vStar := by dsimp [b]; linarith only [hw.2]
    have hb0 : 0 < b := by dsimp [b]; linarith only [ha, haBar, hw.1, hw.2]
    have hb : b ∈ Ioo (0 : ℝ) vStar := ⟨hb0, hbStar⟩
    change c ≤ G (u, w)
    rw [hGmatch b hb u hu w ⟨hw.1, hwb⟩]
    exact hfloor b hb u w hu.1 (hu.2.trans_lt (haBar.trans_le hw.1)) hwb
  have hclosed : closure (Ico vBar vStar) = Icc vBar vStar :=
    closure_Ico hBarStar.ne
  rw [← hclosed] at hslice hv
  have h := hmap.closure_of_continuousOn hslice hv
  simpa only [isClosed_Ici.closure_eq, Set.mem_Ici] using h

end ChristodoulouBV.Uniqueness

end
