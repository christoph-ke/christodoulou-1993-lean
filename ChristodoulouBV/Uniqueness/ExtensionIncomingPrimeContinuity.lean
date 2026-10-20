module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingInitialPrime
public import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarEdge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# Continuity of the outgoing derivative coordinate expression

The closed C¹ quotient jet extends the coordinate expression for `α′`
continuously to the initial edge of each finite member.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- On a fixed off-axis incoming segment, the coordinate expression for
`α′` is continuous through `u = 0`. -/
theorem alphaPrime_coordinate_continuousOn_incoming_of_c1
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u₀ v : ℝ} (hu₀ : 0 ≤ u₀) (hu₀v : u₀ < v) (hvb : v < b) :
    ContinuousOn
      (fun s => deriv (fun t => S.alpha s t / S.lam s t) v / S.lam s v)
      (Icc (0 : ℝ) u₀) := by
  let B : ℝ := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  let K := closedCoordTriangle 0 B
  let Q : ℝ × ℝ → ℝ := fun p => S.alpha p.1 p.2 / S.lam p.1 p.2
  have hQ : ContDiffOn ℝ 1 Q K := C1Solution.alpha_div_lam_contDiffOn hB hBb H
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hjet : ContinuousOn (fun p => (fderivWithin ℝ Q K p) (0, 1)) K :=
    (hQ.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have hmap (s : ℝ) (hs : s ∈ Icc (0 : ℝ) u₀) : (s, v) ∈ K := by
    change 0 ≤ s ∧ s ≤ v ∧ v ≤ B
    exact ⟨hs.1, hs.2.trans hu₀v.le, hvB.le⟩
  have hJ : ContinuousOn
      (fun s => (fderivWithin ℝ Q K (s, v)) (0, 1))
      (Icc (0 : ℝ) u₀) :=
    hjet.comp (continuous_id.prodMk continuous_const).continuousOn hmap
  have hL : ContinuousOn (fun s => S.lam s v) (Icc (0 : ℝ) u₀) :=
    (C1Solution.five_fields_contDiffOn hB hBb H).1.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hmap
  have hLne : ∀ s ∈ Icc (0 : ℝ) u₀, S.lam s v ≠ 0 := by
    intro s hs
    exact ne_of_gt (H.solution.lam_pos (s, v)
      ⟨hs.1, hs.2.trans_lt hu₀v, hvb⟩)
  have hP : ContinuousOn
      (fun s => (fderivWithin ℝ Q K (s, v)) (0, 1) / S.lam s v)
      (Icc (0 : ℝ) u₀) := hJ.div hL hLne
  apply hP.congr
  intro s hs
  have hder := vertical_hasDerivAt_of_closed_jet hQ
    hs.1 (hs.2.trans_lt hu₀v) hvB
    (g := (fderivWithin ℝ Q K (s, v)) (0, 1)) rfl
  change deriv (fun t => S.alpha s t / S.lam s t) v / S.lam s v =
    (fderivWithin ℝ Q K (s, v)) (0, 1) / S.lam s v
  rw [hder.deriv]

end ChristodoulouBV.Uniqueness

end
