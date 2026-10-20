module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesGlueState
public import ChristodoulouBV.Uniqueness.RouteBGluingFields
import Mathlib.Tactic

/-!
# Physical fields reconstructed from a glued seven-state strip

The rectangle state stores `ψ = r φ`. Positivity of the area radius makes
division by `r` regular throughout the closed strip.
-/

@[expose] public section

noncomputable section

namespace ChristodoulouBV.Uniqueness

/-- The seven primary reduced fields represented by a rectangle state. -/
def rectangleStateFields (Z : ℝ × ℝ → C1Solution.RectangleState) : Fields :=
  routeBFieldsOfComponents fun c p =>
    match c with
    | .radius => C1Solution.stateRadius (Z p)
    | .scalar => C1Solution.statePhi (Z p)
    | .mass => C1Solution.stateMass (Z p)
    | .expansion => C1Solution.stateLam (Z p)
    | .contraction => C1Solution.stateNu (Z p)
    | .outgoing => C1Solution.stateAlpha (Z p)
    | .incoming => C1Solution.stateBeta (Z p)

/-- Each primary field of a safe relative `C¹` rectangle state is relative
`C¹`, including the quotient scalar field. -/
theorem routeBFieldsC1On_rectangleStateFields
    {K : Set (ℝ × ℝ)} {Z : ℝ × ℝ → C1Solution.RectangleState}
    (hZ : ContDiffOn ℝ 1 Z K)
    (hsafe : ∀ p ∈ K, C1Solution.IsSafeRectangleState (Z p)) :
    RouteBFieldsC1On (rectangleStateFields Z) K := by
  have hlam : ContDiffOn ℝ 1 (fun p => C1Solution.stateLam (Z p)) K := by
    change ContDiffOn ℝ 1 (fun p => (Z p).1.1) K
    fun_prop
  have halpha : ContDiffOn ℝ 1 (fun p => C1Solution.stateAlpha (Z p)) K := by
    change ContDiffOn ℝ 1 (fun p => (Z p).1.2) K
    fun_prop
  have hnu : ContDiffOn ℝ 1 (fun p => C1Solution.stateNu (Z p)) K := by
    change ContDiffOn ℝ 1 (fun p => (Z p).2.1) K
    fun_prop
  have hbeta : ContDiffOn ℝ 1 (fun p => C1Solution.stateBeta (Z p)) K := by
    change ContDiffOn ℝ 1 (fun p => (Z p).2.2.1) K
    fun_prop
  have hm : ContDiffOn ℝ 1 (fun p => C1Solution.stateMass (Z p)) K := by
    change ContDiffOn ℝ 1 (fun p => (Z p).2.2.2.1) K
    fun_prop
  have hr : ContDiffOn ℝ 1 (fun p => C1Solution.stateRadius (Z p)) K := by
    change ContDiffOn ℝ 1 (fun p => (Z p).2.2.2.2.1) K
    fun_prop
  have hpsi : ContDiffOn ℝ 1 (fun p => C1Solution.statePsi (Z p)) K := by
    change ContDiffOn ℝ 1 (fun p => (Z p).2.2.2.2.2) K
    fun_prop
  have hphi : ContDiffOn ℝ 1 (fun p => C1Solution.statePhi (Z p)) K := by
    change ContDiffOn ℝ 1
      (fun p => C1Solution.statePsi (Z p) / C1Solution.stateRadius (Z p)) K
    exact hpsi.div hr (fun p hp => ne_of_gt (hsafe p hp).1)
  intro c
  cases c <;>
    simp only [routeBField_ofComponents, rectangleStateFields] <;>
    assumption

end ChristodoulouBV.Uniqueness

end
