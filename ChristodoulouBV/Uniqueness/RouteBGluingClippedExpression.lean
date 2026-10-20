module

public import ChristodoulouBV.Uniqueness.RouteBGluingClippedFields
public import ChristodoulouBV.Uniqueness.RouteBGluingExpression
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Equations for scalar expressions in glued fields

A classical right-hand side depends pointwise on the seven fields. The same
restriction argument also applies to the scalar-radius product and the two
derived amplitudes, which are scalar expressions in those fields.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Regionwise relative-jet equations for any C¹ scalar expression in the
seven fields pass through both seams to the glued state. The expression and
right-hand side may contain products and quotients; no extra seam equation
is assumed. -/
theorem routeB_clipped_glued_expression_jet_equation
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar) (hStarb : vStar < b)
    (SOld SLow SAx T : Fields)
    (hOld : RouteBFieldsEqOn T SOld (routeBOldRegion a vStar))
    (hLow : RouteBFieldsEqOn T SLow (routeBLowerRegion a vStar b))
    (hAx : RouteBFieldsEqOn T SAx (closedCoordTriangle a b))
    (E rhs : (RouteBField → ℝ) → ℝ) (direction : ℝ × ℝ)
    (hEC1 : ContDiffOn ℝ 1 (routeBScalarExpression E T)
      (closedCoordTriangle 0 b))
    (hOldEq : ∀ p ∈ routeBOldRegion a vStar,
      p ∈ developmentWithInitialEdge b →
      (fderivWithin ℝ (routeBScalarExpression E SOld)
        (routeBOldRegion a vStar) p) direction =
        rhs (fun c => routeBField SOld c p))
    (hLowEq : ∀ p ∈ routeBLowerRegion a vStar b,
      p ∈ developmentWithInitialEdge b →
      (fderivWithin ℝ (routeBScalarExpression E SLow)
        (routeBLowerRegion a vStar b) p) direction =
        rhs (fun c => routeBField SLow c p))
    (hAxEq : ∀ p ∈ closedCoordTriangle a b,
      p ∈ developmentWithInitialEdge b →
      (fderivWithin ℝ (routeBScalarExpression E SAx)
        (closedCoordTriangle a b) p) direction =
        rhs (fun c => routeBField SAx c p)) :
    ∀ p ∈ developmentWithInitialEdge b,
      (fderivWithin ℝ (routeBScalarExpression E T)
        (closedCoordTriangle 0 b) p) direction =
        rhs (fun c => routeBField T c p) := by
  have hOldSub : routeBOldRegion a vStar ⊆ closedCoordTriangle 0 b := by
    intro p hp
    exact ⟨hp.1.1, hp.1.2.1, hp.1.2.2.trans hStarb.le⟩
  have hLowSub : routeBLowerRegion a vStar b ⊆ closedCoordTriangle 0 b := by
    intro p hp
    exact ⟨hp.1.1, hp.1.2.trans (haStar.le.trans hp.2.1), hp.2.2⟩
  have hAxSub : closedCoordTriangle a b ⊆ closedCoordTriangle 0 b := by
    intro p hp
    exact ⟨ha.le.trans hp.1, hp.2.1, hp.2.2⟩
  have hOldUnique : UniqueDiffOn ℝ (routeBOldRegion a vStar) :=
    uniqueDiffOn_convex (routeBOldRegion_closed_convex a vStar).2
      (routeBOldRegion_interior_nonempty ha haStar)
  have hLowUnique : UniqueDiffOn ℝ (routeBLowerRegion a vStar b) :=
    uniqueDiffOn_convex (routeBLowerRegion_closed_convex a vStar b).2
      (routeBLowerRegion_interior_nonempty ha hStarb)
  have hAxUnique : UniqueDiffOn ℝ (closedCoordTriangle a b) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b) (by
      rw [interior_closedCoordTriangle]
      exact openCoordTriangle_nonempty (haStar.trans hStarb))
  have hEqOld : EqOn (routeBScalarExpression E T)
      (routeBScalarExpression E SOld) (routeBOldRegion a vStar) := by
    intro p hp
    change E (fun c => routeBField T c p) =
      E (fun c => routeBField SOld c p)
    congr 1
    funext c
    exact hOld c hp
  have hEqLow : EqOn (routeBScalarExpression E T)
      (routeBScalarExpression E SLow) (routeBLowerRegion a vStar b) := by
    intro p hp
    change E (fun c => routeBField T c p) =
      E (fun c => routeBField SLow c p)
    congr 1
    funext c
    exact hLow c hp
  have hEqAx : EqOn (routeBScalarExpression E T)
      (routeBScalarExpression E SAx) (closedCoordTriangle a b) := by
    intro p hp
    change E (fun c => routeBField T c p) =
      E (fun c => routeBField SAx c p)
    congr 1
    funext c
    exact hAx c hp
  have hcover := routeB_clipped_three_region_cover ha.le haStar.le hStarb.le
  intro p hpU
  have hpK : p ∈ closedCoordTriangle 0 b :=
    ⟨hpU.1, hpU.2.1.le, hpU.2.2.le⟩
  have hpiece : p ∈ routeBOldRegion a vStar ∨
      p ∈ routeBLowerRegion a vStar b ∨
        p ∈ closedCoordTriangle a b := by
    have h := hcover.symm ▸ hpK
    rcases h with (hOld' | hLow') | hAx'
    · exact Or.inl hOld'
    · exact Or.inr (Or.inl hLow')
    · exact Or.inr (Or.inr hAx')
  rcases hpiece with hpOld | hpLow | hpAx
  · rw [fderivWithin_eq_of_eqOn_subset hEC1 hOldSub
      hOldUnique hEqOld hpOld, hOldEq p hpOld hpU]
    congr 1
    funext c
    exact (hOld c hpOld).symm
  · rw [fderivWithin_eq_of_eqOn_subset hEC1 hLowSub
      hLowUnique hEqLow hpLow, hLowEq p hpLow hpU]
    congr 1
    funext c
    exact (hLow c hpLow).symm
  · rw [fderivWithin_eq_of_eqOn_subset hEC1 hAxSub
      hAxUnique hEqAx hpAx, hAxEq p hpAx hpU]
    congr 1
    funext c
    exact (hAx c hpAx).symm

end ChristodoulouBV.Uniqueness

end
