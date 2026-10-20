module

public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamValues
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Endpoint closure for Route B seam jets

The classical equations hold on the open development, so their horizontal
jet identities are first obtained below the upper endpoint. Relative C¹
regularity extends their equality to that endpoint.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Equality of the horizontal coordinate jets below `b` extends to both
closed endpoints when the two scalar fields are relatively C¹ on their
respective pieces. -/
theorem routeB_vertical_horizontal_jets_eq_of_eq_below_top
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (hStarb : vStar < b)
    {fLow fAx : ℝ × ℝ → ℝ}
    (hLow : ContDiffOn ℝ 1 fLow (routeBLowerRegion a vStar b))
    (hAx : ContDiffOn ℝ 1 fAx (closedCoordTriangle a b))
    (hBelow : ∀ v ∈ Ico vStar b,
      (fderivWithin ℝ fLow (routeBLowerRegion a vStar b) (a, v)) (1, 0) =
        (fderivWithin ℝ fAx (closedCoordTriangle a b) (a, v)) (1, 0)) :
    ∀ v ∈ Icc vStar b,
      (fderivWithin ℝ fLow (routeBLowerRegion a vStar b) (a, v)) (1, 0) =
        (fderivWithin ℝ fAx (closedCoordTriangle a b) (a, v)) (1, 0) := by
  have hLowUnique : UniqueDiffOn ℝ (routeBLowerRegion a vStar b) :=
    uniqueDiffOn_convex (routeBLowerRegion_closed_convex a vStar b).2
      (routeBLowerRegion_interior_nonempty ha hStarb)
  have hAxUnique : UniqueDiffOn ℝ (closedCoordTriangle a b) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b) (by
      rw [interior_closedCoordTriangle]
      exact openCoordTriangle_nonempty (haStar.trans hStarb))
  have hLowJetCont : ContinuousOn
      (fun p => (fderivWithin ℝ fLow (routeBLowerRegion a vStar b) p) (1, 0))
      (routeBLowerRegion a vStar b) :=
    (hLow.continuousOn_fderivWithin hLowUnique (by norm_num)).clm_apply
      continuousOn_const
  have hAxJetCont : ContinuousOn
      (fun p => (fderivWithin ℝ fAx (closedCoordTriangle a b) p) (1, 0))
      (closedCoordTriangle a b) :=
    (hAx.continuousOn_fderivWithin hAxUnique (by norm_num)).clm_apply
      continuousOn_const
  have hLowEdgeCont : ContinuousOn
      (fun v => (fderivWithin ℝ fLow
        (routeBLowerRegion a vStar b) (a, v)) (1, 0)) (Icc vStar b) :=
    hLowJetCont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hv => ⟨⟨ha.le, le_rfl⟩, hv⟩)
  have hAxEdgeCont : ContinuousOn
      (fun v => (fderivWithin ℝ fAx
        (closedCoordTriangle a b) (a, v)) (1, 0)) (Icc vStar b) :=
    hAxJetCont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hv => ⟨le_rfl, haStar.le.trans hv.1, hv.2⟩)
  have hBelowEq : EqOn
      (fun v => (fderivWithin ℝ fLow
        (routeBLowerRegion a vStar b) (a, v)) (1, 0))
      (fun v => (fderivWithin ℝ fAx
        (closedCoordTriangle a b) (a, v)) (1, 0))
      (Ico vStar b) := hBelow
  have hAll : EqOn
      (fun v => (fderivWithin ℝ fLow
        (routeBLowerRegion a vStar b) (a, v)) (1, 0))
      (fun v => (fderivWithin ℝ fAx
        (closedCoordTriangle a b) (a, v)) (1, 0))
      (Icc vStar b) :=
    hBelowEq.of_subset_closure hLowEdgeCont hAxEdgeCont
      Ico_subset_Icc_self (by rw [closure_Ico hStarb.ne])
  exact hAll

/-- A matching seven-value trace turns the same classical incoming equation
on each piece into equality of its horizontal relative jets on the entire
closed seam. -/
theorem routeB_vertical_horizontal_jets_eq_of_classical_equation
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (hStarb : vStar < b) (SLow SAx : Fields)
    (E rhs : (RouteBField → ℝ) → ℝ)
    (hLowC1 : ContDiffOn ℝ 1 (routeBScalarExpression E SLow)
      (routeBLowerRegion a vStar b))
    (hAxC1 : ContDiffOn ℝ 1 (routeBScalarExpression E SAx)
      (closedCoordTriangle a b))
    (hLowEq : RouteBLocalJetEquation b (routeBLowerRegion a vStar b)
      SLow E rhs (1, 0))
    (hAxEq : RouteBLocalJetEquation b (closedCoordTriangle a b)
      SAx E rhs (1, 0))
    (hValues : ∀ c : RouteBField, ∀ v ∈ Icc vStar b,
      routeBField SLow c (a, v) = routeBField SAx c (a, v)) :
    ∀ v ∈ Icc vStar b,
      (fderivWithin ℝ (routeBScalarExpression E SLow)
        (routeBLowerRegion a vStar b) (a, v)) (1, 0) =
      (fderivWithin ℝ (routeBScalarExpression E SAx)
        (closedCoordTriangle a b) (a, v)) (1, 0) := by
  apply routeB_vertical_horizontal_jets_eq_of_eq_below_top
    ha haStar hStarb hLowC1 hAxC1
  intro v hv
  have hv' : v ∈ Icc vStar b := ⟨hv.1, hv.2.le⟩
  have hDev : (a, v) ∈ developmentWithInitialEdge b :=
    ⟨ha.le, haStar.trans_le hv.1, hv.2⟩
  rw [hLowEq (a, v) ⟨⟨ha.le, le_rfl⟩, hv'⟩ hDev,
    hAxEq (a, v) ⟨le_rfl, haStar.le.trans hv.1, hv.2.le⟩ hDev]
  congr 1
  funext c
  exact hValues c v hv'

end ChristodoulouBV.Uniqueness

end
