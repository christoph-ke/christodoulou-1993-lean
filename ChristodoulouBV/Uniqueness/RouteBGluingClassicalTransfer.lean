module

public import ChristodoulouBV.Uniqueness.RouteBGluingClassicalJet
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Classical equations across the Route B seams

Every classical relative-jet equation on the three closed pieces transfers
to their C¹ glue, including the horizontal and vertical seams and their
common corner.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The glued seven-field state satisfies all twelve relative-jet equations
on the enlarged closed triangle wherever it meets the open development. -/
theorem routeB_classicalJetOn_of_three
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar) (hStarb : vStar < b)
    (SOld SLow SAx T : Fields)
    (hT : RouteBFieldsC1On T (closedCoordTriangle 0 b))
    (hOld : RouteBFieldsEqOn T SOld (closedCoordTriangle 0 vStar))
    (hLow : RouteBFieldsEqOn T SLow (routeBLowerRegion a vStar b))
    (hAx : RouteBFieldsEqOn T SAx (closedCoordTriangle a b))
    (hOldJet : RouteBClassicalJetOn b (closedCoordTriangle 0 vStar) SOld)
    (hLowJet : RouteBClassicalJetOn b (routeBLowerRegion a vStar b) SLow)
    (hAxJet : RouteBClassicalJetOn b (closedCoordTriangle a b) SAx) :
    RouteBClassicalJetOn b (closedCoordTriangle 0 b) T := by
  have hselect (c : RouteBField) :
      ContDiffOn ℝ 1
        (routeBScalarExpression (routeBSelector c) T)
        (closedCoordTriangle 0 b) := hT c
  have hpsi : ContDiffOn ℝ 1
      (routeBScalarExpression routeBScalarRadiusExpr T)
      (closedCoordTriangle 0 b) := routeB_scalarRadius_c1 hT
  have htheta : ContDiffOn ℝ 1
      (routeBScalarExpression routeBThetaExpr T)
      (closedCoordTriangle 0 b) := by
    exact (hT.theta_zeta).1
  have hzeta : ContDiffOn ℝ 1
      (routeBScalarExpression routeBZetaExpr T)
      (closedCoordTriangle 0 b) := by
    exact (hT.theta_zeta).2
  have htransfer (E rhs : (RouteBField → ℝ) → ℝ)
      (direction : ℝ × ℝ)
      (hEC1 : ContDiffOn ℝ 1 (routeBScalarExpression E T)
        (closedCoordTriangle 0 b))
      (hO : RouteBLocalJetEquation b (closedCoordTriangle 0 vStar)
        SOld E rhs direction)
      (hL : RouteBLocalJetEquation b (routeBLowerRegion a vStar b)
        SLow E rhs direction)
      (hA : RouteBLocalJetEquation b (closedCoordTriangle a b)
        SAx E rhs direction) :
      RouteBLocalJetEquation b (closedCoordTriangle 0 b)
        T E rhs direction := by
    intro p _ hpU
    exact routeB_glued_expression_jet_equation ha haStar hStarb
      SOld SLow SAx T hOld hLow hAx E rhs direction
      hEC1 hO hL hA p hpU
  exact {
    radius_out := htransfer _ _ _ (hselect .radius)
      hOldJet.radius_out hLowJet.radius_out hAxJet.radius_out
    radius_in := htransfer _ _ _ (hselect .radius)
      hOldJet.radius_in hLowJet.radius_in hAxJet.radius_in
    scalar_radius_out := htransfer _ _ _ hpsi
      hOldJet.scalar_radius_out hLowJet.scalar_radius_out
      hAxJet.scalar_radius_out
    scalar_radius_in := htransfer _ _ _ hpsi
      hOldJet.scalar_radius_in hLowJet.scalar_radius_in
      hAxJet.scalar_radius_in
    mass_out := htransfer _ _ _ (hselect .mass)
      hOldJet.mass_out hLowJet.mass_out hAxJet.mass_out
    mass_in := htransfer _ _ _ (hselect .mass)
      hOldJet.mass_in hLowJet.mass_in hAxJet.mass_in
    expansion_in := htransfer _ _ _ (hselect .expansion)
      hOldJet.expansion_in hLowJet.expansion_in hAxJet.expansion_in
    contraction_out := htransfer _ _ _ (hselect .contraction)
      hOldJet.contraction_out hLowJet.contraction_out hAxJet.contraction_out
    theta_in := htransfer _ _ _ htheta
      hOldJet.theta_in hLowJet.theta_in hAxJet.theta_in
    zeta_out := htransfer _ _ _ hzeta
      hOldJet.zeta_out hLowJet.zeta_out hAxJet.zeta_out
    outgoing_in := htransfer _ _ _ (hselect .outgoing)
      hOldJet.outgoing_in hLowJet.outgoing_in hAxJet.outgoing_in
    incoming_out := htransfer _ _ _ (hselect .incoming)
      hOldJet.incoming_out hLowJet.incoming_out hAxJet.incoming_out
  }

end ChristodoulouBV.Uniqueness

end
