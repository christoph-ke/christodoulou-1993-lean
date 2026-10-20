module

public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamJetClosure
import Mathlib.Tactic

/-!
# Directly constrained incoming jets on the Route B seam

Five of the incoming coordinate jets are given directly by the classical
equations: those of radius, expansion, outgoing transport, mass, and the
rescaled scalar `r φ`. Their right-hand sides agree once the values agree.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Equality of all field values forces equality of the four primary
incoming jets fixed directly by the classical equations, together with the
incoming jet of `r φ`. -/
theorem routeB_vertical_direct_horizontal_jets_eq
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (hStarb : vStar < b) (SLow SAx : Fields)
    (hLowC1 : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hAxC1 : RouteBFieldsC1On SAx (closedCoordTriangle a b))
    (hLowJet : RouteBClassicalJetOn b (routeBLowerRegion a vStar b) SLow)
    (hAxJet : RouteBClassicalJetOn b (closedCoordTriangle a b) SAx)
    (hValues : ∀ c : RouteBField, ∀ v ∈ Icc vStar b,
      routeBField SLow c (a, v) = routeBField SAx c (a, v)) :
    (∀ c ∈ ({RouteBField.radius, RouteBField.expansion,
        RouteBField.outgoing, RouteBField.mass} : Set RouteBField),
      ∀ v ∈ Icc vStar b,
        (fderivWithin ℝ (routeBField SLow c)
          (routeBLowerRegion a vStar b) (a, v)) (1, 0) =
        (fderivWithin ℝ (routeBField SAx c)
          (closedCoordTriangle a b) (a, v)) (1, 0)) ∧
      (∀ v ∈ Icc vStar b,
        (fderivWithin ℝ
          (routeBScalarExpression routeBScalarRadiusExpr SLow)
          (routeBLowerRegion a vStar b) (a, v)) (1, 0) =
        (fderivWithin ℝ
          (routeBScalarExpression routeBScalarRadiusExpr SAx)
          (closedCoordTriangle a b) (a, v)) (1, 0)) := by
  have hSelectorLow (c : RouteBField) :
      ContDiffOn ℝ 1
        (routeBScalarExpression (routeBSelector c) SLow)
        (routeBLowerRegion a vStar b) := by
    have hfun : routeBScalarExpression (routeBSelector c) SLow =
        routeBField SLow c := by
      funext p
      rfl
    rw [hfun]
    exact hLowC1 c
  have hSelectorAx (c : RouteBField) :
      ContDiffOn ℝ 1
        (routeBScalarExpression (routeBSelector c) SAx)
        (closedCoordTriangle a b) := by
    have hfun : routeBScalarExpression (routeBSelector c) SAx =
        routeBField SAx c := by
      funext p
      rfl
    rw [hfun]
    exact hAxC1 c
  have hSelectorJet (c : RouteBField)
      (rhs : (RouteBField → ℝ) → ℝ)
      (hLowEq : RouteBLocalJetEquation b (routeBLowerRegion a vStar b)
        SLow (routeBSelector c) rhs (1, 0))
      (hAxEq : RouteBLocalJetEquation b (closedCoordTriangle a b)
        SAx (routeBSelector c) rhs (1, 0)) :
      ∀ v ∈ Icc vStar b,
        (fderivWithin ℝ (routeBField SLow c)
          (routeBLowerRegion a vStar b) (a, v)) (1, 0) =
        (fderivWithin ℝ (routeBField SAx c)
          (closedCoordTriangle a b) (a, v)) (1, 0) := by
    have h := routeB_vertical_horizontal_jets_eq_of_classical_equation
      ha haStar hStarb SLow SAx (routeBSelector c) rhs
      (hSelectorLow c) (hSelectorAx c) hLowEq hAxEq hValues
    have hfunLow : routeBScalarExpression (routeBSelector c) SLow =
        routeBField SLow c := by
      funext p
      rfl
    have hfunAx : routeBScalarExpression (routeBSelector c) SAx =
        routeBField SAx c := by
      funext p
      rfl
    rw [hfunLow, hfunAx] at h
    exact h
  constructor
  · intro c hc
    rcases Set.mem_insert_iff.mp hc with rfl | hc
    · exact hSelectorJet .radius (routeBSelector .contraction)
        hLowJet.radius_in hAxJet.radius_in
    rcases Set.mem_insert_iff.mp hc with rfl | hc
    · exact hSelectorJet .expansion routeBMixedExpr
        hLowJet.expansion_in hAxJet.expansion_in
    rcases Set.mem_insert_iff.mp hc with rfl | hc
    · exact hSelectorJet .outgoing routeBMixedScalarExpr
        hLowJet.outgoing_in hAxJet.outgoing_in
    have hc : c = RouteBField.mass := by simpa using hc
    subst c
    exact hSelectorJet .mass routeBMassIncomingExpr
      hLowJet.mass_in hAxJet.mass_in
  · have hψLow : ContDiffOn ℝ 1
        (routeBScalarExpression routeBScalarRadiusExpr SLow)
        (routeBLowerRegion a vStar b) := by
      change ContDiffOn ℝ 1
        (fun p : ℝ × ℝ => SLow.r p.1 p.2 * SLow.phi p.1 p.2)
        (routeBLowerRegion a vStar b)
      exact (hLowC1 .radius).mul (hLowC1 .scalar)
    have hψAx : ContDiffOn ℝ 1
        (routeBScalarExpression routeBScalarRadiusExpr SAx)
        (closedCoordTriangle a b) := by
      change ContDiffOn ℝ 1
        (fun p : ℝ × ℝ => SAx.r p.1 p.2 * SAx.phi p.1 p.2)
        (closedCoordTriangle a b)
      exact (hAxC1 .radius).mul (hAxC1 .scalar)
    exact routeB_vertical_horizontal_jets_eq_of_classical_equation
      ha haStar hStarb SLow SAx routeBScalarRadiusExpr
      (routeBSelector .incoming) hψLow hψAx
      hLowJet.scalar_radius_in hAxJet.scalar_radius_in hValues

end ChristodoulouBV.Uniqueness

end
