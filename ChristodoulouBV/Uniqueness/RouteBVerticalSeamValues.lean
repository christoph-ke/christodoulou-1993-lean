module

public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamBeta
import Mathlib.Tactic

/-!
# Complete value trace on the Route B vertical seam

The three prescribed characteristic data and the seven corner values
determine every primary field value on the closed shared edge. The scalar,
mass, contraction, and incoming transport equations propagate the four
unprescribed values in that order.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The edge data `λ`, `α/λ`, and `r`, physical positivity on the edge,
the local classical equations, and seven matching corner values imply that
all seven field values agree on the full lower/axis seam. -/
theorem routeB_vertical_seven_values_eq
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (hStarb : vStar < b) (SLow SAx : Fields)
    (hLowC1 : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hAxC1 : RouteBFieldsC1On SAx (closedCoordTriangle a b))
    (hLowJet : RouteBClassicalJetOn b (routeBLowerRegion a vStar b) SLow)
    (hAxJet : RouteBClassicalJetOn b (closedCoordTriangle a b) SAx)
    (hRadiusLow : ∀ v ∈ Icc vStar b, 0 < SLow.r a v)
    (hLamLow : ∀ v ∈ Icc vStar b, 0 < SLow.lam a v)
    (hLamAx : ∀ v ∈ Icc vStar b, 0 < SAx.lam a v)
    (hGapLow : ∀ v ∈ Icc vStar b,
      0 < 1 - 2 * SLow.m a v / SLow.r a v)
    (hLam : ∀ v ∈ Icc vStar b, SLow.lam a v = SAx.lam a v)
    (hQuot : ∀ v ∈ Icc vStar b,
      SLow.alpha a v / SLow.lam a v = SAx.alpha a v / SAx.lam a v)
    (hRadius : ∀ v ∈ Icc vStar b, SLow.r a v = SAx.r a v)
    (hCorner : ∀ c : RouteBField,
      routeBField SLow c (a, vStar) = routeBField SAx c (a, vStar)) :
    ∀ c : RouteBField, ∀ v ∈ Icc vStar b,
      routeBField SLow c (a, v) = routeBField SAx c (a, v) := by
  have hPrescribed := routeB_vertical_prescribed_values_eq
    SLow SAx hLamLow hLamAx hLam hQuot hRadius
  have hAlpha : ∀ v ∈ Icc vStar b,
      SLow.alpha a v = SAx.alpha a v :=
    fun v hv => (hPrescribed v hv).2.1
  have hPhi := routeB_vertical_scalar_values_eq
    ha haStar hStarb SLow SAx hLowC1 hAxC1 hLowJet hAxJet
    hRadius hRadiusLow hAlpha (hCorner .scalar)
  have hMass := routeB_vertical_mass_values_eq
    ha haStar SLow SAx hLowC1 hAxC1 hLowJet hAxJet
    hRadius hRadiusLow hLam hLamLow hAlpha hPhi (hCorner .mass)
  have hNu := routeB_vertical_nu_values_eq
    ha haStar SLow SAx hLowC1 hAxC1 hLowJet hAxJet
    hRadius hRadiusLow hLam hMass hGapLow (hCorner .contraction)
  have hBeta := routeB_vertical_beta_values_eq
    ha haStar SLow SAx hLowC1 hAxC1 hLowJet hAxJet
    hRadius hPhi hMass hLam hNu (hCorner .incoming)
  intro c v hv
  cases c with
  | radius => exact hRadius v hv
  | scalar => exact hPhi v hv
  | mass => exact hMass v hv
  | expansion => exact hLam v hv
  | contraction => exact hNu v hv
  | outgoing => exact hAlpha v hv
  | incoming => exact hBeta v hv

end ChristodoulouBV.Uniqueness

end
