module

public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamPhiJet
import Mathlib.Tactic

/-!
# Proven part of the Route B vertical seam

The characteristic equations identify all seven values and the five
directly constrained incoming jets. The linearized equations for the
remaining contraction and incoming transport jets are handled separately.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- All seven values and five transverse coordinate jets agree on the
axis/rectangle seam under the physical sign and characteristic data
hypotheses. The two remaining transverse jets are `νᵤ` and `βᵤ`. -/
theorem routeB_vertical_values_and_five_horizontal_jets_eq
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
    (∀ c : RouteBField, ∀ v ∈ Icc vStar b,
      routeBField SLow c (a, v) = routeBField SAx c (a, v)) ∧
    (∀ c ∈ ({RouteBField.radius, RouteBField.scalar,
        RouteBField.mass, RouteBField.expansion,
        RouteBField.outgoing} : Set RouteBField),
      ∀ v ∈ Icc vStar b,
        (fderivWithin ℝ (routeBField SLow c)
          (routeBLowerRegion a vStar b) (a, v)) (1, 0) =
        (fderivWithin ℝ (routeBField SAx c)
          (closedCoordTriangle a b) (a, v)) (1, 0)) := by
  have hValues := routeB_vertical_seven_values_eq
    ha haStar hStarb SLow SAx hLowC1 hAxC1 hLowJet hAxJet
    hRadiusLow hLamLow hLamAx hGapLow hLam hQuot hRadius hCorner
  have hDirect := routeB_vertical_direct_horizontal_jets_eq
    ha haStar hStarb SLow SAx hLowC1 hAxC1 hLowJet hAxJet hValues
  have hPhi := routeB_vertical_phi_horizontal_jet_eq
    ha haStar hStarb SLow SAx hLowC1 hAxC1
    (hValues .radius) hRadiusLow (hValues .scalar)
    (hDirect.1 .radius (by simp)) hDirect.2
  refine ⟨hValues, ?_⟩
  intro c hc
  rcases Set.mem_insert_iff.mp hc with rfl | hc
  · exact hDirect.1 .radius (by simp)
  rcases Set.mem_insert_iff.mp hc with rfl | hc
  · exact hPhi
  rcases Set.mem_insert_iff.mp hc with rfl | hc
  · exact hDirect.1 .mass (by simp)
  rcases Set.mem_insert_iff.mp hc with rfl | hc
  · exact hDirect.1 .expansion (by simp)
  have hc : c = RouteBField.outgoing := by simpa using hc
  subst c
  exact hDirect.1 .outgoing (by simp)

end ChristodoulouBV.Uniqueness

end
