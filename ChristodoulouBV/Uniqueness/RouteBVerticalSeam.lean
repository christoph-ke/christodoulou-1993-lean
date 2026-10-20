module

public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamBetaJet
public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamPartial
import ChristodoulouBV.C1Solution.RectangleSeams
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Complete Route B axis/lower vertical seam

Prescribed edge data and common corner values determine all seven field
traces. The classical equations and physical signs propagate the remaining
transverse jets. Thus the lower band and axis triangle have equal values
and full relative first jets on their shared closed edge.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The physical axis and lower pieces have matching seven-state values and
full relative first jets on their closed vertical seam. The conclusion is
the exact seam interface used by clipped three-region gluing. -/
theorem routeB_vertical_seam
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (hStarb : vStar < b) (SLow SAx : Fields)
    (hLowC1 : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hAxC1 : RouteBFieldsC1On SAx (closedCoordTriangle a b))
    (hLowJet : RouteBClassicalJetOn b (routeBLowerRegion a vStar b) SLow)
    (hAxJet : RouteBClassicalJetOn b (closedCoordTriangle a b) SAx)
    (hRLow : ∀ p ∈ routeBLowerRegion a vStar b, 0 < SLow.r p.1 p.2)
    (hLamLow : ∀ p ∈ routeBLowerRegion a vStar b, 0 < SLow.lam p.1 p.2)
    (_hNuLow : ∀ p ∈ routeBLowerRegion a vStar b, SLow.nu p.1 p.2 < 0)
    (hGapLow : ∀ p ∈ routeBLowerRegion a vStar b,
      0 < 1 - 2 * SLow.m p.1 p.2 / SLow.r p.1 p.2)
    (hRAx : ∀ p ∈ closedCoordTriangle a b, p.1 < p.2 →
      0 < SAx.r p.1 p.2)
    (hLamAx : ∀ p ∈ closedCoordTriangle a b,
      0 < SAx.lam p.1 p.2)
    (_hNuAx : ∀ p ∈ closedCoordTriangle a b, p.1 < p.2 →
      SAx.nu p.1 p.2 < 0)
    (hGapAx : ∀ p ∈ closedCoordTriangle a b, p.1 < p.2 →
      0 < 1 - 2 * SAx.m p.1 p.2 / SAx.r p.1 p.2)
    (hEdgeLam : ∀ v ∈ Icc vStar b, SLow.lam a v = SAx.lam a v)
    (hEdgeQuot : ∀ v ∈ Icc vStar b,
      SLow.alpha a v / SLow.lam a v = SAx.alpha a v / SAx.lam a v)
    (hEdgeRadius : ∀ v ∈ Icc vStar b, SLow.r a v = SAx.r a v)
    (hCornerValues : ∀ c : RouteBField,
      routeBField SLow c (a, vStar) = routeBField SAx c (a, vStar))
    (hCornerJets : ∀ c : RouteBField,
      fderivWithin ℝ (routeBField SLow c)
        (routeBLowerRegion a vStar b) (a, vStar) =
      fderivWithin ℝ (routeBField SAx c)
        (closedCoordTriangle a b) (a, vStar)) :
    RouteBFieldsEqOn SLow SAx
      (routeBLowerRegion a vStar b ∩ closedCoordTriangle a b) ∧
    RouteBFieldsJetEqOn SLow SAx
      (routeBLowerRegion a vStar b) (closedCoordTriangle a b) := by
  let KL := routeBLowerRegion a vStar b
  let KA := closedCoordTriangle a b
  have hMapL : ∀ v ∈ Icc vStar b, (a, v) ∈ KL :=
    fun v hv => ⟨⟨ha.le, le_rfl⟩, hv⟩
  have hMapA : ∀ v ∈ Icc vStar b, (a, v) ∈ KA :=
    fun v hv => ⟨le_rfl, haStar.le.trans hv.1, hv.2⟩
  have hPartial := routeB_vertical_values_and_five_horizontal_jets_eq
    ha haStar hStarb SLow SAx hLowC1 hAxC1 hLowJet hAxJet
    (fun v hv => hRLow (a, v) (hMapL v hv))
    (fun v hv => hLamLow (a, v) (hMapL v hv))
    (fun v hv => hLamAx (a, v) (hMapA v hv))
    (fun v hv => hGapLow (a, v) (hMapL v hv))
    hEdgeLam hEdgeQuot hEdgeRadius hCornerValues
  have hValues := hPartial.1
  have hPrimaryJets :
      ∀ c ∈ ({RouteBField.radius, RouteBField.mass,
          RouteBField.expansion} : Set RouteBField),
        ∀ v ∈ Icc vStar b,
          fderivWithin ℝ (routeBField SLow c) KL (a, v) =
          fderivWithin ℝ (routeBField SAx c) KA (a, v) := by
    intro c hc v hv
    have hcFive : c ∈ ({RouteBField.radius, RouteBField.scalar,
        RouteBField.mass, RouteBField.expansion,
        RouteBField.outgoing} : Set RouteBField) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc ⊢
      tauto
    apply C1Solution.continuousLinearMap_ext_coordinate
    · exact hPartial.2 c hcFive v hv
    · exact routeB_vertical_jet_eq_of_trace_eq ha haStar hStarb
        (hLowC1 c) (hAxC1 c) (hValues c) hv
  have hNu : ∀ v ∈ Icc vStar b,
      (fderivWithin ℝ (routeBField SLow .contraction) KL (a, v)) (1, 0) =
      (fderivWithin ℝ (routeBField SAx .contraction) KA (a, v)) (1, 0) :=
    routeB_vertical_nu_horizontal_jet_eq
      ha haStar hStarb SLow SAx hLowC1 hAxC1 hLowJet hAxJet
      hRLow hGapLow hRAx hGapAx hValues hPrimaryJets
      (congrArg (fun J : (ℝ × ℝ) →L[ℝ] ℝ => J (1, 0))
        (hCornerJets .contraction))
  have hPhi : ∀ v ∈ Icc vStar b,
      (fderivWithin ℝ (routeBField SLow .scalar) KL (a, v)) (1, 0) =
      (fderivWithin ℝ (routeBField SAx .scalar) KA (a, v)) (1, 0) :=
    hPartial.2 .scalar (by simp)
  have hBeta : ∀ v ∈ Icc vStar b,
      (fderivWithin ℝ (routeBField SLow .incoming) KL (a, v)) (1, 0) =
      (fderivWithin ℝ (routeBField SAx .incoming) KA (a, v)) (1, 0) :=
    routeB_vertical_beta_horizontal_jet_eq
      ha haStar hStarb SLow SAx hLowC1 hAxC1 hLowJet hAxJet
      hRLow hGapLow hRAx hGapAx hValues hPrimaryJets hNu hPhi
      (congrArg (fun J : (ℝ × ℝ) →L[ℝ] ℝ => J (1, 0))
        (hCornerJets .incoming))
  have hHorizontal : ∀ c : RouteBField, ∀ v ∈ Icc vStar b,
      (fderivWithin ℝ (routeBField SLow c) KL (a, v)) (1, 0) =
      (fderivWithin ℝ (routeBField SAx c) KA (a, v)) (1, 0) := by
    intro c v hv
    cases c with
    | radius => exact hPartial.2 .radius (by simp) v hv
    | scalar => exact hPhi v hv
    | mass => exact hPartial.2 .mass (by simp) v hv
    | expansion => exact hPartial.2 .expansion (by simp) v hv
    | contraction => exact hNu v hv
    | outgoing => exact hPartial.2 .outgoing (by simp) v hv
    | incoming => exact hBeta v hv
  have hFull := routeB_vertical_full_jets_eq_of_horizontal_jets_eq
    ha haStar hStarb SLow SAx hLowC1 hAxC1 hValues hHorizontal
  constructor
  · intro c p hp
    have hu : p.1 = a := le_antisymm hp.1.1.2 hp.2.1
    have hv : p.2 ∈ Icc vStar b := hp.1.2
    have hpEq : p = (a, p.2) := by
      ext
      · exact hu
      · rfl
    rw [hpEq]
    exact hValues c p.2 hv
  · intro c p hp
    have hu : p.1 = a := le_antisymm hp.1.1.2 hp.2.1
    have hv : p.2 ∈ Icc vStar b := hp.1.2
    have hpEq : p = (a, p.2) := by
      ext
      · exact hu
      · rfl
    rw [hpEq]
    exact hFull c p.2 hv

end ChristodoulouBV.Uniqueness

end
