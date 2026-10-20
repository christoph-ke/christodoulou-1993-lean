module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesCoverFields
public import ChristodoulouBV.Uniqueness.RouteBGluingOldTerminal
import ChristodoulouBV.Uniqueness.RouteBGluingJetTransfer
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# The lower strip meets the clipped old region

The closed old piece equals the canonical terminal trace data on its upper
rectangle. This identifies its values and full relative first jets with
the lower strip along the clipped horizontal seam.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The terminal physical fields are the physical fields reconstructed from
their seven-state tuple wherever the terminal radius is positive. -/
theorem OffAxisTerminalC1Packet.terminalFields_eq_rectangleStateFields
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    {p : ℝ × ℝ} (hr : P.state.r p ≠ 0) :
    ∀ c : RouteBField,
      routeBField P.terminalFields c p =
        routeBField (rectangleStateFields P.state.rectangleState) c p := by
  intro c
  cases c <;>
    simp only [OffAxisTerminalC1Packet.terminalFields,
      routeBField, rectangleStateFields, routeBFieldsOfComponents,
      OffAxisTerminalTraces.rectangleState, C1Solution.statePhi,
      C1Solution.statePsi, C1Solution.stateRadius,
      C1Solution.stateBeta, C1Solution.stateMass,
      C1Solution.stateLam, C1Solution.stateNu,
      C1Solution.stateAlpha]
  field_simp

/-- Value and full-jet matching on the terminal rectangles transfers to
the clipped old/lower seam. -/
theorem routeB_clipped_old_lower_seam_of_terminal
    {a vBar vStar b : ℝ} (ha : 0 < a)
    (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hStarb : vStar < b)
    (SOld SBase SLow : Fields)
    (hOldC1 : RouteBFieldsC1On SOld (routeBOldRegion a vStar))
    (hOldBase : RouteBFieldsEqOn SOld SBase
      (routeBLowerRegion a vBar vStar))
    (hBaseLow : RouteBFieldsEqOn SBase SLow
      (routeBLowerRegion a vBar vStar ∩
        routeBLowerRegion a vStar b))
    (hBaseLowJet : RouteBFieldsJetEqOn SBase SLow
      (routeBLowerRegion a vBar vStar)
      (routeBLowerRegion a vStar b)) :
    RouteBFieldsEqOn SOld SLow
        (routeBOldRegion a vStar ∩ routeBLowerRegion a vStar b) ∧
      RouteBFieldsJetEqOn SOld SLow
        (routeBOldRegion a vStar) (routeBLowerRegion a vStar b) := by
  let KBase := routeBLowerRegion a vBar vStar
  let KOld := routeBOldRegion a vStar
  let KLow := routeBLowerRegion a vStar b
  have hBaseSub : KBase ⊆ KOld := by
    intro p hp
    exact mem_routeBOldRegion.mpr
      ⟨hp.1.1, hp.1.2, hp.1.2.trans (haBar.le.trans hp.2.1), hp.2.2⟩
  have hBaseUnique : UniqueDiffOn ℝ KBase :=
    uniqueDiffOn_convex (routeBLowerRegion_closed_convex a vBar vStar).2
      (routeBLowerRegion_interior_nonempty ha hBarStar)
  have hSeamSub : KOld ∩ KLow ⊆ KBase ∩ KLow := by
    intro p hp
    have h := hp
    rw [routeB_clipped_old_inter_lower
      (haBar.trans hBarStar).le hStarb.le] at h
    exact ⟨⟨h.1, ⟨by simpa only [h.2] using hBarStar.le, h.2.le⟩⟩, hp.2⟩
  constructor
  · intro c p hp
    have hpBase := hSeamSub hp
    exact (hOldBase c hpBase.1).trans (hBaseLow c hpBase)
  · intro c p hp
    have hpBase := hSeamSub hp
    have hOldJet := fderivWithin_eq_of_eqOn_subset
      (hOldC1 c) hBaseSub hBaseUnique (hOldBase c) hpBase.1
    exact hOldJet.trans (hBaseLowJet c hpBase)

/-- The canonical terminal trace data identify the old closed piece with the
physical lower strip in value and full first jet on their clipped seam. -/
theorem OffAxisTerminalC1Packet.clipped_old_lower_seam
    {a vBar vStar b : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar)
    (hBarStar : vBar < vStar) (hStarb : vStar < b)
    (SOld SLow : Fields)
    (hOldC1 : RouteBFieldsC1On SOld (routeBOldRegion a vStar))
    (hOldTop : RouteBFieldsEqOn SOld P.terminalFields
      (routeBLowerRegion a vBar vStar))
    (hBaseLow : RouteBFieldsEqOn
      (rectangleStateFields P.state.rectangleState) SLow
      (routeBLowerRegion a vBar vStar ∩
        routeBLowerRegion a vStar b))
    (hBaseLowJet : RouteBFieldsJetEqOn
      (rectangleStateFields P.state.rectangleState) SLow
      (routeBLowerRegion a vBar vStar)
      (routeBLowerRegion a vStar b)) :
    RouteBFieldsEqOn SOld SLow
        (routeBOldRegion a vStar ∩ routeBLowerRegion a vStar b) ∧
      RouteBFieldsJetEqOn SOld SLow
        (routeBOldRegion a vStar) (routeBLowerRegion a vStar b) := by
  have hOldBase : RouteBFieldsEqOn SOld
      (rectangleStateFields P.state.rectangleState)
      (routeBLowerRegion a vBar vStar) := by
    intro c p hp
    have hr : P.state.r p ≠ 0 := by
      have hfloor := (P.state.floors p.1 hp.1 p.2 hp.2).1
      exact ne_of_gt (P.state.radius_pos.trans_le hfloor)
    exact (hOldTop c hp).trans
      (P.terminalFields_eq_rectangleStateFields hr c)
  exact routeB_clipped_old_lower_seam_of_terminal
    ha haBar hBarStar hStarb SOld
    (rectangleStateFields P.state.rectangleState) SLow
    hOldC1 hOldBase hBaseLow hBaseLowJet

end ChristodoulouBV.Uniqueness

end
