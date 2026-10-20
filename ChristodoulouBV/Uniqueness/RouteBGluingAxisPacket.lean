module

public import ChristodoulouBV.Uniqueness.RouteBGluingAxisClassical
public import ChristodoulouBV.Uniqueness.RouteBGluingOldFullPacket
public import ChristodoulouBV.Uniqueness.RouteBGluingClippedFinal

/-!
# Axis input and partially instantiated corrected Route B gluing

The classical axis solution supplies all axis-region hypotheses. The
remaining assumptions in the final theorem concern the lower region and
its two seams.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Complete axis-region input to corrected three-region gluing. -/
theorem exists_routeB_axis_piece_packet
    {a b : ℝ} {SAx : Fields}
    (ha : 0 ≤ a) (hab : a < b)
    (HT : C1Solution.AxisClassicalSolution a b SAx) :
    RouteBFieldsC1On SAx (closedCoordTriangle a b) ∧
    RouteBClassicalJetOn b (closedCoordTriangle a b) SAx ∧
    (∀ u ∈ Icc a b, SAx.r u u = 0 ∧ SAx.m u u = 0) ∧
    (∀ p ∈ closedCoordTriangle a b, 0 < SAx.lam p.1 p.2) ∧
    (∀ p ∈ closedCoordTriangle a b,
      p ∈ developmentWithInitialEdge b →
      0 < SAx.r p.1 p.2 ∧ SAx.nu p.1 p.2 < 0 ∧
        0 < 1 - 2 * SAx.m p.1 p.2 / SAx.r p.1 p.2) := by
  obtain ⟨hAxis, hLam, hSigns⟩ := routeB_axis_values_signs HT
  exact ⟨routeB_axis_fields_c1 HT,
    routeB_axis_classicalJetOn ha hab HT, hAxis, hLam, hSigns⟩

/-- The old and axis inputs are now discharged. Given one lower piece and
its horizontal and vertical seam data, the corrected three-region theorem
produces the enlarged frozen C¹ solution. -/
theorem OffAxisTerminalC1Packet.exists_routeB_clipped_solution_from_lower
    {alpha₀ : ℝ → ℝ} {a vBar vStar b u₀ ε : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (J : RouteBTerminalBaseJets P)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hStarb : vStar < b)
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ d ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge d) (S d) ∧
      (∀ v ∈ Ioo (0 : ℝ) d,
        (S d).r 0 v = v / 2 ∧ (S d).alpha 0 v = alpha₀ v))
    (hε : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ d ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge d,
        2 * (S d).m p.1 p.2 / (S d).r p.1 p.2 ≤ ε)
    {SAx : Fields}
    (HT : C1Solution.AxisClassicalSolution a b SAx)
    (hrT : ∀ v ∈ Icc a vStar, SAx.r a v = P.rEdge v)
    (hpsiT : ∀ v ∈ Icc a vStar,
      SAx.r a v * SAx.phi a v = ∫ s in a..v, P.g s * P.hEdge s) :
    ∃ SOld : Fields,
      RouteBFieldsC1On SOld (routeBOldRegion a vStar) ∧
      RouteBClassicalJetOn b (routeBOldRegion a vStar) SOld ∧
      (∀ e ∈ Ioo a vStar, ∀ d ∈ Ioo e vStar,
        RouteBFieldsEqOn SOld (routeBCanonicalOldFields d (S d))
          (routeBOldRegion a e)) ∧
      RouteBFieldsEqOn SOld P.terminalFields
        (routeBLowerRegion a vBar vStar) ∧
      ∀ SLow : Fields,
      RouteBFieldsC1On SLow (routeBLowerRegion a vStar b) →
      RouteBClassicalJetOn b (routeBLowerRegion a vStar b) SLow →
      RouteBFieldsEqOn SOld SLow
        (routeBOldRegion a vStar ∩ routeBLowerRegion a vStar b) →
      RouteBFieldsJetEqOn SOld SLow
        (routeBOldRegion a vStar) (routeBLowerRegion a vStar b) →
      RouteBFieldsEqOn SLow SAx
        (routeBLowerRegion a vStar b ∩ closedCoordTriangle a b) →
      RouteBFieldsJetEqOn SLow SAx
        (routeBLowerRegion a vStar b) (closedCoordTriangle a b) →
      (∀ p ∈ routeBLowerRegion a vStar b,
        0 < SLow.lam p.1 p.2) →
      (∀ p ∈ routeBLowerRegion a vStar b,
        p ∈ developmentWithInitialEdge b →
        0 < SLow.r p.1 p.2 ∧ SLow.nu p.1 p.2 < 0 ∧
          0 < 1 - 2 * SLow.m p.1 p.2 / SLow.r p.1 p.2) →
      (∀ v ∈ Icc vStar b,
        SLow.r 0 v = v / 2 ∧ SLow.alpha 0 v = alpha₀ v) →
      ∃ T : Fields,
        IsC1Solution (developmentWithInitialEdge b) T ∧
        (∀ v ∈ Ioo (0 : ℝ) b,
          T.r 0 v = v / 2 ∧ T.alpha 0 v = alpha₀ v) ∧
        RouteBFieldsEqOn T SOld (routeBOldRegion a vStar) ∧
        RouteBFieldsEqOn T SLow (routeBLowerRegion a vStar b) ∧
        RouteBFieldsEqOn T SAx (closedCoordTriangle a b) := by
  obtain ⟨hAxC1, hAxJet, hAxAxis, hAxLam, hAxSigns⟩ :=
    exists_routeB_axis_piece_packet ha.le (haBar.trans (hBarStar.trans hStarb)) HT
  obtain ⟨SOld, hOldC1, hOldJet, hOldMatch, hOldTop, hOldAxis, hOldData,
      hOldLam, hOldSigns, hOldAx, hJetOldAx⟩ :=
    P.exists_routeB_closed_old_full_packet J ha haBar hBarStar hStarb
      hu₀ hα hfamily hε htail HT hrT hpsiT hAxC1
  refine ⟨SOld, hOldC1, hOldJet, hOldMatch, hOldTop, ?_⟩
  intro SLow hLowC1 hLowJet hOldLow hJetOldLow hLowAx hJetLowAx
    hLowLam hLowSigns hLowData
  exact exists_routeB_clipped_three_region_isC1Solution
    ha (haBar.trans hBarStar) hStarb alpha₀ SOld SLow SAx
    hOldC1 hLowC1 hAxC1 hOldLow hOldAx hLowAx
    hJetOldLow hJetOldAx hJetLowAx
    hOldJet hLowJet hAxJet hOldAxis hAxAxis
    hOldLam hLowLam hAxLam hOldSigns hLowSigns hAxSigns
    hOldData hLowData

end ChristodoulouBV.Uniqueness

end
