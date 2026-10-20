module

public import ChristodoulouBV.Uniqueness.RouteBGluingClippedClassicalTransfer
public import ChristodoulouBV.Uniqueness.RouteBGluingClassicalBridge
public import ChristodoulouBV.Uniqueness.RouteBGluingClippedGauge
public import ChristodoulouBV.Uniqueness.RouteBGluingClippedSigns
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Generic corrected three-region Route B patch

Three closed C¹ seven-field pieces with compatible values and full first
jets glue to one frozen C¹ solution on the enlarged initial-edge development.
The local classical equations, signs, regular axis, and initial data are
properties of the supplied pieces. The Route B construction provides those
pieces in its separate terminal, lower-cover, axis, and seam constructions.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Generic Route B gluing for the corrected cover and exact frozen
conclusion. `SOld` is C¹ only on the clipped old region `0 ≤ u ≤ a`,
`u ≤ v ≤ vStar`; the axis piece owns the rest of the old triangle. The
local jet equations are the relative boundary form of the classical
equations on each piece. -/
theorem exists_routeB_clipped_three_region_isC1Solution
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar) (hStarb : vStar < b)
    (alpha₀ : ℝ → ℝ) (SOld SLow SAx : Fields)
    (hOldC1 : RouteBFieldsC1On SOld (routeBOldRegion a vStar))
    (hLowC1 : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hAxC1 : RouteBFieldsC1On SAx (closedCoordTriangle a b))
    (hOldLow : RouteBFieldsEqOn SOld SLow
      (routeBOldRegion a vStar ∩ routeBLowerRegion a vStar b))
    (hOldAx : RouteBFieldsEqOn SOld SAx
      (routeBOldRegion a vStar ∩ closedCoordTriangle a b))
    (hLowAx : RouteBFieldsEqOn SLow SAx
      (routeBLowerRegion a vStar b ∩ closedCoordTriangle a b))
    (hJetOldLow : RouteBFieldsJetEqOn SOld SLow
      (routeBOldRegion a vStar) (routeBLowerRegion a vStar b))
    (hJetOldAx : RouteBFieldsJetEqOn SOld SAx
      (routeBOldRegion a vStar) (closedCoordTriangle a b))
    (hJetLowAx : RouteBFieldsJetEqOn SLow SAx
      (routeBLowerRegion a vStar b) (closedCoordTriangle a b))
    (hOldClassical : RouteBClassicalJetOn b
      (routeBOldRegion a vStar) SOld)
    (hLowClassical : RouteBClassicalJetOn b
      (routeBLowerRegion a vStar b) SLow)
    (hAxClassical : RouteBClassicalJetOn b
      (closedCoordTriangle a b) SAx)
    (hOldAxis : ∀ u ∈ Icc (0 : ℝ) a,
      SOld.r u u = 0 ∧ SOld.m u u = 0)
    (hAxAxis : ∀ u ∈ Icc a b,
      SAx.r u u = 0 ∧ SAx.m u u = 0)
    (hOldLam : ∀ p ∈ routeBOldRegion a vStar,
      0 < SOld.lam p.1 p.2)
    (hLowLam : ∀ p ∈ routeBLowerRegion a vStar b,
      0 < SLow.lam p.1 p.2)
    (hAxLam : ∀ p ∈ closedCoordTriangle a b,
      0 < SAx.lam p.1 p.2)
    (hOldSigns : ∀ p ∈ routeBOldRegion a vStar,
      p ∈ developmentWithInitialEdge b →
      0 < SOld.r p.1 p.2 ∧ SOld.nu p.1 p.2 < 0 ∧
        0 < 1 - 2 * SOld.m p.1 p.2 / SOld.r p.1 p.2)
    (hLowSigns : ∀ p ∈ routeBLowerRegion a vStar b,
      p ∈ developmentWithInitialEdge b →
      0 < SLow.r p.1 p.2 ∧ SLow.nu p.1 p.2 < 0 ∧
        0 < 1 - 2 * SLow.m p.1 p.2 / SLow.r p.1 p.2)
    (hAxSigns : ∀ p ∈ closedCoordTriangle a b,
      p ∈ developmentWithInitialEdge b →
      0 < SAx.r p.1 p.2 ∧ SAx.nu p.1 p.2 < 0 ∧
        0 < 1 - 2 * SAx.m p.1 p.2 / SAx.r p.1 p.2)
    (hOldData : ∀ v ∈ Icc (0 : ℝ) vStar,
      SOld.r 0 v = v / 2 ∧ SOld.alpha 0 v = alpha₀ v)
    (hLowData : ∀ v ∈ Icc vStar b,
      SLow.r 0 v = v / 2 ∧ SLow.alpha 0 v = alpha₀ v) :
    ∃ T : Fields,
      IsC1Solution (developmentWithInitialEdge b) T ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        T.r 0 v = v / 2 ∧ T.alpha 0 v = alpha₀ v) ∧
      RouteBFieldsEqOn T SOld (routeBOldRegion a vStar) ∧
      RouteBFieldsEqOn T SLow (routeBLowerRegion a vStar b) ∧
      RouteBFieldsEqOn T SAx (closedCoordTriangle a b) := by
  obtain ⟨T, hTC1, hMatchOld, hMatchLow, hMatchAx, hData⟩ :=
    exists_routeB_clipped_fields_c1_glue_with_initial_data
      ha haStar hStarb alpha₀ SOld SLow SAx
      hOldC1 hLowC1 hAxC1 hOldLow hOldAx hLowAx
      hJetOldLow hJetOldAx hJetLowAx hOldData hLowData
  have hTJet : RouteBClassicalJetOn b (closedCoordTriangle 0 b) T :=
    routeB_clipped_classicalJetOn_of_three ha haStar hStarb
      SOld SLow SAx T hTC1 hMatchOld hMatchLow hMatchAx
      hOldClassical hLowClassical hAxClassical
  have hAxis : ∀ u ∈ Icc (0 : ℝ) b,
      T.r u u = 0 ∧ T.m u u = 0 := by
    intro u hu
    by_cases hBelow : u ≤ a
    · have hp : (u, u) ∈ routeBOldRegion a vStar :=
        mem_routeBOldRegion.mpr ⟨hu.1, hBelow, le_rfl,
          hBelow.trans haStar.le⟩
      have hr := hMatchOld .radius hp
      have hm := hMatchOld .mass hp
      change T.r u u = SOld.r u u at hr
      change T.m u u = SOld.m u u at hm
      obtain ⟨hro, hmo⟩ := hOldAxis u ⟨hu.1, hBelow⟩
      exact ⟨hr.trans hro, hm.trans hmo⟩
    · have hAbove : a ≤ u := le_of_not_ge hBelow
      have hp : (u, u) ∈ closedCoordTriangle a b :=
        ⟨hAbove, le_rfl, hu.2⟩
      have hr := hMatchAx .radius hp
      have hm := hMatchAx .mass hp
      change T.r u u = SAx.r u u at hr
      change T.m u u = SAx.m u u at hm
      obtain ⟨hra, hma⟩ := hAxAxis u ⟨hAbove, hu.2⟩
      exact ⟨hr.trans hra, hm.trans hma⟩
  obtain ⟨hLam, hSigns⟩ := routeB_clipped_signs_of_fields_eqOn
    ha haStar hStarb SOld SLow SAx T
    hMatchOld hMatchLow hMatchAx
    hOldLam hLowLam hAxLam hOldSigns hLowSigns hAxSigns
  have hb : 0 < b := ha.trans (haStar.trans hStarb)
  have hSolution : IsC1Solution (developmentWithInitialEdge b) T :=
    routeB_isC1Solution_of_classicalJet hb T hTC1 hTJet
      (fun u hu => (hAxis u hu).1)
      (fun u hu => (hAxis u hu).2)
      (fun p hp => (hSigns p hp).1)
      hLam
      (fun p hp => (hSigns p hp).2.1)
      (fun p hp => (hSigns p hp).2.2)
  exact ⟨T, hSolution, hData, hMatchOld, hMatchLow, hMatchAx⟩

end ChristodoulouBV.Uniqueness

end
