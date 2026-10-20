module

public import ChristodoulouBV.Uniqueness.RouteBAssemblyLifetime
public import ChristodoulouBV.Uniqueness.RouteBAssemblyShortLower
public import ChristodoulouBV.Uniqueness.RouteBAssemblyRadius
public import ChristodoulouBV.Uniqueness.RouteBAssemblyCorner
public import ChristodoulouBV.Uniqueness.RouteBVerticalSeam
public import ChristodoulouBV.Uniqueness.RouteBGluingOldFullPacket
public import ChristodoulouBV.Uniqueness.RouteBGluingClippedFinal
public import ChristodoulouBV.Uniqueness.RouteBGluingAxisPacket
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# Route B final assembly for the C¹ extension principle

Uniform old-family estimates fix an axis lifetime before the incoming
cutoff is selected. A short lower cover and the prescribed axis triangle
then meet at the terminal corner. The vertical seam theorem and corrected
three-region gluing produce a larger frozen development.
-/

public section

open Set ChristodoulouBV.AxisPicard

namespace ChristodoulouBV.Uniqueness

/-- The frozen Theorem 5.1 family and tail premises have a Route B C¹
extension beyond their common outgoing endpoint. -/
theorem exists_routeB_extension
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ d ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge d) (S d) ∧
      (∀ v ∈ Ioo (0 : ℝ) d,
        (S d).r 0 v = v / 2 ∧ (S d).alpha 0 v = alpha₀ v))
    (hε : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ d ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge d,
        2 * (S d).m p.1 p.2 / (S d).r p.1 p.2 ≤ ε) :
    ∃ v₁ : ℝ, vStar < v₁ ∧ ∃ T : Fields,
      IsC1Solution (developmentWithInitialEdge v₁) T ∧
      (∀ v ∈ Ioo (0 : ℝ) v₁,
        T.r 0 v = v / 2 ∧ T.alpha 0 v = alpha₀ v) := by
  obtain ⟨c, Clam, H, Tlife, a, vBar, η, b,
      hc, _, _, hTlife, hu₀a, haBar, hBarStar, hgap,
      hη, hηhalf, hb, hStarb, _, P, J, SOld₀, SLow,
      hOldBounds, hOld₀C1, hOld₀Top, hLowC1, hLowJet,
      hOld₀Low, hOld₀LowJet, hAnySeam, hLowLam,
      hLowSigns, hLowData⟩ :=
    exists_routeB_lower_cover_with_uniform_edge_lifetime
      hu₀ hα hfamily hε htail
  have ha : 0 < a := hu₀.1.trans hu₀a
  have haStar : a < vStar := haBar.trans hBarStar
  have hfloor : ∀ v ∈ Icc a vStar, c ≤ P.g v := by
    intro v hv
    simpa only [intervalC1Extension_eq hv] using (hOldBounds v hv).1
  obtain ⟨g, h, hg, hh, _, hOldEdge, hLowEdge⟩ :=
    P.exists_routeB_joined_physical_edge ha haBar hBarStar
      hStarb hc hfloor hfamily SOld₀ SLow hOld₀C1 hLowC1
      hOld₀Top hOld₀Low hOld₀LowJet hLowLam
  obtain ⟨η', b', hη', hη'η, hb', hStarb', _, SAx,
      HT, hBox, hAxOld, hAxLow⟩ :=
    P.exists_routeB_axis_from_joined_edge ha haBar hBarStar
      hη hc (by rw [← hTlife]; exact hgap)
      (by rw [← hTlife]; exact hηhalf)
      hOldBounds hg hh
      (fun v hv => (hOldEdge v hv))
      (by
        intro v hv
        exact hLowEdge v ⟨hv.1, by simpa only [hb] using hv.2⟩)
  have hbb : b' < b := by rw [hb', hb]; linarith only [hη'η]
  have hab' : a < b' := haStar.trans hStarb'
  obtain ⟨hLowC1', hLowJet', hLowLam', hLowSigns', hLowData'⟩ :=
    routeB_short_lower_packet ha haStar hStarb' hbb SLow
      hLowC1 hLowJet hLowLam hLowSigns hLowData
  have hAxC1 := routeB_axis_fields_c1 HT
  obtain ⟨SOld, hOldC1, hOldJet, _, hOldTop,
      hOldAxis, hOldData, hOldLam, hOldSigns,
      hOldAx, hOldAxJet⟩ :=
    P.exists_routeB_closed_old_full_packet J ha haBar hBarStar
      hStarb' hu₀ hα hfamily hε htail HT
      (fun v hv => (hAxOld v hv).1)
      (fun v hv => (hAxOld v hv).2) hAxC1
  obtain ⟨hOldLow, hOldLowJet⟩ :=
    routeB_short_lower_horizontal_seam ha hStarb' hbb.le
      P SLow hLowC1 hAnySeam SOld hOldC1 hOldTop
  obtain ⟨hCornerValues, hCornerJets⟩ :=
    routeB_triple_corner_values_and_jets ha haStar hStarb'
      SOld SLow SAx hOldLow hOldAx hOldLowJet hOldAxJet
  have hEdgeLam : ∀ v ∈ Icc vStar b',
      SLow.lam a v = SAx.lam a v :=
    fun v hv => (hAxLow v hv).1.symm
  have hEdgeQuot : ∀ v ∈ Icc vStar b',
      SLow.alpha a v / SLow.lam a v =
        SAx.alpha a v / SAx.lam a v :=
    fun v hv => (hAxLow v hv).2.symm
  have hCornerR : SLow.r a vStar = SAx.r a vStar :=
    hCornerValues .radius
  have hEdgeRadius := routeB_lower_axis_radius_edge_eq
    ha haStar hStarb' SLow SAx hLowC1' hLowJet' HT
    hCornerR hEdgeLam
  have hga : 0 < g a := by
    rw [(hOldEdge a ⟨le_rfl, haStar.le⟩).1]
    exact hc.trans_le (hfloor a ⟨le_rfl, haStar.le⟩)
  have hRAx : ∀ p ∈ closedCoordTriangle a b', p.1 < p.2 →
      0 < SAx.r p.1 p.2 :=
    fun p hp hOff => routeB_axis_radius_pos_closed_off_axis HT hp hOff
  have hLamAx : ∀ p ∈ closedCoordTriangle a b',
      0 < SAx.lam p.1 p.2 := HT.lam_pos
  have hNuAx : ∀ p ∈ closedCoordTriangle a b', p.1 < p.2 →
      SAx.nu p.1 p.2 < 0 := by
    intro p hp _
    have h := (hBox p hp).2.1
    linarith only [h, hga]
  have hGapAx : ∀ p ∈ closedCoordTriangle a b', p.1 < p.2 →
      0 < 1 - 2 * SAx.m p.1 p.2 / SAx.r p.1 p.2 := by
    intro p hp _
    have h := (hBox p hp).2.2
    linarith only [h]
  obtain ⟨hLowAx, hLowAxJet⟩ := routeB_vertical_seam
    ha haStar hStarb' SLow SAx hLowC1' hAxC1
    hLowJet' (routeB_axis_classicalJetOn ha.le hab' HT)
    (fun p hp => (hLowSigns' p hp).1)
    hLowLam'
    (fun p hp => (hLowSigns' p hp).2.1)
    (fun p hp => (hLowSigns' p hp).2.2)
    hRAx hLamAx hNuAx hGapAx
    hEdgeLam hEdgeQuot hEdgeRadius hCornerValues hCornerJets
  obtain ⟨hAxAxis, _, hAxSigns⟩ := routeB_axis_values_signs HT
  obtain ⟨T, hTC1, hTData, _, _, _⟩ :=
    exists_routeB_clipped_three_region_isC1Solution
      ha haStar hStarb' alpha₀ SOld SLow SAx
      hOldC1 hLowC1' hAxC1 hOldLow hOldAx hLowAx
      hOldLowJet hOldAxJet hLowAxJet
      hOldJet hLowJet' (routeB_axis_classicalJetOn ha.le hab' HT)
      hOldAxis hAxAxis hOldLam hLowLam' hLamAx
      hOldSigns
      (fun p hp _ => hLowSigns' p hp)
      hAxSigns hOldData hLowData'
  exact ⟨b', hStarb', T, hTC1, hTData⟩

end ChristodoulouBV.Uniqueness

end
