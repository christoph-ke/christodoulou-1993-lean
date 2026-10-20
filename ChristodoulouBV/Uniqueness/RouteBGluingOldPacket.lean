module

public import ChristodoulouBV.Uniqueness.RouteBGluingOldAxisSeam
public import ChristodoulouBV.Uniqueness.RouteBGluingOldData
public import ChristodoulouBV.Uniqueness.RouteBGluingOldSigns

/-!
# Closed old Route B construction

The canonical finite family and terminal base jets produce a C¹ old piece
with its physical signs, canonical axis, prescribed initial edge and full
value-and-jet match to the axis solution. The classical relative equations
remain a separate obligation.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The non-equation data of the closed old piece for the corrected
three-region Route B gluing theorem. -/
theorem OffAxisTerminalC1Packet.exists_routeB_closed_old_packet
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
      SAx.r a v * SAx.phi a v = ∫ s in a..v, P.g s * P.hEdge s)
    (hAxC1 : RouteBFieldsC1On SAx (closedCoordTriangle a b)) :
    ∃ SOld : Fields,
      RouteBFieldsC1On SOld (routeBOldRegion a vStar) ∧
      (∀ e ∈ Ioo a vStar, ∀ d ∈ Ioo e vStar,
        RouteBFieldsEqOn SOld (routeBCanonicalOldFields d (S d))
          (routeBOldRegion a e)) ∧
      RouteBFieldsEqOn SOld P.terminalFields
        (routeBLowerRegion a vBar vStar) ∧
      (∀ u ∈ Icc (0 : ℝ) a,
        SOld.r u u = 0 ∧ SOld.m u u = 0) ∧
      (∀ v ∈ Icc (0 : ℝ) vStar,
        SOld.r 0 v = v / 2 ∧ SOld.alpha 0 v = alpha₀ v) ∧
      (∀ p ∈ routeBOldRegion a vStar, 0 < SOld.lam p.1 p.2) ∧
      (∀ p ∈ routeBOldRegion a vStar,
        p ∈ developmentWithInitialEdge b →
        0 < SOld.r p.1 p.2 ∧ SOld.nu p.1 p.2 < 0 ∧
          0 < 1 - 2 * SOld.m p.1 p.2 / SOld.r p.1 p.2) ∧
      RouteBFieldsEqOn SOld SAx
        (routeBOldRegion a vStar ∩ closedCoordTriangle a b) ∧
      RouteBFieldsJetEqOn SOld SAx
        (routeBOldRegion a vStar) (closedCoordTriangle a b) := by
  obtain ⟨SOld, hC1, hMatch, hTop⟩ :=
    P.exists_routeB_closed_old_fields_with_match J ha haBar hBarStar hfamily
  have hAxis := routeB_old_axis_of_finite_match ha
    (haBar.trans hBarStar) hMatch
  have hData := routeB_old_initial_data_of_finite_match ha
    (haBar.trans hBarStar) hα hfamily hC1 hMatch
  have hSigns := P.closed_old_signs_of_match ha haBar hBarStar
    hStarb hu₀ hα hfamily hε htail hMatch hTop
  have hSeam := P.clipped_old_axis_seam ha (haBar.trans hBarStar)
    hfamily HT hStarb hrT hpsiT hC1 hAxC1 hMatch
  exact ⟨SOld, hC1, hMatch, hTop, hAxis, hData,
    hSigns.1, hSigns.2, hSeam.1, hSeam.2⟩

end ChristodoulouBV.Uniqueness

end
