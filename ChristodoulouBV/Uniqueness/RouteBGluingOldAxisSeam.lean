module

public import ChristodoulouBV.Uniqueness.RouteBGluingOldMatch
public import ChristodoulouBV.Uniqueness.RouteBGluingIdentificationSeam

/-!
# The closed old/axis seam

The constructed closed old representative satisfies the finite matching
condition of the established item-4 identification theorem. Hence the values and
full relative first jets agree with the axis solution on their entire
vertical overlap, including the terminal triple corner.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Construct the closed old C¹ piece and discharge its value and full-jet
seam with the identified axis solution. -/
theorem OffAxisTerminalC1Packet.exists_routeB_closed_old_with_axis_seam
    {alpha₀ : ℝ → ℝ} {a vBar vStar b : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (J : RouteBTerminalBaseJets P)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ d ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge d) (S d) ∧
      (∀ v ∈ Ioo (0 : ℝ) d,
        (S d).r 0 v = v / 2 ∧ (S d).alpha 0 v = alpha₀ v))
    {SAx : Fields}
    (HT : C1Solution.AxisClassicalSolution a b SAx) (hStarb : vStar < b)
    (hrT : ∀ v ∈ Icc a vStar, SAx.r a v = P.rEdge v)
    (hpsiT : ∀ v ∈ Icc a vStar,
      SAx.r a v * SAx.phi a v = ∫ s in a..v, P.g s * P.hEdge s)
    (hAxC1 : RouteBFieldsC1On SAx (closedCoordTriangle a b)) :
    ∃ SOld : Fields,
      RouteBFieldsC1On SOld (routeBOldRegion a vStar) ∧
      RouteBFieldsEqOn SOld P.terminalFields
        (routeBLowerRegion a vBar vStar) ∧
      RouteBFieldsEqOn SOld SAx
        (routeBOldRegion a vStar ∩ closedCoordTriangle a b) ∧
      RouteBFieldsJetEqOn SOld SAx
        (routeBOldRegion a vStar) (closedCoordTriangle a b) := by
  obtain ⟨SOld, hOldC1, hOldMatch, hTop⟩ :=
    P.exists_routeB_closed_old_fields_with_match J ha haBar hBarStar hfamily
  have hSeam := P.clipped_old_axis_seam ha (haBar.trans hBarStar)
    hfamily HT hStarb hrT hpsiT hOldC1 hAxC1 hOldMatch
  exact ⟨SOld, hOldC1, hTop, hSeam.1, hSeam.2⟩

end ChristodoulouBV.Uniqueness

end
