module

public import ChristodoulouBV.Uniqueness.RouteBAssemblyShortLower
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# The Route B triple-corner values and jets

The old/lower and old/axis seams identify all seven values and full first
jets of the lower and axis pieces at their common corner.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Two closed seams through `(a,vStar)` give the exact corner value and
jet hypotheses required by the lower/axis vertical seam theorem. -/
theorem routeB_triple_corner_values_and_jets
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (hStarb : vStar < b) (SOld SLow SAx : Fields)
    (hOldLow : RouteBFieldsEqOn SOld SLow
      (routeBOldRegion a vStar ∩ routeBLowerRegion a vStar b))
    (hOldAx : RouteBFieldsEqOn SOld SAx
      (routeBOldRegion a vStar ∩ closedCoordTriangle a b))
    (hOldLowJet : RouteBFieldsJetEqOn SOld SLow
      (routeBOldRegion a vStar) (routeBLowerRegion a vStar b))
    (hOldAxJet : RouteBFieldsJetEqOn SOld SAx
      (routeBOldRegion a vStar) (closedCoordTriangle a b)) :
    (∀ q : RouteBField,
      routeBField SLow q (a, vStar) =
        routeBField SAx q (a, vStar)) ∧
    (∀ q : RouteBField,
      fderivWithin ℝ (routeBField SLow q)
        (routeBLowerRegion a vStar b) (a, vStar) =
      fderivWithin ℝ (routeBField SAx q)
        (closedCoordTriangle a b) (a, vStar)) := by
  have hpOld : (a, vStar) ∈ routeBOldRegion a vStar :=
    mem_routeBOldRegion.mpr ⟨ha.le, le_rfl, haStar.le, le_rfl⟩
  have hpLow : (a, vStar) ∈ routeBLowerRegion a vStar b :=
    ⟨⟨ha.le, le_rfl⟩, ⟨le_rfl, hStarb.le⟩⟩
  have hpAx : (a, vStar) ∈ closedCoordTriangle a b := by
    change a ≤ a ∧ a ≤ vStar ∧ vStar ≤ b
    exact ⟨le_rfl, haStar.le, hStarb.le⟩
  constructor
  · intro q
    exact (hOldLow q ⟨hpOld, hpLow⟩).symm.trans
      (hOldAx q ⟨hpOld, hpAx⟩)
  · intro q
    exact (hOldLowJet q ⟨hpOld, hpLow⟩).symm.trans
      (hOldAxJet q ⟨hpOld, hpAx⟩)

end ChristodoulouBV.Uniqueness

end
