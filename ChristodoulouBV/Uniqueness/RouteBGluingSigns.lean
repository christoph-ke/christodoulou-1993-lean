module

public import ChristodoulouBV.Uniqueness.RouteBGluingFields
public import ChristodoulouBV.Frozen.DevelopmentWithInitialEdge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Sign transfer across the Route B cover

Pointwise field agreement transfers the classical bridge's sign conditions
from the three input regions to the enlarged development.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A glued state inherits `λ > 0` on the closed triangle and the radius,
incoming, and mass-gap signs on the open development. Each input sign is
required only where its own closed region meets the relevant carrier. -/
theorem routeB_signs_of_fields_eqOn
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar) (hStarb : vStar < b)
    (SOld SLow SAx T : Fields)
    (hOld : RouteBFieldsEqOn T SOld (closedCoordTriangle 0 vStar))
    (hLow : RouteBFieldsEqOn T SLow (routeBLowerRegion a vStar b))
    (hAx : RouteBFieldsEqOn T SAx (closedCoordTriangle a b))
    (hOldLam : ∀ p ∈ closedCoordTriangle 0 vStar,
      0 < SOld.lam p.1 p.2)
    (hLowLam : ∀ p ∈ routeBLowerRegion a vStar b,
      0 < SLow.lam p.1 p.2)
    (hAxLam : ∀ p ∈ closedCoordTriangle a b,
      0 < SAx.lam p.1 p.2)
    (hOldSigns : ∀ p ∈ closedCoordTriangle 0 vStar,
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
        0 < 1 - 2 * SAx.m p.1 p.2 / SAx.r p.1 p.2) :
    (∀ p ∈ closedCoordTriangle 0 b, 0 < T.lam p.1 p.2) ∧
      (∀ p ∈ developmentWithInitialEdge b,
        0 < T.r p.1 p.2 ∧ T.nu p.1 p.2 < 0 ∧
          0 < 1 - 2 * T.m p.1 p.2 / T.r p.1 p.2) := by
  have htransfer (S : Fields) (K : Set (ℝ × ℝ))
      (hEq : RouteBFieldsEqOn T S K)
      (hLam : ∀ p ∈ K, 0 < S.lam p.1 p.2)
      (hSigns : ∀ p ∈ K, p ∈ developmentWithInitialEdge b →
        0 < S.r p.1 p.2 ∧ S.nu p.1 p.2 < 0 ∧
          0 < 1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) :
      (∀ p ∈ K, 0 < T.lam p.1 p.2) ∧
        (∀ p ∈ K, p ∈ developmentWithInitialEdge b →
          0 < T.r p.1 p.2 ∧ T.nu p.1 p.2 < 0 ∧
            0 < 1 - 2 * T.m p.1 p.2 / T.r p.1 p.2) := by
    constructor
    · intro p hp
      have h := hEq .expansion hp
      change T.lam p.1 p.2 = S.lam p.1 p.2 at h
      exact h ▸ hLam p hp
    · intro p hp hpU
      have hr := hEq .radius hp
      have hm := hEq .mass hp
      have hnu := hEq .contraction hp
      change T.r p.1 p.2 = S.r p.1 p.2 at hr
      change T.m p.1 p.2 = S.m p.1 p.2 at hm
      change T.nu p.1 p.2 = S.nu p.1 p.2 at hnu
      rw [hr, hm, hnu]
      exact hSigns p hp hpU
  have hO := htransfer SOld _ hOld hOldLam hOldSigns
  have hL := htransfer SLow _ hLow hLowLam hLowSigns
  have hA := htransfer SAx _ hAx hAxLam hAxSigns
  have hcover := routeB_three_region_cover ha.le haStar.le hStarb.le
  have hpiece (p : ℝ × ℝ) (hp : p ∈ closedCoordTriangle 0 b) :
      p ∈ closedCoordTriangle 0 vStar ∨
        p ∈ routeBLowerRegion a vStar b ∨
          p ∈ closedCoordTriangle a b := by
    have h := hcover.symm ▸ hp
    rcases h with (hOld | hLow) | hAx
    · exact Or.inl hOld
    · exact Or.inr (Or.inl hLow)
    · exact Or.inr (Or.inr hAx)
  constructor
  · intro p hp
    rcases hpiece p hp with hpOld | hpLow | hpAx
    · exact hO.1 p hpOld
    · exact hL.1 p hpLow
    · exact hA.1 p hpAx
  · intro p hp
    have hpK : p ∈ closedCoordTriangle 0 b :=
      ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
    rcases hpiece p hpK with hpOld | hpLow | hpAx
    · exact hO.2 p hpOld hp
    · exact hL.2 p hpLow hp
    · exact hA.2 p hpAx hp

end ChristodoulouBV.Uniqueness

end
