module

public import ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Geometry of the three Route B regions

The lower band is a closed rectangle. Together with the old and translated
axis triangles it covers the enlarged closed coordinate triangle.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The closed lower band between the old terminal line and the new endpoint. -/
@[expose] def routeBLowerRegion (a vStar b : ℝ) : Set (ℝ × ℝ) :=
  Icc 0 a ×ˢ Icc vStar b

/-- The lower band is the rectangle specified inside the large triangle. -/
theorem routeBLowerRegion_eq_rectangle_inter_triangle
    {a vStar b : ℝ} (haStar : a ≤ vStar) :
    routeBLowerRegion a vStar b =
      (Icc 0 a ×ˢ Icc vStar b) ∩ closedCoordTriangle 0 b := by
  ext p
  constructor
  · intro hp
    refine ⟨hp, ?_⟩
    exact ⟨hp.1.1, hp.1.2.trans (haStar.trans hp.2.1), hp.2.2⟩
  · exact fun hp => hp.1

/-- The three closed pieces cover exactly the enlarged triangle. -/
theorem routeB_three_region_cover
    {a vStar b : ℝ} (ha : 0 ≤ a) (haStar : a ≤ vStar)
    (hStarb : vStar ≤ b) :
    closedCoordTriangle 0 vStar ∪ routeBLowerRegion a vStar b ∪
      closedCoordTriangle a b = closedCoordTriangle 0 b := by
  ext p
  constructor
  · intro hp
    rcases hp with (hOld | hLow) | hAx
    · exact ⟨hOld.1, hOld.2.1, hOld.2.2.trans hStarb⟩
    · exact ⟨hLow.1.1, hLow.1.2.trans (haStar.trans hLow.2.1), hLow.2.2⟩
    · exact ⟨ha.trans hAx.1, hAx.2.1, hAx.2.2⟩
  · intro hp
    by_cases hv : p.2 ≤ vStar
    · exact Or.inl (Or.inl ⟨hp.1, hp.2.1, hv⟩)
    · by_cases hu : p.1 ≤ a
      · exact Or.inl (Or.inr ⟨⟨hp.1, hu⟩, ⟨le_of_not_ge hv, hp.2.2⟩⟩)
      · exact Or.inr ⟨le_of_not_ge hu, hp.2.1, hp.2.2⟩

/-- The old/lower intersection is the horizontal terminal segment. -/
theorem routeB_old_inter_lower
    {a vStar b : ℝ} (haStar : a ≤ vStar) (hStarb : vStar ≤ b) :
    closedCoordTriangle 0 vStar ∩ routeBLowerRegion a vStar b =
      {p : ℝ × ℝ | p.1 ∈ Icc 0 a ∧ p.2 = vStar} := by
  ext p
  constructor
  · rintro ⟨hOld, hLow⟩
    exact ⟨hLow.1, le_antisymm hOld.2.2 hLow.2.1⟩
  · rintro ⟨hu, rfl⟩
    exact ⟨⟨hu.1, hu.2.trans haStar, le_rfl⟩,
      ⟨hu, ⟨le_rfl, hStarb⟩⟩⟩

/-- The old/axis intersection is the smaller closed axis triangle. -/
theorem routeB_old_inter_axis
    {a vStar b : ℝ} (ha : 0 ≤ a) (hStarb : vStar ≤ b) :
    closedCoordTriangle 0 vStar ∩ closedCoordTriangle a b =
      closedCoordTriangle a vStar := by
  ext p
  constructor
  · rintro ⟨hOld, hAx⟩
    exact ⟨hAx.1, hAx.2.1, hOld.2.2⟩
  · intro hp
    exact ⟨⟨ha.trans hp.1, hp.2.1, hp.2.2⟩,
      ⟨hp.1, hp.2.1, hp.2.2.trans hStarb⟩⟩

/-- The lower/axis intersection is the vertical characteristic segment. -/
theorem routeB_lower_inter_axis
    {a vStar b : ℝ} (ha : 0 ≤ a) (haStar : a ≤ vStar) :
    routeBLowerRegion a vStar b ∩ closedCoordTriangle a b =
      {p : ℝ × ℝ | p.1 = a ∧ p.2 ∈ Icc vStar b} := by
  ext p
  constructor
  · rintro ⟨hLow, hAx⟩
    exact ⟨le_antisymm hLow.1.2 hAx.1, hLow.2⟩
  · rintro ⟨rfl, hv⟩
    exact ⟨⟨⟨ha, le_rfl⟩, hv⟩, ⟨le_rfl, haStar.trans hv.1, hv.2⟩⟩

/-- All three pieces meet at exactly the corner `(a,vStar)`. -/
theorem routeB_triple_corner
    {a vStar b : ℝ} (ha : 0 ≤ a) (haStar : a ≤ vStar)
    (hStarb : vStar ≤ b) :
    (closedCoordTriangle 0 vStar ∩ routeBLowerRegion a vStar b) ∩
      closedCoordTriangle a b = {(a, vStar)} := by
  ext p
  constructor
  · rintro ⟨⟨hOld, hLow⟩, hAx⟩
    change p = (a, vStar)
    exact Prod.ext (le_antisymm hLow.1.2 hAx.1)
      (le_antisymm hOld.2.2 hLow.2.1)
  · intro hp
    have hp' : p = (a, vStar) := by simpa using hp
    subst p
    exact ⟨⟨⟨ha, haStar, le_rfl⟩,
      ⟨⟨ha, le_rfl⟩, ⟨le_rfl, hStarb⟩⟩⟩,
      ⟨le_rfl, haStar, hStarb⟩⟩

/-- The lower band is closed and convex. -/
theorem routeBLowerRegion_closed_convex (a vStar b : ℝ) :
    IsClosed (routeBLowerRegion a vStar b) ∧
      Convex ℝ (routeBLowerRegion a vStar b) := by
  exact ⟨isClosed_Icc.prod isClosed_Icc,
    (convex_Icc 0 a).prod (convex_Icc vStar b)⟩

/-- The lower band has two-dimensional interior when both intervals are nontrivial. -/
theorem routeBLowerRegion_interior_nonempty
    {a vStar b : ℝ} (ha : 0 < a) (hStarb : vStar < b) :
    (interior (routeBLowerRegion a vStar b)).Nonempty := by
  change (interior (Icc 0 a ×ˢ Icc vStar b)).Nonempty
  rw [interior_prod_eq, interior_Icc, interior_Icc]
  refine ⟨(a / 2, (vStar + b) / 2), ?_⟩
  exact ⟨by constructor <;> linarith, by constructor <;> linarith⟩

end ChristodoulouBV.Uniqueness

end
