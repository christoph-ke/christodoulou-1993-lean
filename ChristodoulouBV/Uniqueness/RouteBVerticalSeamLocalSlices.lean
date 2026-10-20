module

public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamLocalODE
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Safe local rectangles at the vertical seam

Every strict point of the shared characteristic has one closed rectangle
inside the lower band and one inside the axis triangle. Both rectangles
remain in the open development and stay away from the axis and top edge.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A nondegenerate closed coordinate rectangle has unique relative jets. -/
theorem routeB_uniqueDiffOn_closed_rectangle
    {u₀ u₁ v₀ v₁ : ℝ} (hu : u₀ < u₁) (hv : v₀ < v₁) :
    UniqueDiffOn ℝ (Icc u₀ u₁ ×ˢ Icc v₀ v₁) := by
  apply uniqueDiffOn_convex ((convex_Icc u₀ u₁).prod (convex_Icc v₀ v₁))
  rw [interior_prod_eq, interior_Icc, interior_Icc]
  exact ⟨((u₀ + u₁) / 2, (v₀ + v₁) / 2),
    ⟨by constructor <;> linarith, by constructor <;> linarith⟩⟩

/-- The lower-side local rectangle at a strict point of the vertical seam. -/
theorem routeB_lower_local_rectangle_at_vertical_seam
    {a vStar b v : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (hv : v ∈ Ioo vStar b) :
    let u₀ := a / 2
    let v₀ := (vStar + v) / 2
    let v₁ := (v + b) / 2
    u₀ < a ∧ v₀ < v ∧ v < v₁ ∧ a ∈ Icc u₀ a ∧
      Icc u₀ a ×ˢ Icc v₀ v₁ ⊆ routeBLowerRegion a vStar b ∧
      (∀ p ∈ Icc u₀ a ×ˢ Icc v₀ v₁,
        p ∈ developmentWithInitialEdge b) := by
  dsimp only
  have hu₀ : 0 < a / 2 := by linarith only [ha]
  have hvStar₀ : vStar < (vStar + v) / 2 := by
    linarith only [hv.1]
  have hv₀ : (vStar + v) / 2 < v := by
    linarith only [hv.1]
  have hv₁ : v < (v + b) / 2 := by
    linarith only [hv.2]
  have hv₁b : (v + b) / 2 < b := by
    linarith only [hv.2]
  refine ⟨by linarith only [ha], hv₀, hv₁,
    ⟨by linarith only [ha], le_rfl⟩, ?_, ?_⟩
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨⟨hu₀.le.trans hx.1, hx.2⟩,
      ⟨hvStar₀.le.trans hy.1, hy.2.trans hv₁b.le⟩⟩
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨hu₀.le.trans hx.1,
      hx.2.trans_lt (haStar.trans (hvStar₀.trans_le hy.1)),
      hy.2.trans_lt hv₁b⟩

/-- The axis-side local rectangle at a strict point of the vertical seam. -/
theorem routeB_axis_local_rectangle_at_vertical_seam
    {a vStar b v : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (hv : v ∈ Ioo vStar b) :
    let u₁ := (a + vStar) / 2
    let v₀ := (vStar + v) / 2
    let v₁ := (v + b) / 2
    a < u₁ ∧ v₀ < v ∧ v < v₁ ∧ a ∈ Icc a u₁ ∧
      Icc a u₁ ×ˢ Icc v₀ v₁ ⊆ closedCoordTriangle a b ∧
      (∀ p ∈ Icc a u₁ ×ˢ Icc v₀ v₁,
        p ∈ developmentWithInitialEdge b) := by
  dsimp only
  have hu₁ : (a + vStar) / 2 < vStar := by
    linarith only [haStar]
  have hvStar₀ : vStar < (vStar + v) / 2 := by
    linarith only [hv.1]
  have hv₀ : (vStar + v) / 2 < v := by
    linarith only [hv.1]
  have hv₁ : v < (v + b) / 2 := by
    linarith only [hv.2]
  have hv₁b : (v + b) / 2 < b := by
    linarith only [hv.2]
  refine ⟨by linarith only [haStar], hv₀, hv₁,
    ⟨le_rfl, by linarith only [haStar]⟩, ?_, ?_⟩
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    change a ≤ x ∧ x ≤ y ∧ y ≤ b
    exact ⟨hx.1,
      (hx.2.trans_lt hu₁).le.trans (hvStar₀.le.trans hy.1),
      hy.2.trans hv₁b.le⟩
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨ha.le.trans hx.1,
      (hx.2.trans_lt hu₁).trans_le (hvStar₀.le.trans hy.1),
      hy.2.trans_lt hv₁b⟩

end ChristodoulouBV.Uniqueness

end
