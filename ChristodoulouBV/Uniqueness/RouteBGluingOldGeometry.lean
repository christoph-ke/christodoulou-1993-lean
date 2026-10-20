module

public import ChristodoulouBV.Uniqueness.RouteBGluingClippedGeometry
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Two closed regions of the old Route B piece

The lower finite-cutoff triangle and the off-axis terminal rectangle meet
on a horizontal segment and cover exactly the clipped old region.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The finite old triangle and the terminal rectangle cover the closed
clipped old region. -/
theorem routeB_old_triangle_terminal_cover
    {a vBar vStar : ℝ} (_ha : 0 ≤ a) (haBar : a ≤ vBar)
    (hBarStar : vBar ≤ vStar) :
    routeBOldRegion a vBar ∪ routeBLowerRegion a vBar vStar =
      routeBOldRegion a vStar := by
  ext p
  constructor
  · rintro (hTri | hRect)
    · obtain ⟨hu0, hua, huv, hvBar⟩ := mem_routeBOldRegion.mp hTri
      exact mem_routeBOldRegion.mpr
        ⟨hu0, hua, huv, hvBar.trans hBarStar⟩
    · exact mem_routeBOldRegion.mpr
        ⟨hRect.1.1, hRect.1.2,
          hRect.1.2.trans (haBar.trans hRect.2.1), hRect.2.2⟩
  · intro hp
    obtain ⟨hu0, hua, huv, hvStar⟩ := mem_routeBOldRegion.mp hp
    by_cases hv : p.2 ≤ vBar
    · exact Or.inl (mem_routeBOldRegion.mpr ⟨hu0, hua, huv, hv⟩)
    · exact Or.inr ⟨⟨hu0, hua⟩, ⟨le_of_not_ge hv, hvStar⟩⟩

end ChristodoulouBV.Uniqueness

end
