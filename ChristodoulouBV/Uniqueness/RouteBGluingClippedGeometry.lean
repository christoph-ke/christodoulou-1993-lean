module

public import ChristodoulouBV.Uniqueness.RouteBGluingGeometry
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Corrected Route B closed cover

The old piece stops at `u = a`. The part of the old terminal triangle with
`u ≥ a` belongs to the new axis triangle, including its terminal corner.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The closed part of the old triangle needed in the Route B patch. -/
@[expose] def routeBOldRegion (a vStar : ℝ) : Set (ℝ × ℝ) :=
  closedCoordTriangle 0 vStar ∩ {p | p.1 ≤ a}

/-- Membership in the clipped old region. -/
theorem mem_routeBOldRegion {a vStar : ℝ} {p : ℝ × ℝ} :
    p ∈ routeBOldRegion a vStar ↔
      0 ≤ p.1 ∧ p.1 ≤ a ∧ p.1 ≤ p.2 ∧ p.2 ≤ vStar := by
  simp only [routeBOldRegion, mem_inter_iff, mem_ofPred_eq, closedCoordTriangle]
  tauto

/-- The corrected three regions cover the enlarged closed triangle. -/
theorem routeB_clipped_three_region_cover
    {a vStar b : ℝ} (ha : 0 ≤ a) (haStar : a ≤ vStar)
    (hStarb : vStar ≤ b) :
    routeBOldRegion a vStar ∪ routeBLowerRegion a vStar b ∪
      closedCoordTriangle a b = closedCoordTriangle 0 b := by
  ext p
  constructor
  · rintro ((hOld | hLow) | hAx)
    · exact ⟨hOld.1.1, hOld.1.2.1, hOld.1.2.2.trans hStarb⟩
    · exact ⟨hLow.1.1, hLow.1.2.trans (haStar.trans hLow.2.1), hLow.2.2⟩
    · exact ⟨ha.trans hAx.1, hAx.2.1, hAx.2.2⟩
  · intro hp
    by_cases hu : p.1 ≤ a
    · by_cases hv : p.2 ≤ vStar
      · exact Or.inl (Or.inl ⟨⟨hp.1, hp.2.1, hv⟩, hu⟩)
      · exact Or.inl (Or.inr ⟨⟨hp.1, hu⟩, ⟨le_of_not_ge hv, hp.2.2⟩⟩)
    · exact Or.inr ⟨le_of_not_ge hu, hp.2.1, hp.2.2⟩

/-- The clipped old/lower intersection is the lower horizontal seam. -/
theorem routeB_clipped_old_inter_lower
    {a vStar b : ℝ} (haStar : a ≤ vStar) (hStarb : vStar ≤ b) :
    routeBOldRegion a vStar ∩ routeBLowerRegion a vStar b =
      {p : ℝ × ℝ | p.1 ∈ Icc 0 a ∧ p.2 = vStar} := by
  ext p
  constructor
  · rintro ⟨hOld, hLow⟩
    exact ⟨⟨hOld.1.1, hOld.2⟩, le_antisymm hOld.1.2.2 hLow.2.1⟩
  · rintro ⟨hu, rfl⟩
    exact ⟨⟨⟨hu.1, hu.2.trans haStar, le_rfl⟩, hu.2⟩,
      ⟨hu, ⟨le_rfl, hStarb⟩⟩⟩

/-- The clipped old/axis intersection is the vertical seam below `vStar`. -/
theorem routeB_clipped_old_inter_axis
    {a vStar b : ℝ} (ha : 0 ≤ a) (haStar : a ≤ vStar)
    (hStarb : vStar ≤ b) :
    routeBOldRegion a vStar ∩ closedCoordTriangle a b =
      {p : ℝ × ℝ | p.1 = a ∧ p.2 ∈ Icc a vStar} := by
  ext p
  constructor
  · rintro ⟨hOld, hAx⟩
    have hu : p.1 = a := le_antisymm hOld.2 hAx.1
    exact ⟨hu, ⟨hu ▸ hOld.1.2.1, hOld.1.2.2⟩⟩
  · rintro ⟨rfl, hv⟩
    exact ⟨mem_routeBOldRegion.mpr ⟨ha, le_rfl, hv.1, hv.2⟩,
      ⟨le_rfl, hv.1, hv.2.trans hStarb⟩⟩

/-- All corrected pieces meet only at `(a,vStar)`. -/
theorem routeB_clipped_triple_corner
    {a vStar b : ℝ} (ha : 0 ≤ a) (haStar : a ≤ vStar)
    (hStarb : vStar ≤ b) :
    (routeBOldRegion a vStar ∩ routeBLowerRegion a vStar b) ∩
      closedCoordTriangle a b = {(a, vStar)} := by
  rw [routeB_clipped_old_inter_lower haStar hStarb]
  ext p
  constructor
  · rintro ⟨⟨hu, hv⟩, hAx⟩
    have hp : p = (a, vStar) :=
      Prod.ext (le_antisymm hu.2 hAx.1) hv
    simp [hp]
  · intro hp
    have hp' : p = (a, vStar) := by simpa using hp
    subst p
    exact ⟨⟨⟨ha, le_rfl⟩, rfl⟩, ⟨le_rfl, haStar, hStarb⟩⟩

/-- The clipped old region is closed and convex. -/
theorem routeBOldRegion_closed_convex (a vStar : ℝ) :
    IsClosed (routeBOldRegion a vStar) ∧
      Convex ℝ (routeBOldRegion a vStar) := by
  constructor
  · exact (isClosed_closedCoordTriangle 0 vStar).inter
      (isClosed_le continuous_fst continuous_const)
  · intro p hp q hq s t hs ht hst
    refine ⟨(convex_closedCoordTriangle 0 vStar) hp.1 hq.1 hs ht hst, ?_⟩
    change (s • p + t • q).1 ≤ a
    change s * p.1 + t * q.1 ≤ a
    calc
      s * p.1 + t * q.1 ≤ s * a + t * a :=
        add_le_add (mul_le_mul_of_nonneg_left hp.2 hs)
          (mul_le_mul_of_nonneg_left hq.2 ht)
      _ = a := by rw [← add_mul, hst, one_mul]

/-- The clipped old region has a two-dimensional interior. -/
theorem routeBOldRegion_interior_nonempty
    {a vStar : ℝ} (ha : 0 < a) (haStar : a < vStar) :
    (interior (routeBOldRegion a vStar)).Nonempty := by
  refine ⟨(a / 2, (a + vStar) / 2), ?_⟩
  let U := openCoordTriangle 0 vStar ∩ {p : ℝ × ℝ | p.1 < a}
  have hUopen : IsOpen U := by
    have hTriOpen : IsOpen (openCoordTriangle 0 vStar) := by
      rw [← interior_closedCoordTriangle]
      exact isOpen_interior
    exact hTriOpen.inter (isOpen_lt continuous_fst continuous_const)
  have hUmem : (a / 2, (a + vStar) / 2) ∈ U := by
    refine ⟨?_, ?_⟩
    · exact ⟨by linarith, by linarith, by linarith⟩
    · dsimp; linarith
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset (hUopen.mem_nhds hUmem) (by
    intro p hp
    exact mem_routeBOldRegion.mpr
      ⟨hp.1.1.le, hp.2.le, hp.1.2.1.le, hp.1.2.2.le⟩)

end ChristodoulouBV.Uniqueness

end
