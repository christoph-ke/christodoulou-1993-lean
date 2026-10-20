module

public import ChristodoulouBV.Uniqueness.RouteBGluingClippedFields
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Closing the old/axis seam at the terminal corner

Equality of values and full relative jets on the open vertical seam extends
to both endpoints by C¹ continuity on the two closed regions.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- If item 4 identifies the old and axis fields and their full relative
jets for `a < v < vStar`, the equality also holds at the axis and terminal
endpoints. The terminal endpoint is the triple corner of the corrected cover. -/
theorem routeB_clipped_old_axis_seam_of_open
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar) (hStarb : vStar < b)
    (SOld SAx : Fields)
    (hOldC1 : RouteBFieldsC1On SOld (routeBOldRegion a vStar))
    (hAxC1 : RouteBFieldsC1On SAx (closedCoordTriangle a b))
    (hValues : ∀ c : RouteBField, ∀ v ∈ Ioo a vStar,
      routeBField SOld c (a, v) = routeBField SAx c (a, v))
    (hJets : ∀ c : RouteBField, ∀ v ∈ Ioo a vStar,
      fderivWithin ℝ (routeBField SOld c) (routeBOldRegion a vStar) (a, v) =
        fderivWithin ℝ (routeBField SAx c) (closedCoordTriangle a b) (a, v)) :
    RouteBFieldsEqOn SOld SAx
        (routeBOldRegion a vStar ∩ closedCoordTriangle a b) ∧
      RouteBFieldsJetEqOn SOld SAx
        (routeBOldRegion a vStar) (closedCoordTriangle a b) := by
  let U : Set (ℝ × ℝ) := {a} ×ˢ Ioo a vStar
  let E : Set (ℝ × ℝ) := routeBOldRegion a vStar ∩ closedCoordTriangle a b
  have hE : E = {a} ×ˢ Icc a vStar := by
    change routeBOldRegion a vStar ∩ closedCoordTriangle a b =
      {a} ×ˢ Icc a vStar
    rw [routeB_clipped_old_inter_axis ha.le haStar.le hStarb.le]
    ext p
    simp only [mem_ofPred_eq, mem_prod, mem_singleton_iff]
  have hUE : U ⊆ E := by
    rw [hE]
    intro p hp
    exact ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
  have hEU : E ⊆ closure U := by
    rw [hE]
    change {a} ×ˢ Icc a vStar ⊆ closure ({a} ×ˢ Ioo a vStar)
    rw [closure_prod_eq, closure_singleton, closure_Ioo haStar.ne]
  have hOldSub : E ⊆ routeBOldRegion a vStar := inter_subset_left
  have hAxSub : E ⊆ closedCoordTriangle a b := inter_subset_right
  have hOldUnique : UniqueDiffOn ℝ (routeBOldRegion a vStar) :=
    uniqueDiffOn_convex (routeBOldRegion_closed_convex a vStar).2
      (routeBOldRegion_interior_nonempty ha haStar)
  have hAxUnique : UniqueDiffOn ℝ (closedCoordTriangle a b) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b) (by
      rw [interior_closedCoordTriangle]
      exact openCoordTriangle_nonempty (haStar.trans hStarb))
  constructor
  · intro c
    have hU : EqOn (routeBField SOld c) (routeBField SAx c) U := by
      intro p hp
      have hp' : p = (a, p.2) := Prod.ext hp.1 rfl
      rw [hp']
      exact hValues c p.2 hp.2
    exact hU.of_subset_closure
      ((hOldC1 c).continuousOn.mono hOldSub)
      ((hAxC1 c).continuousOn.mono hAxSub) hUE hEU
  · intro c
    have hU : EqOn
        (fderivWithin ℝ (routeBField SOld c) (routeBOldRegion a vStar))
        (fderivWithin ℝ (routeBField SAx c) (closedCoordTriangle a b)) U := by
      intro p hp
      have hp' : p = (a, p.2) := Prod.ext hp.1 rfl
      rw [hp']
      exact hJets c p.2 hp.2
    exact hU.of_subset_closure
      (((hOldC1 c).continuousOn_fderivWithin hOldUnique (by norm_num)).mono hOldSub)
      (((hAxC1 c).continuousOn_fderivWithin hAxUnique (by norm_num)).mono hAxSub)
      hUE hEU

end ChristodoulouBV.Uniqueness

end
