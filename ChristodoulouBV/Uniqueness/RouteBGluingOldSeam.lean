module

public import ChristodoulouBV.Uniqueness.RouteBGluingOldTwoPiece
public import ChristodoulouBV.Uniqueness.RouteBGluingJetTransfer
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# The internal old horizontal seam

A finite old member exists above the seam. Both the lower clipped triangle
and a short upper rectangle are restrictions of that same C¹ member, so their
full relative jets agree on the seam.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Equality with one C¹ finite-cutoff representative on both sides of the
horizontal seam transfers its full first jet, including both endpoints. -/
theorem routeB_old_scalar_terminal_seam_of_common
    {a vBar e vStar : ℝ} (ha : 0 < a) (haBar : a < vBar)
    (hBarE : vBar < e) (heStar : e < vStar)
    (fBottom fTop F : ℝ × ℝ → ℝ)
    (hFC1 : ContDiffOn ℝ 1 F (closedCoordTriangle 0 e))
    (hTopC1 : ContDiffOn ℝ 1 fTop (routeBLowerRegion a vBar vStar))
    (hBottomF : EqOn fBottom F (routeBOldRegion a vBar))
    (hTopF : EqOn fTop F (routeBLowerRegion a vBar e)) :
    EqOn fBottom fTop
        (routeBOldRegion a vBar ∩ routeBLowerRegion a vBar vStar) ∧
      EqOn (fderivWithin ℝ fBottom (routeBOldRegion a vBar))
        (fderivWithin ℝ fTop (routeBLowerRegion a vBar vStar))
        (routeBOldRegion a vBar ∩ routeBLowerRegion a vBar vStar) := by
  let KB := routeBOldRegion a vBar
  let KT := routeBLowerRegion a vBar vStar
  let KS := routeBLowerRegion a vBar e
  let KF := closedCoordTriangle 0 e
  have hBsub : KB ⊆ KF := by
    intro p hp
    exact ⟨hp.1.1, hp.1.2.1, hp.1.2.2.trans hBarE.le⟩
  have hSsubF : KS ⊆ KF := by
    intro p hp
    exact ⟨hp.1.1, hp.1.2.trans (haBar.le.trans hp.2.1), hp.2.2⟩
  have hSsubT : KS ⊆ KT := by
    intro p hp
    exact ⟨hp.1, ⟨hp.2.1, hp.2.2.trans heStar.le⟩⟩
  have hBUnique : UniqueDiffOn ℝ KB :=
    uniqueDiffOn_convex (routeBOldRegion_closed_convex a vBar).2
      (routeBOldRegion_interior_nonempty ha haBar)
  have hSUnique : UniqueDiffOn ℝ KS :=
    uniqueDiffOn_convex (routeBLowerRegion_closed_convex a vBar e).2
      (routeBLowerRegion_interior_nonempty ha hBarE)
  constructor
  · intro p hp
    have hpS : p ∈ KS := by
      have hseam := hp
      rw [routeB_clipped_old_inter_lower haBar.le
        (hBarE.trans heStar).le] at hseam
      obtain ⟨hu, hv⟩ := hseam
      exact ⟨hu, ⟨hv ▸ le_rfl, hv ▸ hBarE.le⟩⟩
    exact (hBottomF hp.1).trans (hTopF hpS).symm
  · intro p hp
    have hpS : p ∈ KS := by
      have hseam := hp
      rw [routeB_clipped_old_inter_lower haBar.le
        (hBarE.trans heStar).le] at hseam
      obtain ⟨hu, hv⟩ := hseam
      exact ⟨hu, ⟨hv ▸ le_rfl, hv ▸ hBarE.le⟩⟩
    have hFB := fderivWithin_eq_of_eqOn_subset
      hFC1 hBsub hBUnique (fun q hq => (hBottomF hq).symm) hp.1
    have hFS := fderivWithin_eq_of_eqOn_subset
      hFC1 hSsubF hSUnique (fun _ _ => rfl) hpS
    have hTS := fderivWithin_eq_of_eqOn_subset
      hTopC1 hSsubT hSUnique hTopF hpS
    exact hFB.symm.trans (hFS.trans hTS.symm)

end ChristodoulouBV.Uniqueness

end
