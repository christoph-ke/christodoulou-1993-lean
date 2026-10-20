module

public import ChristodoulouBV.Uniqueness.RouteBGluingClippedSeam
public import ChristodoulouBV.Uniqueness.RouteBGluingJetTransfer
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Finite-cutoff transfer of the old/axis full jet

On a strict cutoff below `vStar`, the canonical old member is C¹ across
`u = a`. Equality on both sides transfers its full jet to the two pieces.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A common C¹ finite-cutoff representative identifies both values and
full relative jets of the clipped old and axis pieces at a seam point. -/
theorem routeB_clipped_scalar_seam_at_of_common
    {a c vStar b : ℝ} (ha : 0 < a) (hac : a < c)
    (hcStar : c < vStar) (hStarb : vStar < b)
    (fOld fAx F : ℝ × ℝ → ℝ)
    (hOldC1 : ContDiffOn ℝ 1 fOld (routeBOldRegion a vStar))
    (hAxC1 : ContDiffOn ℝ 1 fAx (closedCoordTriangle a b))
    (hFC1 : ContDiffOn ℝ 1 F (closedCoordTriangle 0 c))
    (hOldF : EqOn fOld F (routeBOldRegion a c))
    (hAxF : EqOn fAx F (closedCoordTriangle a c))
    {v : ℝ} (hv : v ∈ Icc a c) :
    fOld (a, v) = fAx (a, v) ∧
      fderivWithin ℝ fOld (routeBOldRegion a vStar) (a, v) =
        fderivWithin ℝ fAx (closedCoordTriangle a b) (a, v) := by
  let KO := routeBOldRegion a c
  let KA := closedCoordTriangle a c
  let KF := closedCoordTriangle 0 c
  have hpO : (a, v) ∈ KO :=
    mem_routeBOldRegion.mpr ⟨ha.le, le_rfl, hv.1, hv.2⟩
  have hpA : (a, v) ∈ KA := ⟨le_rfl, hv.1, hv.2⟩
  have hOsub : KO ⊆ routeBOldRegion a vStar := by
    intro p hp
    obtain ⟨h0, hu, huv, hvc⟩ := mem_routeBOldRegion.mp hp
    exact mem_routeBOldRegion.mpr ⟨h0, hu, huv, hvc.trans hcStar.le⟩
  have hAsub : KA ⊆ closedCoordTriangle a b := by
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.trans (hcStar.trans hStarb).le⟩
  have hOFsub : KO ⊆ KF := by
    intro p hp
    exact hp.1
  have hAFsub : KA ⊆ KF := by
    intro p hp
    exact ⟨ha.le.trans hp.1, hp.2.1, hp.2.2⟩
  have hOunique : UniqueDiffOn ℝ KO :=
    uniqueDiffOn_convex (routeBOldRegion_closed_convex a c).2
      (routeBOldRegion_interior_nonempty ha hac)
  have hAunique : UniqueDiffOn ℝ KA :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a c) (by
      rw [interior_closedCoordTriangle]
      exact openCoordTriangle_nonempty hac)
  constructor
  · exact (hOldF hpO).trans (hAxF hpA).symm
  · have hOldJet := fderivWithin_eq_of_eqOn_subset
      hOldC1 hOsub hOunique hOldF hpO
    have hFOJet := fderivWithin_eq_of_eqOn_subset
      hFC1 hOFsub hOunique (fun _ _ => rfl) hpO
    have hAxJet := fderivWithin_eq_of_eqOn_subset
      hAxC1 hAsub hAunique hAxF hpA
    have hFAJet := fderivWithin_eq_of_eqOn_subset
      hFC1 hAFsub hAunique (fun _ _ => rfl) hpA
    exact hOldJet.trans (hFOJet.symm.trans (hFAJet.trans hAxJet.symm))

end ChristodoulouBV.Uniqueness

end
