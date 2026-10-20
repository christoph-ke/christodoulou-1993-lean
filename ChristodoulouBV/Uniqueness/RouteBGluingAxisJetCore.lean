module

public import ChristodoulouBV.Uniqueness.RouteBGluingClassicalJet
public import ChristodoulouBV.C1Solution.AxisLocalExistenceSystem
import ChristodoulouBV.C1Solution.AxisMassDefect
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Classical axis equations as relative jets

An ordinary characteristic derivative in the strict triangle determines the
relative jet also on its incoming edge. The source needs continuity only off
the axis, where the gluing theorem uses the equation.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Transfer an outgoing ordinary derivative to a relative jet at every
off-axis point of a closed axis triangle, including its incoming edge. -/
theorem routeB_axis_vertical_jet_of_slices
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {f G : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b))
    (hG : ContinuousOn G
      (closedCoordTriangle a b ∩ developmentWithInitialEdge b))
    (hslice : ∀ u v, a < u → u < v → v < b →
      HasDerivAt (fun t => f (u, t)) (G (u, v)) v)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hpD : p ∈ developmentWithInitialEdge b) :
    (fderivWithin ℝ f (closedCoordTriangle a b) p) (0, 1) = G p := by
  let K := closedCoordTriangle a b
  let U := K ∩ developmentWithInitialEdge b
  have hUnique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b) (by
      rw [interior_closedCoordTriangle]
      exact openCoordTriangle_nonempty hab)
  have hJet : ContinuousOn
      (fun q => (fderivWithin ℝ f K q) (0, 1)) U :=
    ((hf.continuousOn_fderivWithin hUnique (by norm_num)).clm_apply
      continuousOn_const).mono inter_subset_left
  have hOpen : EqOn (fun q => (fderivWithin ℝ f K q) (0, 1)) G
      (openCoordTriangle a b) := by
    rintro ⟨u, v⟩ hq
    have hV := AxisPicard.vertical_hasDerivAt_of_triangle_c1 hf hq
    exact hV.unique (hslice u v hq.1 hq.2.1 hq.2.2)
  have hOpenSub : openCoordTriangle a b ⊆ U := by
    intro q hq
    exact ⟨⟨hq.1.le, hq.2.1.le, hq.2.2.le⟩,
      ⟨ha.trans hq.1.le, hq.2.1, hq.2.2⟩⟩
  have hClose : U ⊆ closure (openCoordTriangle a b) := by
    rw [closure_openCoordTriangle hab]
    exact inter_subset_left
  exact (hOpen.of_subset_closure hJet hG hOpenSub hClose) ⟨hp, hpD⟩

/-- Incoming analogue of `routeB_axis_vertical_jet_of_slices`. -/
theorem routeB_axis_horizontal_jet_of_slices
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {f G : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b))
    (hG : ContinuousOn G
      (closedCoordTriangle a b ∩ developmentWithInitialEdge b))
    (hslice : ∀ u v, a < u → u < v → v < b →
      HasDerivAt (fun t => f (t, v)) (G (u, v)) u)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hpD : p ∈ developmentWithInitialEdge b) :
    (fderivWithin ℝ f (closedCoordTriangle a b) p) (1, 0) = G p := by
  let K := closedCoordTriangle a b
  let U := K ∩ developmentWithInitialEdge b
  have hUnique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b) (by
      rw [interior_closedCoordTriangle]
      exact openCoordTriangle_nonempty hab)
  have hJet : ContinuousOn
      (fun q => (fderivWithin ℝ f K q) (1, 0)) U :=
    ((hf.continuousOn_fderivWithin hUnique (by norm_num)).clm_apply
      continuousOn_const).mono inter_subset_left
  have hOpen : EqOn (fun q => (fderivWithin ℝ f K q) (1, 0)) G
      (openCoordTriangle a b) := by
    rintro ⟨u, v⟩ hq
    have hH := AxisPicard.horizontal_hasDerivAt_of_triangle_c1 hf hq
    exact hH.unique (hslice u v hq.1 hq.2.1 hq.2.2)
  have hOpenSub : openCoordTriangle a b ⊆ U := by
    intro q hq
    exact ⟨⟨hq.1.le, hq.2.1.le, hq.2.2.le⟩,
      ⟨ha.trans hq.1.le, hq.2.1, hq.2.2⟩⟩
  have hClose : U ⊆ closure (openCoordTriangle a b) := by
    rw [closure_openCoordTriangle hab]
    exact inter_subset_left
  exact (hOpen.of_subset_closure hJet hG hOpenSub hClose) ⟨hp, hpD⟩

end ChristodoulouBV.Uniqueness

end
