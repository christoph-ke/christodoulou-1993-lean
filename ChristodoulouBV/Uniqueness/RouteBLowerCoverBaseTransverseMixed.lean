module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.MixedPartial
public import ChristodoulouBV.ForMathlib.Geometry.NullTriangle
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# The outgoing equation for a finite incoming jet

The frozen mixed equation gives the outgoing derivative of a field. On a
finite C¹ triangle, differentiating that equation in the incoming coordinate
gives an outgoing equation for its incoming jet. No second derivative of the
original field is assumed.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- A C¹ vertical source on a finite triangle determines the outgoing
derivative of the incoming jet at every strict interior point. -/
theorem hasDerivAt_horizontal_jet_of_vertical_source_on_triangle
    {B : ℝ} (hB : 0 < B) {F G : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B))
    (hG : ContDiffOn ℝ 1 G (closedCoordTriangle 0 B))
    (hsource : ∀ p ∈ closedCoordTriangle 0 B,
      (fderivWithin ℝ F (closedCoordTriangle 0 B) p) (0, 1) = G p)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    HasDerivAt
      (fun t => (fderivWithin ℝ F (closedCoordTriangle 0 B) (u, t)) (1, 0))
      ((fderivWithin ℝ G (closedCoordTriangle 0 B) (u, v)) (1, 0)) v := by
  obtain ⟨hu, huv, hv⟩ := hp
  let a := u / 2
  let a' := (u + v) / 2
  let c := (u + 3 * v) / 4
  let d := (v + B) / 2
  have hau : a < u := by dsimp [a]; linarith
  have hua' : u < a' := by dsimp [a']; linarith
  have ha'c : a' < c := by dsimp [a', c]; linarith
  have hcv : c < v := by dsimp [c]; linarith
  have hvd : v < d := by dsimp [d]; linarith
  have hdB : d < B := by dsimp [d]; linarith
  have ha : 0 < a := by dsimp [a]; linarith
  let K := closedCoordTriangle 0 B
  let R := Icc a a' ×ˢ Icc c d
  have hmap (p : ℝ × ℝ) (hpR : p ∈ R) : p ∈ openCoordTriangle 0 B := by
    change p.1 ∈ Icc a a' ∧ p.2 ∈ Icc c d at hpR
    exact ⟨ha.trans_le hpR.1.1,
      (hpR.1.2.trans_lt ha'c).trans_le hpR.2.1,
      hpR.2.2.trans_lt hdB⟩
  have hsub : R ⊆ K := fun p hpR =>
    let h := hmap p hpR
    ⟨h.1.le, h.2.1.le, h.2.2.le⟩
  let Fu : ℝ → ℝ → ℝ := fun x y =>
    (fderivWithin ℝ F K (x, y)) (1, 0)
  let Gu : ℝ → ℝ → ℝ := fun x y =>
    (fderivWithin ℝ G K (x, y)) (1, 0)
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hFuC : ContinuousOn (fun p : ℝ × ℝ => Fu p.1 p.2) R :=
    ((hF.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const).mono hsub
  have hGuC : ContinuousOn (fun p : ℝ × ℝ => Gu p.1 p.2) R :=
    ((hG.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const).mono hsub
  have hdiffF (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc c d) : DifferentiableAt ℝ F (x, y) := by
    have hi : (x, y) ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact hmap (x, y) ⟨hx, hy⟩
    exact ((hF.differentiableOn (by norm_num)).mono interior_subset
      (x, y) hi).differentiableAt (isOpen_interior.mem_nhds hi)
  have hdiffG (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc c d) : DifferentiableAt ℝ G (x, y) := by
    have hi : (x, y) ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact hmap (x, y) ⟨hx, hy⟩
    exact ((hG.differentiableOn (by norm_num)).mono interior_subset
      (x, y) hi).differentiableAt (isOpen_interior.mem_nhds hi)
  have hFuDeriv (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc c d) :
      HasDerivAt (fun t => F (t, y)) (Fu x y) x := by
    have hwithin : fderivWithin ℝ F K (x, y) = fderiv ℝ F (x, y) :=
      fderivWithin_eq_fderiv (hunique (x, y) (hsub ⟨hx, hy⟩))
        (hdiffF x hx y hy)
    have hpair : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
      (hasDerivAt_id' x).prodMk (hasDerivAt_const x y)
    simpa only [Fu, hwithin, Function.comp_def] using
      (hdiffF x hx y hy).hasFDerivAt.comp_hasDerivAt x hpair
  have hGuDeriv (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc c d) :
      HasDerivAt (fun t => G (t, y)) (Gu x y) x := by
    have hwithin : fderivWithin ℝ G K (x, y) = fderiv ℝ G (x, y) :=
      fderivWithin_eq_fderiv (hunique (x, y) (hsub ⟨hx, hy⟩))
        (hdiffG x hx y hy)
    have hpair : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
      (hasDerivAt_id' x).prodMk (hasDerivAt_const x y)
    simpa only [Gu, hwithin, Function.comp_def] using
      (hdiffG x hx y hy).hasFDerivAt.comp_hasDerivAt x hpair
  have hGsource (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc c d) :
      HasDerivAt (fun t => F (x, t)) (G (x, y)) y := by
    have hwithin : fderivWithin ℝ F K (x, y) = fderiv ℝ F (x, y) :=
      fderivWithin_eq_fderiv (hunique (x, y) (hsub ⟨hx, hy⟩))
        (hdiffF x hx y hy)
    have hs := hsource (x, y) (hsub ⟨hx, hy⟩)
    rw [hwithin] at hs
    have hpair : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
      (hasDerivAt_const y x).prodMk (hasDerivAt_id' y)
    simpa only [hs, Function.comp_def] using
      (hdiffF x hx y hy).hasFDerivAt.comp_hasDerivAt y hpair
  have hmixed := (hasDerivWithinAt_horizontal_partial_of_vertical_partial
    (a := a) (a' := a') (b := c) (b' := d)
    (hau.trans hua') (hcv.trans hvd)
    (hF.continuousOn.mono hsub) hFuC (hG.continuousOn.mono hsub) hGuC
    (fun x hx y hy => (hFuDeriv x hx y hy).hasDerivWithinAt)
    (fun x hx y hy => (hGsource x hx y hy).hasDerivWithinAt)
    (fun x hx y hy => (hGuDeriv x hx y hy).hasDerivWithinAt)).2.2
      u ⟨hau.le, hua'.le⟩ v ⟨hcv.le, hvd.le⟩
  exact hmixed.hasDerivAt (Icc_mem_nhds hcv hvd)

end ChristodoulouBV.Uniqueness

end
