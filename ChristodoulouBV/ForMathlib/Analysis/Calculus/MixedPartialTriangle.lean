module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.MixedPartialInterior
public import ChristodoulouBV.ForMathlib.Geometry.NullTriangle
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# Commuting a mixed partial on the interior of a closed triangle

The source of the horizontal derivative is only C¹. The resulting outgoing
derivative of the vertical jet exists without assuming that the original
function is C².
-/

public section

open Set Filter
open scoped Topology

/-- A C¹ horizontal source can be differentiated vertically and then
integrated horizontally at any strict interior point of a triangle. -/
theorem hasDerivAt_vertical_deriv_of_horizontal_source_on_triangle
    {B : ℝ} (hB : 0 < B) {F G : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B))
    (hG : ContDiffOn ℝ 1 G (closedCoordTriangle 0 B))
    (hsource : ∀ p ∈ closedCoordTriangle 0 B,
      (fderivWithin ℝ F (closedCoordTriangle 0 B) p) (1, 0) = G p)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    HasDerivAt (fun s => deriv (fun t => F (s, t)) v)
      (deriv (fun t => G (u, t)) v) u := by
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
  let Fv : ℝ → ℝ → ℝ := fun x y =>
    (fderivWithin ℝ F K (x, y)) (0, 1)
  let Gv : ℝ → ℝ → ℝ := fun x y =>
    (fderivWithin ℝ G K (x, y)) (0, 1)
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hFvC : ContinuousOn (fun p : ℝ × ℝ => Fv p.1 p.2) R :=
    ((hF.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const).mono hsub
  have hGvC : ContinuousOn (fun p : ℝ × ℝ => Gv p.1 p.2) R :=
    ((hG.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const).mono hsub
  have hFvDeriv (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc c d) :
      HasDerivAt (fun t => F (x, t)) (Fv x y) y := by
    have hi : (x, y) ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact hmap (x, y) ⟨hx, hy⟩
    have hd : DifferentiableAt ℝ F (x, y) :=
      ((hF.differentiableOn (by norm_num)).mono interior_subset (x, y) hi).differentiableAt
        (isOpen_interior.mem_nhds hi)
    have hwithin : fderivWithin ℝ F K (x, y) = fderiv ℝ F (x, y) :=
      fderivWithin_eq_fderiv (hunique (x, y) (interior_subset hi)) hd
    have hpair : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
      (hasDerivAt_const y x).prodMk (hasDerivAt_id' y)
    have hcomp := hd.hasFDerivAt.comp_hasDerivAt y hpair
    simpa only [Fv, hwithin, Function.comp_def] using hcomp
  have hGvDeriv (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc c d) :
      HasDerivAt (fun t => G (x, t)) (Gv x y) y := by
    have hi : (x, y) ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact hmap (x, y) ⟨hx, hy⟩
    have hd : DifferentiableAt ℝ G (x, y) :=
      ((hG.differentiableOn (by norm_num)).mono interior_subset (x, y) hi).differentiableAt
        (isOpen_interior.mem_nhds hi)
    have hwithin : fderivWithin ℝ G K (x, y) = fderiv ℝ G (x, y) :=
      fderivWithin_eq_fderiv (hunique (x, y) (interior_subset hi)) hd
    have hpair : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
      (hasDerivAt_const y x).prodMk (hasDerivAt_id' y)
    have hcomp := hd.hasFDerivAt.comp_hasDerivAt y hpair
    simpa only [Gv, hwithin, Function.comp_def] using hcomp
  have hFhDeriv (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc c d) :
      HasDerivAt (fun t => F (t, y)) (G (x, y)) x := by
    have hi : (x, y) ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact hmap (x, y) ⟨hx, hy⟩
    have hd : DifferentiableAt ℝ F (x, y) :=
      ((hF.differentiableOn (by norm_num)).mono interior_subset (x, y) hi).differentiableAt
        (isOpen_interior.mem_nhds hi)
    have hwithin : fderivWithin ℝ F K (x, y) = fderiv ℝ F (x, y) :=
      fderivWithin_eq_fderiv (hunique (x, y) (interior_subset hi)) hd
    have hs := hsource (x, y) (hsub ⟨hx, hy⟩)
    rw [hwithin] at hs
    have hpair : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
      (hasDerivAt_id' x).prodMk (hasDerivAt_const x y)
    have hcomp := hd.hasFDerivAt.comp_hasDerivAt x hpair
    simpa only [hs, Function.comp_def] using hcomp
  have hmixed := hasDerivAt_vertical_partial_of_horizontal_equation
    (u₀ := a) (u₁ := a') (v₀ := c) (v₁ := d)
    (hau.trans hua') (hcv.trans hvd)
    (hF.continuousOn.mono hsub) hFvC (hG.continuousOn.mono hsub) hGvC
    (fun x hx y hy => hFvDeriv x hx y hy)
    (fun x hx y hy => hFhDeriv x hx y hy)
    (fun x hx y hy => hGvDeriv x hx y hy)
    ⟨hau, hua'⟩ ⟨hcv, hvd⟩
  have hEq : (fun x => deriv (fun t => F (x, t)) v) =ᶠ[𝓝 u]
      (fun x => Fv x v) := by
    filter_upwards [Ioo_mem_nhds hau hua'] with x hx
    exact (hFvDeriv x ⟨hx.1.le, hx.2.le⟩ v
      ⟨hcv.le, hvd.le⟩).deriv
  rw [← (hGvDeriv u ⟨hau.le, hua'.le⟩ v
    ⟨hcv.le, hvd.le⟩).deriv] at hmixed
  exact hmixed.congr_of_eventuallyEq hEq

end
