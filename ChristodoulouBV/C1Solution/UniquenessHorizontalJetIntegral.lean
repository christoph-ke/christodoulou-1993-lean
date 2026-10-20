module

public import ChristodoulouBV.C1Solution.RectangleJetSeamsHorizontal
public import ChristodoulouBV.C1Solution.UniquenessFinal
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Horizontal integration of outgoing jets

A continuous horizontal equation on the closed triangle can be
differentiated in the outgoing direction on each off-axis rectangle.
This gives the horizontal integral identity for its outgoing jet.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace ChristodoulouBV.C1Solution

/-- The outgoing relative jet of a C¹ field satisfies the differentiated
horizontal equation at each point strictly below the horizontal top edge. -/
theorem triangle_vertical_jet_hasDerivWithinAt_of_horizontal_equation
    {B : ℝ} (hB : 0 < B) {F G : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B))
    (hG : ContDiffOn ℝ 1 G (closedCoordTriangle 0 B))
    (hFu : ∀ p ∈ closedCoordTriangle 0 B,
      (fderivWithin ℝ F (closedCoordTriangle 0 B) p) (1, 0) = G p)
    {s v : ℝ} (hs : 0 ≤ s) (hsv : s < v) (hv : v ≤ B) :
    HasDerivWithinAt
      (fun t => (fderivWithin ℝ F (closedCoordTriangle 0 B) (t, v)) (0, 1))
      ((fderivWithin ℝ G (closedCoordTriangle 0 B) (s, v)) (0, 1))
      (Icc 0 ((s + v) / 2)) s := by
  let T := closedCoordTriangle 0 B
  let a₁ := (s + v) / 2
  let b₀ := (s + v) / 2
  let R := Icc 0 a₁ ×ˢ Icc b₀ B
  have ha₁ : 0 < a₁ := by dsimp [a₁]; linarith
  have hb₀ : b₀ < B := by dsimp [b₀]; linarith
  have hR : R ⊆ T := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨hx.1, hx.2.trans hy.1, hy.2⟩
  have hunique : UniqueDiffOn ℝ T :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  let Fv : ℝ → ℝ → ℝ := fun x y => (fderivWithin ℝ F T (x, y)) (0, 1)
  let Gv : ℝ → ℝ → ℝ := fun x y => (fderivWithin ℝ G T (x, y)) (0, 1)
  have hFvcont : ContinuousOn (fun p => Fv p.1 p.2) R :=
    ((hF.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const).mono hR
  have hGvcont : ContinuousOn (fun p => Gv p.1 p.2) R :=
    ((hG.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const).mono hR
  have hcoord {H : ℝ × ℝ → ℝ} (hH : ContDiffOn ℝ 1 H T)
      (x : ℝ) (hx : x ∈ Icc 0 a₁)
      (y : ℝ) (hy : y ∈ Icc b₀ B) :
      HasDerivWithinAt (fun t => H (t, y))
        ((fderivWithin ℝ H T (x, y)) (1, 0)) (Icc 0 a₁) x ∧
      HasDerivWithinAt (fun t => H (x, t))
        ((fderivWithin ℝ H T (x, y)) (0, 1)) (Icc b₀ B) y := by
    have hp : (x, y) ∈ T := hR ⟨hx, hy⟩
    have hFd := (hH.differentiableOn (by norm_num) (x, y) hp).hasFDerivWithinAt
    constructor
    · have hpair : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
        (hasDerivAt_id' x).prodMk (hasDerivAt_const x y)
      have hmap : MapsTo (fun t : ℝ => (t, y)) (Icc 0 a₁) T :=
        fun t ht => hR ⟨ht, hy⟩
      simpa only [Function.comp_def] using
        hFd.comp_hasDerivWithinAt x hpair.hasDerivWithinAt hmap
    · have hpair : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
        (hasDerivAt_const y x).prodMk (hasDerivAt_id' y)
      have hmap : MapsTo (fun t : ℝ => (x, t)) (Icc b₀ B) T :=
        fun t ht => hR ⟨hx, ht⟩
      simpa only [Function.comp_def] using
        hFd.comp_hasDerivWithinAt y hpair.hasDerivWithinAt hmap
  have hFhorizontal (x : ℝ) (hx : x ∈ Icc 0 a₁)
      (y : ℝ) (hy : y ∈ Icc b₀ B) :
      HasDerivWithinAt (fun t => F (t, y)) (G (x, y)) (Icc 0 a₁) x := by
    rw [← hFu (x, y) (hR ⟨hx, hy⟩)]
    exact (hcoord hF x hx y hy).1
  have hGvertical (x : ℝ) (hx : x ∈ Icc 0 a₁)
      (y : ℝ) (hy : y ∈ Icc b₀ B) :
      HasDerivWithinAt (fun t => G (x, t)) (Gv x y) (Icc b₀ B) y :=
    (hcoord hG x hx y hy).2
  have hsI : s ∈ Icc 0 a₁ := by dsimp [a₁]; constructor <;> linarith
  have hvI : v ∈ Icc b₀ B := by dsimp [b₀]; constructor <;> linarith
  exact hasDerivWithinAt_vertical_jet_of_horizontal_equation
    ha₁ hb₀ (hF.continuousOn.mono hR)
    (hG.continuousOn.mono hR) hGvcont
    (fun x hx y hy => (hcoord hF x hx y hy).2)
    hFhorizontal hGvertical hsI hvI

/-- The outgoing jet of a horizontally driven C¹ field equals its initial
jet plus the horizontal integral of the outgoing jet of the source. -/
theorem integral_horizontal_source_vertical_jet_eq_sub
    {B : ℝ} (hB : 0 < B) {F G : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B))
    (hG : ContDiffOn ℝ 1 G (closedCoordTriangle 0 B))
    (hFu : ∀ p ∈ closedCoordTriangle 0 B,
      (fderivWithin ℝ F (closedCoordTriangle 0 B) p) (1, 0) = G p)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ B) :
    (∫ s in (0 : ℝ)..u,
      (fderivWithin ℝ G (closedCoordTriangle 0 B) (s, v)) (0, 1)) =
      (fderivWithin ℝ F (closedCoordTriangle 0 B) (u, v)) (0, 1) -
      (fderivWithin ℝ F (closedCoordTriangle 0 B) (0, v)) (0, 1) := by
  let T := closedCoordTriangle 0 B
  let Fv : ℝ → ℝ := fun s => (fderivWithin ℝ F T (s, v)) (0, 1)
  let Gv : ℝ → ℝ := fun s => (fderivWithin ℝ G T (s, v)) (0, 1)
  have hunique : UniqueDiffOn ℝ T :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hmap : MapsTo (fun s : ℝ => (s, v)) (Icc 0 u) T := by
    intro s hs
    exact ⟨hs.1, hs.2.trans huv, hv⟩
  have hFvc : ContinuousOn Fv (Icc 0 u) :=
    ((hF.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const).comp
      (continuous_id.prodMk continuous_const).continuousOn hmap
  have hGvc : ContinuousOn Gv (Icc 0 u) :=
    ((hG.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const).comp
      (continuous_id.prodMk continuous_const).continuousOn hmap
  have hderiv (s : ℝ) (hs : s ∈ Ioo 0 u) : HasDerivAt Fv (Gv s) s := by
    have hlocal := triangle_vertical_jet_hasDerivWithinAt_of_horizontal_equation
      hB hF hG hFu hs.1.le (hs.2.trans_le huv) hv
    have hsupper : s < (s + v) / 2 := by linarith only [hs.2, huv]
    have hzero : (0 : ℝ) < s := hs.1
    exact hlocal.hasDerivAt (Icc_mem_nhds hzero hsupper)
  have hint : IntervalIntegrable Gv volume 0 u :=
    hGvc.intervalIntegrable_of_Icc hu
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hu hFvc hderiv hint

/-- A continuous horizontal equation integrates from the initial edge to
any point of the same incoming ray. -/
theorem integral_horizontal_source_eq_sub
    {B : ℝ} (_hB : 0 < B) {F G : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B))
    (hG : ContDiffOn ℝ 1 G (closedCoordTriangle 0 B))
    (hFu : ∀ p ∈ closedCoordTriangle 0 B,
      (fderivWithin ℝ F (closedCoordTriangle 0 B) p) (1, 0) = G p)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ B) :
    (∫ s in (0 : ℝ)..u, G (s, v)) = F (u, v) - F (0, v) := by
  let T := closedCoordTriangle 0 B
  have hmap : MapsTo (fun s : ℝ => (s, v)) (Icc 0 u) T := by
    intro s hs
    exact ⟨hs.1, hs.2.trans huv, hv⟩
  have hFc : ContinuousOn (fun s => F (s, v)) (Icc 0 u) :=
    hF.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hmap
  have hGc : ContinuousOn (fun s => G (s, v)) (Icc 0 u) :=
    hG.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hmap
  have hderiv (s : ℝ) (hs : s ∈ Ioo 0 u) :
      HasDerivAt (fun t => F (t, v)) (G (s, v)) s := by
    have hp : (s, v) ∈ T := ⟨hs.1.le, hs.2.le.trans huv, hv⟩
    have hFd := (hF.differentiableOn (by norm_num) (s, v) hp).hasFDerivWithinAt
    have hpair : HasDerivAt (fun t : ℝ => (t, v)) (1, 0) s :=
      (hasDerivAt_id' s).prodMk (hasDerivAt_const s v)
    have hlocal : ∀ᶠ t in 𝓝 s, (t, v) ∈ T := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
      exact ⟨ht.1.le, ht.2.le.trans huv, hv⟩
    simpa only [Function.comp_def, hFu (s, v) hp] using
      hFd.comp_hasDerivAt s hpair hlocal
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hu hFc hderiv (hGc.intervalIntegrable_of_Icc hu)

end ChristodoulouBV.C1Solution

end
