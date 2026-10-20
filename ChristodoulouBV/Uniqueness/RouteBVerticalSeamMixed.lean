module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.MixedPartial
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-!
# Mixed partials at an off-axis characteristic boundary

The vertical source only needs to be C¹ on a small rectangle beside the
seam. In particular, it need not extend smoothly across the axis of the
larger triangle.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A vertical equation on a closed local rectangle gives an ordinary
outgoing derivative of the incoming relative jet, even when the point lies
on the incoming boundary of the larger C¹ region. -/
theorem routeB_horizontal_jet_hasDerivAt_of_local_vertical_source
    {K : Set (ℝ × ℝ)} {u₀ u₁ v₀ v₁ s v : ℝ}
    (hu : u₀ < u₁) (hv : v₀ < v) (hv' : v < v₁)
    (hs : s ∈ Icc u₀ u₁)
    (hR : Icc u₀ u₁ ×ˢ Icc v₀ v₁ ⊆ K)
    (hUniqueK : UniqueDiffOn ℝ K)
    {f G : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f K)
    (hG : ContDiffOn ℝ 1 G (Icc u₀ u₁ ×ˢ Icc v₀ v₁))
    (hsource : ∀ p ∈ Icc u₀ u₁ ×ˢ Icc v₀ v₁,
      (fderivWithin ℝ f K p) (0, 1) = G p) :
    HasDerivAt
      (fun t => (fderivWithin ℝ f K (s, t)) (1, 0))
      ((fderivWithin ℝ G (Icc u₀ u₁ ×ˢ Icc v₀ v₁) (s, v)) (1, 0)) v := by
  let R := Icc u₀ u₁ ×ˢ Icc v₀ v₁
  have hvR : v₀ < v₁ := hv.trans hv'
  have hUniqueR : UniqueDiffOn ℝ R :=
    uniqueDiffOn_convex ((convex_Icc u₀ u₁).prod (convex_Icc v₀ v₁)) (by
      rw [interior_prod_eq, interior_Icc, interior_Icc]
      exact ⟨((u₀ + u₁) / 2, (v₀ + v₁) / 2),
        ⟨by constructor <;> linarith, by constructor <;> linarith⟩⟩)
  have hfc : ContinuousOn f R := hf.continuousOn.mono hR
  have hGc : ContinuousOn G R := hG.continuousOn
  have hfu : ContinuousOn
      (fun p => (fderivWithin ℝ f K p) (1, 0)) R :=
    ((hf.continuousOn_fderivWithin hUniqueK (by norm_num)).clm_apply
      continuousOn_const).mono hR
  have hGu : ContinuousOn
      (fun p => (fderivWithin ℝ G R p) (1, 0)) R :=
    (hG.continuousOn_fderivWithin hUniqueR (by norm_num)).clm_apply
      continuousOn_const
  have hslice_u {F : ℝ × ℝ → ℝ} {D : Set (ℝ × ℝ)}
      (hF : ContDiffOn ℝ 1 F D)
      (hsub : R ⊆ D)
      (x : ℝ) (hx : x ∈ Icc u₀ u₁)
      (y : ℝ) (hy : y ∈ Icc v₀ v₁) :
      HasDerivWithinAt (fun t => F (t, y))
        ((fderivWithin ℝ F D (x, y)) (1, 0)) (Icc u₀ u₁) x := by
    have hp : (x, y) ∈ D := hsub ⟨hx, hy⟩
    have hmap : MapsTo (fun t : ℝ => (t, y)) (Icc u₀ u₁) D :=
      fun t ht => hsub ⟨ht, hy⟩
    have hpair : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
      (hasDerivAt_id' x).prodMk (hasDerivAt_const x y)
    have hFd := (hF.differentiableOn (by norm_num) (x, y) hp).hasFDerivWithinAt
    simpa only [Function.comp_def] using
      hFd.comp_hasDerivWithinAt x hpair.hasDerivWithinAt hmap
  have hslice_v (x : ℝ) (hx : x ∈ Icc u₀ u₁)
      (y : ℝ) (hy : y ∈ Icc v₀ v₁) :
      HasDerivWithinAt (fun t => f (x, t)) (G (x, y)) (Icc v₀ v₁) y := by
    have hp : (x, y) ∈ K := hR ⟨hx, hy⟩
    have hmap : MapsTo (fun t : ℝ => (x, t)) (Icc v₀ v₁) K :=
      fun t ht => hR ⟨hx, ht⟩
    have hpair : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
      (hasDerivAt_const y x).prodMk (hasDerivAt_id' y)
    have hFd := (hf.differentiableOn (by norm_num) (x, y) hp).hasFDerivWithinAt
    simpa only [Function.comp_def, hsource (x, y) ⟨hx, hy⟩] using
      hFd.comp_hasDerivWithinAt y hpair.hasDerivWithinAt hmap
  have hODE := hasDerivWithinAt_horizontal_partial_of_vertical_partial
    hu hvR hfc hfu hGc hGu
    (fun x hx y hy => hslice_u hf hR x hx y hy)
    hslice_v (fun x hx y hy => hslice_u hG (subset_rfl) x hx y hy)
  have hvMem : v ∈ Icc v₀ v₁ := ⟨hv.le, hv'.le⟩
  exact (hODE.2.2 s hs v hvMem).hasDerivAt (Icc_mem_nhds hv hv')

end ChristodoulouBV.Uniqueness

end
