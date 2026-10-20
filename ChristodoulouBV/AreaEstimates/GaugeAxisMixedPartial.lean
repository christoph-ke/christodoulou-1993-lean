module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.MixedPartial
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Tactic

/-!
# Commuting a C¹ mixed transport on an interior rectangle

A C¹ field need not have all second derivatives. If one coordinate partial
equals a C¹ transport density, the other mixed partial nevertheless exists
and equals the derivative of that density. The rectangle lemmas below use the
fundamental theorem of calculus and differentiation under the integral.
-/

public section

open Set

namespace ChristodoulouBV

private theorem hasDerivAt_horizontal_slice {f : ℝ × ℝ → ℝ}
    {u v : ℝ} (hf : DifferentiableAt ℝ f (u, v)) :
    HasDerivAt (fun x => f (x, v)) ((fderiv ℝ f (u, v)) (1, 0)) u := by
  have hp : HasDerivAt (fun x : ℝ => (x, v)) (1, 0) u :=
    (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
  simpa only [Function.comp_def] using hf.hasFDerivAt.comp_hasDerivAt u hp

private theorem hasDerivAt_vertical_slice {f : ℝ × ℝ → ℝ}
    {u v : ℝ} (hf : DifferentiableAt ℝ f (u, v)) :
    HasDerivAt (fun y => f (u, y)) ((fderiv ℝ f (u, v)) (0, 1)) v := by
  have hp : HasDerivAt (fun y : ℝ => (u, y)) (0, 1) v :=
    (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
  simpa only [Function.comp_def] using hf.hasFDerivAt.comp_hasDerivAt v hp

/-- A C¹ horizontal transport density permits the interchange
`∂ᵤ(∂ᵥ f) = ∂ᵥ g` on every contained rectangle. -/
theorem mixed_horizontal_on_rectangle
    {T : Set (ℝ × ℝ)} (hT : IsOpen T)
    {f g : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f T) (hg : ContDiffOn ℝ 1 g T)
    (hfu : ∀ p ∈ T, (fderiv ℝ f p) (1, 0) = g p)
    {a a' d d' : ℝ} (haa' : a < a') (hdd' : d < d')
    (hR : Icc a a' ×ˢ Icc d d' ⊆ T)
    {u v : ℝ} (hu : u ∈ Icc a a') (hv : v ∈ Icc d d') :
    HasDerivWithinAt
      (fun x => (fderiv ℝ f (x, v)) (0, 1))
      ((fderiv ℝ g (u, v)) (0, 1)) (Icc a a') u := by
  let R := Icc a a' ×ˢ Icc d d'
  have hfc : ContinuousOn f R := hf.continuousOn.mono hR
  have hgc : ContinuousOn g R := hg.continuousOn.mono hR
  have hfjet : ContinuousOn (fun p => (fderiv ℝ f p) (0, 1)) R :=
    ((hf.continuousOn_fderiv_of_isOpen hT (by norm_num)).clm_apply
      continuousOn_const).mono hR
  have hgjet : ContinuousOn (fun p => (fderiv ℝ g p) (0, 1)) R :=
    ((hg.continuousOn_fderiv_of_isOpen hT (by norm_num)).clm_apply
      continuousOn_const).mono hR
  have hfdiff (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc d d') : DifferentiableAt ℝ f (x, y) :=
    (hf.differentiableOn (by norm_num) (x, y) (hR ⟨hx, hy⟩)).differentiableAt
      (hT.mem_nhds (hR ⟨hx, hy⟩))
  have hgdiff (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc d d') : DifferentiableAt ℝ g (x, y) :=
    (hg.differentiableOn (by norm_num) (x, y) (hR ⟨hx, hy⟩)).differentiableAt
      (hT.mem_nhds (hR ⟨hx, hy⟩))
  have hfvertical (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc d d') :
      HasDerivWithinAt (fun t => f (x, t))
        ((fderiv ℝ f (x, y)) (0, 1)) (Icc d d') y :=
    (hasDerivAt_vertical_slice (hfdiff x hx y hy)).hasDerivWithinAt
  have hfhorizontal (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc d d') :
      HasDerivWithinAt (fun t => f (t, y)) (g (x, y)) (Icc a a') x := by
    convert (hasDerivAt_horizontal_slice (hfdiff x hx y hy)).hasDerivWithinAt using 1
    exact (hfu (x, y) (hR ⟨hx, hy⟩)).symm
  have hgvertical (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc d d') :
      HasDerivWithinAt (fun t => g (x, t))
        ((fderiv ℝ g (x, y)) (0, 1)) (Icc d d') y :=
    (hasDerivAt_vertical_slice (hgdiff x hx y hy)).hasDerivWithinAt
  exact (hasDerivWithinAt_vertical_partial_of_horizontal_partial
    haa' hdd' hfc hfjet hgc hgjet hfvertical hfhorizontal hgvertical).2.2 u hu v hv

/-- A C¹ vertical transport density permits the interchange
`∂ᵥ(∂ᵤ f) = ∂ᵤ g` on every contained rectangle. -/
theorem mixed_vertical_on_rectangle
    {T : Set (ℝ × ℝ)} (hT : IsOpen T)
    {f g : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f T) (hg : ContDiffOn ℝ 1 g T)
    (hfv : ∀ p ∈ T, (fderiv ℝ f p) (0, 1) = g p)
    {a a' d d' : ℝ} (haa' : a < a') (hdd' : d < d')
    (hR : Icc a a' ×ˢ Icc d d' ⊆ T)
    {u v : ℝ} (hu : u ∈ Icc a a') (hv : v ∈ Icc d d') :
    HasDerivWithinAt
      (fun y => (fderiv ℝ f (u, y)) (1, 0))
      ((fderiv ℝ g (u, v)) (1, 0)) (Icc d d') v := by
  let R := Icc a a' ×ˢ Icc d d'
  have hfc : ContinuousOn f R := hf.continuousOn.mono hR
  have hgc : ContinuousOn g R := hg.continuousOn.mono hR
  have hfjet : ContinuousOn (fun p => (fderiv ℝ f p) (1, 0)) R :=
    ((hf.continuousOn_fderiv_of_isOpen hT (by norm_num)).clm_apply
      continuousOn_const).mono hR
  have hgjet : ContinuousOn (fun p => (fderiv ℝ g p) (1, 0)) R :=
    ((hg.continuousOn_fderiv_of_isOpen hT (by norm_num)).clm_apply
      continuousOn_const).mono hR
  have hfdiff (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc d d') : DifferentiableAt ℝ f (x, y) :=
    (hf.differentiableOn (by norm_num) (x, y) (hR ⟨hx, hy⟩)).differentiableAt
      (hT.mem_nhds (hR ⟨hx, hy⟩))
  have hgdiff (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc d d') : DifferentiableAt ℝ g (x, y) :=
    (hg.differentiableOn (by norm_num) (x, y) (hR ⟨hx, hy⟩)).differentiableAt
      (hT.mem_nhds (hR ⟨hx, hy⟩))
  have hfhorizontal (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc d d') :
      HasDerivWithinAt (fun t => f (t, y))
        ((fderiv ℝ f (x, y)) (1, 0)) (Icc a a') x :=
    (hasDerivAt_horizontal_slice (hfdiff x hx y hy)).hasDerivWithinAt
  have hfvertical (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc d d') :
      HasDerivWithinAt (fun t => f (x, t)) (g (x, y)) (Icc d d') y := by
    convert (hasDerivAt_vertical_slice (hfdiff x hx y hy)).hasDerivWithinAt using 1
    exact (hfv (x, y) (hR ⟨hx, hy⟩)).symm
  have hghorizontal (x : ℝ) (hx : x ∈ Icc a a')
      (y : ℝ) (hy : y ∈ Icc d d') :
      HasDerivWithinAt (fun t => g (t, y))
        ((fderiv ℝ g (x, y)) (1, 0)) (Icc a a') x :=
    (hasDerivAt_horizontal_slice (hgdiff x hx y hy)).hasDerivWithinAt
  exact (hasDerivWithinAt_horizontal_partial_of_vertical_partial
    haa' hdd' hfc hfjet hgc hgjet hfhorizontal hfvertical hghorizontal).2.2 u hu v hv

end ChristodoulouBV

end
