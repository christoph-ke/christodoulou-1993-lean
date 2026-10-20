module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Banach-valued parameter integrals on a closed rectangle

Joint continuity of an integrand and its parameter derivative on a compact
rectangle gives differentiation under an interval integral. The derivative is
needed only in the interior of the parameter interval.
-/

public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiate a Banach-valued integral in a parameter when the derivative
extends continuously to the closed parameter and integration rectangle. -/
theorem hasDerivAt_integral_of_continuousOn_rectangle_banach
    {a a' b b' u v : ℝ}
    (hu : u ∈ Ioo a a') (hv : v ∈ Icc b b')
    {F F' : ℝ → ℝ → E}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Icc a a' ×ˢ Icc b b'))
    (hF' : ContinuousOn (fun p : ℝ × ℝ => F' p.1 p.2)
      (Icc a a' ×ˢ Icc b b'))
    (hderiv : ∀ x ∈ Ioo a a', ∀ t ∈ Icc b b',
      HasDerivAt (fun y => F y t) (F' x t) x) :
    HasDerivAt (fun x => ∫ t in b..v, F x t) (∫ t in b..v, F' u t) u := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF'
  have hslice (H : ℝ → ℝ → E)
      (hH : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2)
        (Icc a a' ×ˢ Icc b b'))
      (x : ℝ) (hx : x ∈ Icc a a') : ContinuousOn (H x) (Icc b v) := by
    exact hH.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hx, ⟨ht.1, ht.2.trans hv.2⟩⟩)
  have hFint (x : ℝ) (hx : x ∈ Icc a a') :
      IntervalIntegrable (F x) volume b v :=
    ((hslice F hF x hx).intervalIntegrable_of_Icc hv.1)
  have hF'int (x : ℝ) (hx : x ∈ Icc a a') :
      IntervalIntegrable (F' x) volume b v :=
    ((hslice F' hF' x hx).intervalIntegrable_of_Icc hv.1)
  have hmeas (x : ℝ) (hx : x ∈ Icc a a') :
      AEStronglyMeasurable (F x) (volume.restrict (Ι b v)) :=
    (intervalIntegrable_iff.1 (hFint x hx)).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (F' u) (volume.restrict (Ι b v)) :=
    (intervalIntegrable_iff.1 (hF'int u ⟨hu.1.le, hu.2.le⟩)).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ => C) (s := Ioo a a')
    (Ioo_mem_nhds hu.1 hu.2)
    (by
      filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
      exact hmeas x ⟨hx.1.le, hx.2.le⟩)
    (hFint u ⟨hu.1.le, hu.2.le⟩) hmeas'
    (by
      filter_upwards with t ht
      simp only [uIoc_of_le hv.1] at ht
      intro x hx
      exact hC (x, t) ⟨⟨hx.1.le, hx.2.le⟩, ⟨ht.1.le, ht.2.trans hv.2⟩⟩)
    intervalIntegrable_const
    (by
      filter_upwards with t ht
      simp only [uIoc_of_le hv.1] at ht
      intro x hx
      exact hderiv x hx t ⟨ht.1.le, ht.2.trans hv.2⟩)).2

/-- Integrating a jointly continuous Banach-valued field over a fixed
subinterval gives a function continuous in the other rectangle coordinate. -/
theorem continuousOn_integral_of_continuousOn_rectangle_banach
    {a a' b b' v : ℝ} (hv : v ∈ Icc b b') {F : ℝ → ℝ → E}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Icc a a' ×ˢ Icc b b')) :
    ContinuousOn (fun x => ∫ t in b..v, F x t) (Icc a a') := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF
  intro u hu
  have hslice (x : ℝ) (hx : x ∈ Icc a a') : ContinuousOn (F x) (Icc b v) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hx, ⟨ht.1, ht.2.trans hv.2⟩⟩)
  have hmeas (x : ℝ) (hx : x ∈ Icc a a') :
      AEStronglyMeasurable (F x) (volume.restrict (Ι b v)) :=
    (intervalIntegrable_iff.1
      ((hslice x hx).intervalIntegrable_of_Icc hv.1)).aestronglyMeasurable
  apply continuousWithinAt_of_dominated_interval
    (bound := fun _ => C)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact hmeas x hx
  · filter_upwards [self_mem_nhdsWithin] with x hx
    filter_upwards with t ht
    simp only [uIoc_of_le hv.1] at ht
    exact hC (x, t) ⟨hx, ⟨ht.1.le, ht.2.trans hv.2⟩⟩
  · exact intervalIntegrable_const
  · filter_upwards with t ht
    simp only [uIoc_of_le hv.1] at ht
    have htR : t ∈ Icc b b' := ⟨ht.1.le, ht.2.trans hv.2⟩
    exact (hF.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun x hx => ⟨hx, htR⟩)) u hu

/-- Differentiate a Banach-valued parameter integral at every point of the
closed parameter interval, taking a relative derivative at its endpoints. -/
theorem hasDerivWithinAt_integral_of_continuousOn_rectangle_banach
    {a a' b b' u v : ℝ} (haa' : a < a')
    (hu : u ∈ Icc a a') (hv : v ∈ Icc b b')
    {F F' : ℝ → ℝ → E}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Icc a a' ×ˢ Icc b b'))
    (hF' : ContinuousOn (fun p : ℝ × ℝ => F' p.1 p.2)
      (Icc a a' ×ˢ Icc b b'))
    (hderiv : ∀ x ∈ Ioo a a', ∀ t ∈ Icc b b',
      HasDerivAt (fun y => F y t) (F' x t) x) :
    HasDerivWithinAt (fun x => ∫ t in b..v, F x t)
      (∫ t in b..v, F' u t) (Icc a a') u := by
  let g : ℝ → E := fun x => ∫ t in b..v, F x t
  let g' : ℝ → E := fun x => ∫ t in b..v, F' x t
  let L : E → ℝ →L[ℝ] E :=
    fun e => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) e
  have hL : Continuous L :=
    (ContinuousLinearMap.smulRightL ℝ ℝ E 1).continuous
  have hg : ContinuousOn g (Icc a a') :=
    continuousOn_integral_of_continuousOn_rectangle_banach hv hF
  have hg' : ContinuousOn g' (Icc a a') :=
    continuousOn_integral_of_continuousOn_rectangle_banach hv hF'
  have hdiff : DifferentiableOn ℝ g (Ioo a a') := by
    intro x hx
    exact ((hasDerivAt_integral_of_continuousOn_rectangle_banach
      hx hv hF hF' hderiv).differentiableAt).differentiableWithinAt
  have hderiv' : ∀ x ∈ Ioo a a', fderiv ℝ g x = L (g' x) := by
    intro x hx
    exact (hasDerivAt_integral_of_continuousOn_rectangle_banach
      hx hv hF hF' hderiv).hasFDerivAt.fderiv
  have hcont : ∀ x ∈ closure (Ioo a a'), ContinuousWithinAt g (Ioo a a') x := by
    rw [closure_Ioo haa'.ne]
    intro x hx
    exact (hg x hx).mono Ioo_subset_Icc_self
  have hlim : Tendsto (fun x => fderiv ℝ g x)
      (𝓝[Ioo a a'] u) (𝓝 (L (g' u))) := by
    have hG : Tendsto (fun x => L (g' x))
        (𝓝[Ioo a a'] u) (𝓝 (L (g' u))) :=
      hL.continuousAt.comp_continuousWithinAt
        ((hg' u hu).mono Ioo_subset_Icc_self)
    apply hG.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hderiv' x hx).symm
  have h := hasFDerivWithinAt_closure_of_tendsto_fderiv
    hdiff (convex_Ioo a a') isOpen_Ioo hcont hlim
  rw [closure_Ioo haa'.ne] at h
  simpa [g, g', L] using h.hasDerivWithinAt

end intervalIntegral

/-- Chain rule along a vertical parameter line with a moving Banach-valued state. -/
theorem HasFDerivAt.hasDerivAt_vertical_state
    {S T : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup T] [NormedSpace ℝ T]
    {f : ((ℝ × ℝ) × S) → T} {f' : ((ℝ × ℝ) × S) →L[ℝ] T}
    {Z : ℝ → S} {s v : ℝ} {z' : S}
    (hf : HasFDerivAt f f' ((s, v), Z v))
    (hZ : HasDerivAt Z z' v) :
    HasDerivAt (fun t => f ((s, t), Z t)) (f' ((0, 1), z')) v := by
  have hline : HasDerivAt (fun t : ℝ => ((s, t), Z t))
      ((0, 1), z') v :=
    ((hasDerivAt_const v s).prodMk (hasDerivAt_id v)).prodMk hZ
  simpa only [Function.comp_def] using hf.comp_hasDerivAt v hline

/-- Chain rule along a horizontal parameter line with a moving Banach-valued state. -/
theorem HasFDerivAt.hasDerivAt_horizontal_state
    {S T : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup T] [NormedSpace ℝ T]
    {f : ((ℝ × ℝ) × S) → T} {f' : ((ℝ × ℝ) × S) →L[ℝ] T}
    {Z : ℝ → S} {u t : ℝ} {z' : S}
    (hf : HasFDerivAt f f' ((u, t), Z u))
    (hZ : HasDerivAt Z z' u) :
    HasDerivAt (fun s => f ((s, t), Z s)) (f' ((1, 0), z')) u := by
  have hline : HasDerivAt (fun s : ℝ => ((s, t), Z s))
      ((1, 0), z') u :=
    ((hasDerivAt_id u).prodMk (hasDerivAt_const u t)).prodMk hZ
  simpa only [Function.comp_def] using hf.comp_hasDerivAt u hline

end
