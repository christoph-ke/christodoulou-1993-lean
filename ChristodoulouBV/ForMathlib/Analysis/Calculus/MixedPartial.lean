module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Mixed partial derivatives on rectangles

The fundamental theorem of calculus and differentiation under the integral sign give a
mixed partial derivative without assuming a full second derivative of the original function.
The first jets may be given only on a closed rectangle.
-/

public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace intervalIntegral

/-- The fundamental theorem of calculus on a closed interval, with a prescribed continuous
derivative on its interior. The endpoint values of the derivative need only be continuous. -/
theorem integral_eq_sub_of_continuousOn_hasDerivAt
    {a b : ℝ} (hab : a ≤ b) {f f' : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ContinuousOn f' (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    ∫ x in a..b, f' x = f b - f a :=
  integral_eq_sub_of_hasDerivAt_of_le hab hf hderiv
    (hf'.intervalIntegrable_of_Icc hab)

/-- Differentiation under an interval integral when the parameter derivative extends
continuously to a compact rectangle. Only interior parameter derivatives are needed. -/
theorem hasDerivAt_integral_of_continuousOn_rectangle
    {a a' b b' u v : ℝ}
    (hu : u ∈ Ioo a a') (hv : v ∈ Icc b b')
    {F F' : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Icc a a' ×ˢ Icc b b'))
    (hF' : ContinuousOn (fun p : ℝ × ℝ => F' p.1 p.2)
      (Icc a a' ×ˢ Icc b b'))
    (hderiv : ∀ x ∈ Ioo a a', ∀ t ∈ Icc b b',
      HasDerivAt (fun y => F y t) (F' x t) x) :
    HasDerivAt (fun x => ∫ t in b..v, F x t) (∫ t in b..v, F' u t) u := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF'
  have hslice (H : ℝ → ℝ → ℝ)
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

/-- An interval integral of a jointly continuous function is continuous in its parameter on a
compact rectangle. The upper integration limit may be any point in the vertical interval. -/
theorem continuousOn_integral_of_continuousOn_rectangle
    {a a' b b' v : ℝ} (hv : v ∈ Icc b b') {F : ℝ → ℝ → ℝ}
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

end intervalIntegral

/-- On a closed rectangle, a continuous first jet of `f` and a continuous horizontal
derivative of its vertical partial `G` determine the vertical derivative of the horizontal
partial. All derivatives at endpoints are relative derivatives. -/
theorem hasDerivWithinAt_horizontal_partial_of_vertical_partial
    {a a' b b' : ℝ} (haa' : a < a') (hbb' : b < b')
    {f fu G Gu : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Icc a a' ×ˢ Icc b b'))
    (hfu : ContinuousOn (fun p : ℝ × ℝ => fu p.1 p.2)
      (Icc a a' ×ˢ Icc b b'))
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2)
      (Icc a a' ×ˢ Icc b b'))
    (hGu : ContinuousOn (fun p : ℝ × ℝ => Gu p.1 p.2)
      (Icc a a' ×ˢ Icc b b'))
    (hfu_deriv : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      HasDerivWithinAt (fun x => f x v) (fu u v) (Icc a a') u)
    (hG_deriv : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      HasDerivWithinAt (f u) (G u v) (Icc b b') v)
    (hGu_deriv : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      HasDerivWithinAt (fun x => G x v) (Gu u v) (Icc a a') u) :
    (∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      f u v = f u b + ∫ t in b..v, G u t) ∧
    (∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      fu u v = fu u b + ∫ t in b..v, Gu u t) ∧
    (∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      HasDerivWithinAt (fu u) (Gu u v) (Icc b b') v) := by
  have hslice {F : ℝ → ℝ → ℝ}
      (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
        (Icc a a' ×ˢ Icc b b'))
      (u : ℝ) (hu : u ∈ Icc a a') : ContinuousOn (F u) (Icc b b') :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨hu, hv⟩)
  have hfirst (u : ℝ) (hu : u ∈ Icc a a')
      (v : ℝ) (hv : v ∈ Icc b b') :
      f u v = f u b + ∫ t in b..v, G u t := by
    have hderiv : ∀ t ∈ Ioo b v, HasDerivAt (f u) (G u t) t := by
      intro t ht
      exact (hG_deriv u hu t ⟨ht.1.le, ht.2.le.trans hv.2⟩).hasDerivAt
        (Icc_mem_nhds ht.1 (ht.2.trans_le hv.2))
    have hFTC := intervalIntegral.integral_eq_sub_of_continuousOn_hasDerivAt
      hv.1 ((hslice hf u hu).mono (Icc_subset_Icc le_rfl hv.2))
      ((hslice hG u hu).mono (Icc_subset_Icc le_rfl hv.2)) hderiv
    linarith
  have hsecond_interior (u : ℝ) (hu : u ∈ Ioo a a')
      (v : ℝ) (hv : v ∈ Icc b b') :
      fu u v = fu u b + ∫ t in b..v, Gu u t := by
    have huR : u ∈ Icc a a' := ⟨hu.1.le, hu.2.le⟩
    have hvb : b ∈ Icc b b' := ⟨le_rfl, hbb'.le⟩
    have hparam := intervalIntegral.hasDerivAt_integral_of_continuousOn_rectangle
      hu hv hG hGu (by
        intro x hx t ht
        exact (hGu_deriv x ⟨hx.1.le, hx.2.le⟩ t ht).hasDerivAt
          (Icc_mem_nhds hx.1 hx.2))
    have hsum := ((hfu_deriv u huR b hvb).hasDerivAt
      (Icc_mem_nhds hu.1 hu.2)).add hparam
    have heq : (fun x => f x v) =ᶠ[𝓝 u]
        (fun x => f x b + ∫ t in b..v, G x t) := by
      filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
      exact hfirst x ⟨hx.1.le, hx.2.le⟩ v hv
    have hsum' : HasDerivAt
        (fun x => f x b + ∫ t in b..v, G x t)
        (fu u b + ∫ t in b..v, Gu u t) u := by
      have heqfun : ((fun x => f x b) + fun x => ∫ t in b..v, G x t) =
          (fun x => f x b + ∫ t in b..v, G x t) := by
        funext x
        rfl
      rw [heqfun] at hsum
      exact hsum
    exact ((hfu_deriv u huR v hv).hasDerivAt
      (Icc_mem_nhds hu.1 hu.2)).unique
      (hsum'.congr_of_eventuallyEq heq)
  have hsecond (u : ℝ) (hu : u ∈ Icc a a')
      (v : ℝ) (hv : v ∈ Icc b b') :
      fu u v = fu u b + ∫ t in b..v, Gu u t := by
    have hleft : ContinuousOn (fun x => fu x v) (Icc a a') :=
      hfu.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx => ⟨hx, hv⟩)
    have hbase : ContinuousOn (fun x => fu x b) (Icc a a') :=
      hfu.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx => ⟨hx, ⟨le_rfl, hbb'.le⟩⟩)
    have hint := intervalIntegral.continuousOn_integral_of_continuousOn_rectangle hv hGu
    have heq : EqOn (fun x => fu x v)
        (fun x => fu x b + ∫ t in b..v, Gu x t) (Ioo a a') := by
      intro x hx
      exact hsecond_interior x hx v hv
    have hclosure : Icc a a' ⊆ closure (Ioo a a') := by
      rw [closure_Ioo haa'.ne]
    exact (heq.of_subset_closure hleft (hbase.add hint)
      Ioo_subset_Icc_self hclosure) hu
  refine ⟨hfirst, hsecond, ?_⟩
  intro u hu v hv
  have hcont := hslice hGu u hu
  have hint : IntervalIntegrable (Gu u) volume b v :=
    (hcont.mono (Icc_subset_Icc le_rfl hv.2)).intervalIntegrable_of_Icc hv.1
  have hFTC : HasDerivWithinAt
      (fun w => ∫ t in b..w, Gu u t) (Gu u v) (Icc b b') v :=
    @intervalIntegral.integral_hasDerivWithinAt_right ℝ _ _ _ (Gu u) b v hint
      (Icc b b') (Icc b b') (@intervalIntegral.FTCFilter.nhdsIcc v b b' ⟨hv⟩)
      (hcont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc v)
      (hcont v hv)
  have hsum := (hasDerivWithinAt_const (s := Icc b b') (x := v) (c := fu u b)).add hFTC
  have hsum' : HasDerivWithinAt
      (fun w => fu u b + ∫ t in b..w, Gu u t) (Gu u v) (Icc b b') v := by
    have heqfun : ((fun _ : ℝ => fu u b) + fun w => ∫ t in b..w, Gu u t) =
        (fun w => fu u b + ∫ t in b..w, Gu u t) := by
      funext w
      rfl
    rw [heqfun] at hsum
    simpa only [zero_add] using hsum
  exact hsum'.congr (fun w hw => hsecond u hu w hw) (hsecond u hu v hv)

/-- A continuous field of relative vertical derivatives on a nondegenerate rectangle is
the `derivWithin` field and is continuous on the rectangle. -/
theorem continuousOn_derivWithin_vertical_of_continuousOn
    {a a' b b' : ℝ} (hbb' : b < b') {g H : ℝ → ℝ → ℝ}
    (hH : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2)
      (Icc a a' ×ˢ Icc b b'))
    (hderiv : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      HasDerivWithinAt (g u) (H u v) (Icc b b') v) :
    ContinuousOn (fun p : ℝ × ℝ => derivWithin (g p.1) (Icc b b') p.2)
      (Icc a a' ×ˢ Icc b b') := by
  apply hH.congr
  intro p hp
  exact (hderiv p.1 hp.1 p.2 hp.2).derivWithin
    ((uniqueDiffOn_Icc hbb') p.2 hp.2)

/-- The symmetric rectangle theorem: a continuous vertical derivative of the horizontal
partial determines the horizontal derivative of the vertical partial. -/
theorem hasDerivWithinAt_vertical_partial_of_horizontal_partial
    {a a' b b' : ℝ} (haa' : a < a') (hbb' : b < b')
    {f fv H Hv : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Icc a a' ×ˢ Icc b b'))
    (hfv : ContinuousOn (fun p : ℝ × ℝ => fv p.1 p.2)
      (Icc a a' ×ˢ Icc b b'))
    (hH : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2)
      (Icc a a' ×ˢ Icc b b'))
    (hHv : ContinuousOn (fun p : ℝ × ℝ => Hv p.1 p.2)
      (Icc a a' ×ˢ Icc b b'))
    (hfv_deriv : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      HasDerivWithinAt (f u) (fv u v) (Icc b b') v)
    (hH_deriv : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      HasDerivWithinAt (fun x => f x v) (H u v) (Icc a a') u)
    (hHv_deriv : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      HasDerivWithinAt (H u) (Hv u v) (Icc b b') v) :
    (∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      f u v = f a v + ∫ t in a..u, H t v) ∧
    (∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      fv u v = fv a v + ∫ t in a..u, Hv t v) ∧
    (∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      HasDerivWithinAt (fun x => fv x v) (Hv u v) (Icc a a') u) := by
  have hswap {F : ℝ → ℝ → ℝ}
      (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
        (Icc a a' ×ˢ Icc b b')) :
      ContinuousOn (fun p : ℝ × ℝ => F p.2 p.1)
        (Icc b b' ×ˢ Icc a a') := by
    exact hF.comp continuous_swap.continuousOn
      (mapsTo_swap_prod (Icc b b') (Icc a a'))
  have h := hasDerivWithinAt_horizontal_partial_of_vertical_partial
    (a := b) (a' := b') (b := a) (b' := a') hbb' haa'
    (f := fun v u => f u v) (fu := fun v u => fv u v)
    (G := fun v u => H u v) (Gu := fun v u => Hv u v)
    (hswap hf) (hswap hfv) (hswap hH) (hswap hHv)
    (by
      intro v hv u hu
      exact hfv_deriv u hu v hv)
    (by
      intro v hv u hu
      exact hH_deriv u hu v hv)
    (by
      intro v hv u hu
      exact hHv_deriv u hu v hv)
  exact ⟨(fun u hu v hv => h.1 v hv u hu),
    (fun u hu v hv => h.2.1 v hv u hu),
    (fun u hu v hv => h.2.2 v hv u hu)⟩

/-- If `g` is the horizontal partial of `f`, and the vertical partial of `f` has a
continuous horizontal derivative, then the vertical partial of `g` is that derivative. -/
theorem hasDerivWithinAt_vertical_of_horizontal_partial
    {a a' b b' : ℝ} (haa' : a < a') (hbb' : b < b')
    {f g G Gu : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Icc a a' ×ˢ Icc b b'))
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2)
      (Icc a a' ×ˢ Icc b b'))
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2)
      (Icc a a' ×ˢ Icc b b'))
    (hGu : ContinuousOn (fun p : ℝ × ℝ => Gu p.1 p.2)
      (Icc a a' ×ˢ Icc b b'))
    (hg_deriv : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      HasDerivWithinAt (fun x => f x v) (g u v) (Icc a a') u)
    (hG_deriv : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      HasDerivWithinAt (f u) (G u v) (Icc b b') v)
    (hGu_deriv : ∀ u ∈ Icc a a', ∀ v ∈ Icc b b',
      HasDerivWithinAt (fun x => G x v) (Gu u v) (Icc a a') u)
    {u v : ℝ} (hu : u ∈ Icc a a') (hv : v ∈ Icc b b') :
    HasDerivWithinAt (g u) (Gu u v) (Icc b b') v :=
  (hasDerivWithinAt_horizontal_partial_of_vertical_partial haa' hbb'
    hf hg hG hGu hg_deriv hG_deriv hGu_deriv).2.2 u hu v hv
end
