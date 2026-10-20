module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.ClosedConvexJet

/-!
# C¹ regularity from a continuous interior derivative on an interval

A continuous interior first derivative determines the relative derivative at
both endpoints of a compact interval.
-/

public section

open Set

/-- A continuous value and a continuous derivative on a closed interval,
whose interior values satisfy the derivative equation, form a relative `C¹`
function on the whole interval. -/
theorem contDiffOn_one_Icc_of_continuousOn_hasDerivAt_Ioo
    {a b : ℝ} (hab : a < b) {f d : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hd : ContinuousOn d (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (d x) x) :
    ContDiffOn ℝ 1 f (Icc a b) := by
  let L : ℝ → ℝ →L[ℝ] ℝ :=
    fun x => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) x
  have hL : Continuous L :=
    (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous
  let G : ℝ → ℝ →L[ℝ] ℝ := fun x => L (d x)
  have hG : ContinuousOn G (Icc a b) := hL.comp_continuousOn hd
  have hinside : (interior (Icc a b)).Nonempty := by
    rw [interior_Icc]
    exact Set.nonempty_Ioo.mpr hab
  apply (convex_Icc a b).contDiffOn_one_of_continuousOn_fderiv
    isClosed_Icc hinside hf hG
  · intro x hx
    have hx' : x ∈ Ioo a b := by simpa only [interior_Icc] using hx
    exact (hderiv x hx').differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Ioo a b := by simpa only [interior_Icc] using hx
    have heq : ContinuousLinearMap.toSpanSingleton ℝ (d x) = G x := by
      ext
      simp [G, L]
    exact (hderiv x hx').hasFDerivAt.fderiv.trans heq

end
