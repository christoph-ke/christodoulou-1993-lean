module

public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamState
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic

/-!
# Linear outgoing propagation across the Route B seam

After the prescribed and scalar values agree, the remaining outgoing fields
are propagated by linear equations along the shared characteristic. This
lemma accepts relative jets on the two different closed regions and includes
the upper endpoint by continuity.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Matching corner values and the same affine linear outgoing equation
force two C¹ traces to agree on the full closed lower/axis edge. -/
theorem routeB_vertical_trace_eq_of_linear_source
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    {fLow fAx : ℝ × ℝ → ℝ} {A B : ℝ → ℝ}
    (hLow : ContDiffOn ℝ 1 fLow (routeBLowerRegion a vStar b))
    (hAx : ContDiffOn ℝ 1 fAx (closedCoordTriangle a b))
    (hA : ContinuousOn A (Icc vStar b))
    (hLowV : ∀ v ∈ Ico vStar b,
      (fderivWithin ℝ fLow (routeBLowerRegion a vStar b) (a, v)) (0, 1) =
        A v * fLow (a, v) + B v)
    (hAxV : ∀ v ∈ Ico vStar b,
      (fderivWithin ℝ fAx (closedCoordTriangle a b) (a, v)) (0, 1) =
        A v * fAx (a, v) + B v)
    (hCorner : fLow (a, vStar) = fAx (a, vStar)) :
    ∀ v ∈ Icc vStar b, fLow (a, v) = fAx (a, v) := by
  have hmapLow : MapsTo (fun t : ℝ => (a, t)) (Icc vStar b)
      (routeBLowerRegion a vStar b) :=
    fun _ ht => ⟨⟨ha.le, le_rfl⟩, ht⟩
  have hmapAx : MapsTo (fun t : ℝ => (a, t)) (Icc vStar b)
      (closedCoordTriangle a b) :=
    fun _ ht => ⟨le_rfl, haStar.le.trans ht.1, ht.2⟩
  have hLowCont : ContinuousOn (fun v => fLow (a, v)) (Icc vStar b) :=
    hLow.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      hmapLow
  have hAxCont : ContinuousOn (fun v => fAx (a, v)) (Icc vStar b) :=
    hAx.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      hmapAx
  let e : ℝ → ℝ := fun v => fLow (a, v) - fAx (a, v)
  have he : ContinuousOn e (Icc vStar b) := hLowCont.sub hAxCont
  have heCorner : e vStar = 0 := sub_eq_zero.mpr hCorner
  have heDeriv : ∀ v ∈ Ico vStar b,
      HasDerivWithinAt e (A v * e v) (Ici v) v := by
    intro v hv
    have hpair : HasDerivAt (fun t : ℝ => (a, t)) (0, 1) v :=
      (hasDerivAt_const v a).prodMk (hasDerivAt_id' v)
    have hLowFd := (hLow.differentiableOn (by norm_num) (a, v)
      ⟨⟨ha.le, le_rfl⟩, ⟨hv.1, hv.2.le⟩⟩).hasFDerivWithinAt
    have hAxFd := (hAx.differentiableOn (by norm_num) (a, v)
      ⟨le_rfl, haStar.le.trans hv.1, hv.2.le⟩).hasFDerivWithinAt
    have hLowSlice : HasDerivWithinAt (fun t => fLow (a, t))
        (A v * fLow (a, v) + B v) (Icc vStar b) v := by
      simpa only [Function.comp_def, hLowV v hv] using
        hLowFd.comp_hasDerivWithinAt v hpair.hasDerivWithinAt hmapLow
    have hAxSlice : HasDerivWithinAt (fun t => fAx (a, t))
        (A v * fAx (a, v) + B v) (Icc vStar b) v := by
      simpa only [Function.comp_def, hAxV v hv] using
        hAxFd.comp_hasDerivWithinAt v hpair.hasDerivWithinAt hmapAx
    have hdiff := hLowSlice.sub hAxSlice
    have hdiff' : HasDerivWithinAt e (A v * e v) (Icc vStar b) v := by
      convert hdiff using 1
      dsimp [e]
      ring
    exact hdiff'.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hv)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  have hbound : ∀ v ∈ Ico vStar b,
      ‖A v * e v‖ ≤ max M 0 * ‖e v‖ := by
    intro v hv
    have hAv : ‖A v‖ ≤ M := hM v ⟨hv.1, hv.2.le⟩
    calc
      ‖A v * e v‖ = ‖A v‖ * ‖e v‖ := norm_mul _ _
      _ ≤ M * ‖e v‖ := mul_le_mul_of_nonneg_right hAv (norm_nonneg _)
      _ ≤ max M 0 * ‖e v‖ :=
        mul_le_mul_of_nonneg_right (le_max_left M 0) (norm_nonneg _)
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    he heDeriv heCorner hbound
  intro v hv
  exact sub_eq_zero.mp (hzero v hv)

end ChristodoulouBV.Uniqueness

end
