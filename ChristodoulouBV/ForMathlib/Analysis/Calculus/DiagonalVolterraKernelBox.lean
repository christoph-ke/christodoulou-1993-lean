module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraKernelEstimates
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Box estimates for quadratic diagonal kernels

The first-jet estimates for a weighted diagonal error are assembled into
two-input estimates for its quadratic product. The distance is the maximum
of three uniform first-jet sum distances on a closed coordinate triangle.
-/

public section

open Set

namespace intervalIntegral

/-- On a bounded three-jet box, the quadratic kernel has the exact two-input
value and coordinate derivative coefficients. The middle field participates
only in the common distance. -/
theorem weightedDiagonalQuadraticKernel_difference_bounds_threeJetDistanceOn
    {a b c C B L D : ℝ} (hab : a < b) (hsize : b - a ≤ 1)
    {w₁ w₂ g₁ g₂ f₁ f₂ : ℝ × ℝ → ℝ}
    {Gw₁ Gw₂ Gg₁ Gg₂ G₁ G₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw₁ : ContinuousOn w₁ (closedCoordTriangle a b))
    (hw₂ : ContinuousOn w₂ (closedCoordTriangle a b))
    (hg₁ : ContinuousOn g₁ (closedCoordTriangle a b))
    (hg₂ : ContinuousOn g₂ (closedCoordTriangle a b))
    (hf₁ : ContinuousOn f₁ (closedCoordTriangle a b))
    (hf₂ : ContinuousOn f₂ (closedCoordTriangle a b))
    (hGw₁ : ContinuousOn Gw₁ (closedCoordTriangle a b))
    (hGw₂ : ContinuousOn Gw₂ (closedCoordTriangle a b))
    (hGg₁ : ContinuousOn Gg₁ (closedCoordTriangle a b))
    (hGg₂ : ContinuousOn Gg₂ (closedCoordTriangle a b))
    (hG₁ : ContinuousOn G₁ (closedCoordTriangle a b))
    (hG₂ : ContinuousOn G₂ (closedCoordTriangle a b))
    (hdw₁ : DifferentiableOn ℝ w₁ (interior (closedCoordTriangle a b)))
    (hdw₂ : DifferentiableOn ℝ w₂ (interior (closedCoordTriangle a b)))
    (hdf₁ : DifferentiableOn ℝ f₁ (interior (closedCoordTriangle a b)))
    (hdf₂ : DifferentiableOn ℝ f₂ (interior (closedCoordTriangle a b)))
    (hderivw₁ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w₁ p = Gw₁ p)
    (hderivw₂ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w₂ p = Gw₂ p)
    (hderiv₁ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f₁ p = G₁ p)
    (hderiv₂ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f₂ p = G₂ p)
    (hweight₁ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₁ p ∧ w₁ p ≤ C)
    (hweight₂ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₂ p ∧ w₂ p ≤ C)
    (hGw₁U : ∀ p ∈ closedCoordTriangle a b, |Gw₁ p (1, 0)| ≤ L)
    (hGw₂U : ∀ p ∈ closedCoordTriangle a b, |Gw₂ p (1, 0)| ≤ L)
    (hGw₂V : ∀ p ∈ closedCoordTriangle a b, |Gw₂ p (0, 1)| ≤ L)
    (hG₁U : ∀ p ∈ closedCoordTriangle a b, |G₁ p (1, 0)| ≤ L)
    (hG₂U : ∀ p ∈ closedCoordTriangle a b, |G₂ p (1, 0)| ≤ L)
    (hG₁V : ∀ p ∈ closedCoordTriangle a b, |G₁ p (0, 1)| ≤ B)
    (hG₂V : ∀ p ∈ closedCoordTriangle a b, |G₂ p (0, 1)| ≤ B)
    (hc : 0 < c) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hD : D = threeJetDistanceOn (closedCoordTriangle a b)
      w₁ w₂ g₁ g₂ f₁ f₂ Gw₁ Gw₂ Gg₁ Gg₂ G₁ G₂)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |weightedDiagonalQuadraticKernel w₁ f₁ p -
      weightedDiagonalQuadraticKernel w₂ f₂ p| ≤
      weightedDiagonalQuadraticValueDifferenceCoefficient c C B *
        (p.2 - p.1) ^ 2 * D ∧
    |(fderivWithin ℝ (weightedDiagonalQuadraticKernel w₁ f₁)
        (closedCoordTriangle a b) p) (1, 0) -
      (fderivWithin ℝ (weightedDiagonalQuadraticKernel w₂ f₂)
        (closedCoordTriangle a b) p) (1, 0)| ≤
      weightedDiagonalQuadraticDerivativeDifferenceCoefficient c C B L *
        (p.2 - p.1) * D ∧
    |(fderivWithin ℝ (weightedDiagonalQuadraticKernel w₁ f₁)
        (closedCoordTriangle a b) p) (0, 1) -
      (fderivWithin ℝ (weightedDiagonalQuadraticKernel w₂ f₂)
        (closedCoordTriangle a b) p) (0, 1)| ≤
      weightedDiagonalQuadraticDerivativeDifferenceCoefficient c C B L *
        (p.2 - p.1) * D := by
  let K := closedCoordTriangle a b
  have hK : IsCompact K := isCompact_closedCoordTriangle a b
  have hne : K.Nonempty := by
    refine ⟨(a, a), ?_⟩
    exact ⟨le_rfl, le_rfl, hab.le⟩
  have hDw : coordinateJetDistanceOn K w₁ w₂ Gw₁ Gw₂ ≤ D := by
    rw [hD]
    exact coordinateJetDistanceOn_first_le_threeJetDistanceOn K
      w₁ w₂ g₁ g₂ f₁ f₂ Gw₁ Gw₂ Gg₁ Gg₂ G₁ G₂
  have hDnonneg : 0 ≤ D :=
    (coordinateJetDistanceOn_nonneg hK hne hw₁ hw₂ hGw₁ hGw₂).trans hDw
  have hwdiff : |w₁ p - w₂ p| ≤ D :=
    (abs_value_sub_le_coordinateJetDistanceOn hK hne
      hw₁ hw₂ hGw₁ hGw₂ hp).trans hDw
  have hGwUDiff : |Gw₁ p (1, 0) - Gw₂ p (1, 0)| ≤ D :=
    (abs_horizontal_sub_le_coordinateJetDistanceOn hK hne
      hw₁ hw₂ hGw₁ hGw₂ hp).trans hDw
  have hGwVDiff : |Gw₁ p (0, 1) - Gw₂ p (0, 1)| ≤ D :=
    (abs_vertical_sub_le_coordinateJetDistanceOn hK hne
      hw₁ hw₂ hGw₁ hGw₂ hp).trans hDw
  have hH₁ := weightedDiagonalError_bounds_on_jetBox hab hsize
    hw₁ hf₁ hGw₁ hG₁ hdw₁ hdf₁ hderivw₁ hderiv₁
    hweight₁ hGw₁U hG₁U hG₁V hc hB hL hp
  have hH₂ := weightedDiagonalError_bounds_on_jetBox hab hsize
    hw₂ hf₂ hGw₂ hG₂ hdw₂ hdf₂ hderivw₂ hderiv₂
    hweight₂ hGw₂U hG₂U hG₂V hc hB hL hp
  have hHdiff := weightedDiagonalError_difference_bounds_threeJetDistanceOn
    hab hsize hw₁ hw₂ hg₁ hg₂ hf₁ hf₂ hGw₁ hGw₂ hGg₁ hGg₂ hG₁ hG₂
    hdw₁ hdw₂ hdf₁ hdf₂ hderivw₁ hderivw₂ hderiv₁ hderiv₂
    hweight₁ hweight₂ hGw₁U hGw₂U hG₁U hG₂U hG₁V hG₂V
    hc hB hL hD hp
  have hjetw₁ : ∀ z ∈ K, HasFDerivWithinAt w₁ (Gw₁ z) K z := by
    intro z hz
    exact (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
      (isClosed_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      hw₁ hGw₁ hdw₁ hderivw₁ hz
  have hjetw₂ : ∀ z ∈ K, HasFDerivWithinAt w₂ (Gw₂ z) K z := by
    intro z hz
    exact (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
      (isClosed_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      hw₂ hGw₂ hdw₂ hderivw₂ hz
  have hC1₁ := contDiffOn_weightedDiagonalError hab hw₁ hf₁ hGw₁ hG₁
    hdw₁ hdf₁ hderivw₁ hderiv₁ (fun z hz => (hweight₁ z hz).1) hc
  have hC1₂ := contDiffOn_weightedDiagonalError hab hw₂ hf₂ hGw₂ hG₂
    hdw₂ hdf₂ hderivw₂ hderiv₂ (fun z hz => (hweight₂ z hz).1) hc
  have hjet₂ := weightedDiagonalQuadraticKernel_bounds_on_jetBox hab hsize
    hw₂ hf₂ hGw₂ hG₂ hdw₂ hdf₂ hderivw₂ hderiv₂ hweight₂
    hGw₂U hGw₂V hG₂U hG₂V hc hB hL hp
  have hC : 0 ≤ C := (hc.le.trans (hweight₂ p hp).1).trans (hweight₂ p hp).2
  have hw₂abs : |w₂ p| ≤ C := by
    rw [abs_of_nonneg (hc.le.trans (hweight₂ p hp).1)]
    exact (hweight₂ p hp).2
  have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := by
    simpa only [closedCoordTriangle, Set.mem_ofPred_eq] using hp
  have hd : 0 ≤ p.2 - p.1 := sub_nonneg.mpr hcoord.2.1
  have hdle : p.2 - p.1 ≤ 1 := by
    linarith
  have hval := abs_weightedDiagonalQuadraticKernel_sub_le_of_bounds
    hC hB (show 0 ≤ weightedDiagonalErrorValueDifferenceCoefficient c C B by
      dsimp [weightedDiagonalErrorValueDifferenceCoefficient]
      positivity) hDnonneg hd hw₂abs hwdiff hH₁.1 hH₂.1 hHdiff.1
  refine ⟨?_, ?_, ?_⟩
  · simpa only [weightedDiagonalQuadraticValueDifferenceCoefficient] using hval
  · have h := abs_fderivWithin_weightedDiagonalQuadraticKernel_sub_le_of_bounds
      hab hjetw₁ hjetw₂ hC1₁ hC1₂ hB hC hL
      (show 0 ≤ weightedDiagonalErrorValueDifferenceCoefficient c C B by
        dsimp [weightedDiagonalErrorValueDifferenceCoefficient]
        positivity) hDnonneg hp hdle hw₂abs hwdiff (hGw₂U p hp) hGwUDiff
      hH₁.1 hH₂.1 hHdiff.1 hH₁.2.1 hHdiff.2.1
    simpa only [weightedDiagonalQuadraticDerivativeDifferenceCoefficient,
      weightedDiagonalErrorDerivativeCoefficient,
      weightedDiagonalErrorValueDifferenceCoefficient,
      weightedDiagonalErrorDerivativeDifferenceCoefficient] using h
  · have h := abs_fderivWithin_weightedDiagonalQuadraticKernel_sub_le_of_bounds
      hab hjetw₁ hjetw₂ hC1₁ hC1₂ hB hC hL
      (show 0 ≤ weightedDiagonalErrorValueDifferenceCoefficient c C B by
        dsimp [weightedDiagonalErrorValueDifferenceCoefficient]
        positivity) hDnonneg hp hdle hw₂abs hwdiff (hGw₂V p hp) hGwVDiff
      hH₁.1 hH₂.1 hHdiff.1 hH₁.2.2 hHdiff.2.2
    simpa only [weightedDiagonalQuadraticDerivativeDifferenceCoefficient,
      weightedDiagonalErrorDerivativeCoefficient,
      weightedDiagonalErrorValueDifferenceCoefficient,
      weightedDiagonalErrorDerivativeDifferenceCoefficient] using h

end intervalIntegral

end
