module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.ClosedCoordTriangleJetDistance
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMeanHorizontalJetDifference
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Weighted diagonal means under a three-field sum distance

The third field does not enter the weighted mean. Including it in the maximum
sum distance lets the estimates be used directly for triples of first jets.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- The exact two-input value coefficient for a positive weighted diagonal
error under unit bounds on input differences. -/
@[expose] noncomputable def weightedDiagonalErrorValueDifferenceCoefficient
    (c C B : ℝ) : ℝ :=
  (B + C) / (2 * c) + C * B / (2 * c ^ 2)

/-- The exact common two-input first-derivative coefficient for a positive
weighted diagonal error on a coordinate triangle of diameter at most one. -/
@[expose] noncomputable def weightedDiagonalErrorDerivativeDifferenceCoefficient
    (c C B L : ℝ) : ℝ :=
  let M := weightedDiagonalErrorValueDifferenceCoefficient c C B
  let Aφ := C * B + L * B + C * L
  let AΔ := B + C * M + B + L * (1 + M) + L + C
  max (1 + AΔ / c + Aφ / c ^ 2)
    (1 + (B + C * M) / c + C * B / c ^ 2)

/-- The exact common first-derivative coefficient for a positive weighted
diagonal error on a coordinate triangle of diameter at most one. -/
@[expose] noncomputable def weightedDiagonalErrorDerivativeCoefficient
    (c C B L : ℝ) : ℝ :=
  max (L + (C * B + L * B + C * L) / c) (B + C * B / c)

/-- Value and both coordinate first jets obey the single-input box bounds. -/
theorem weightedDiagonalError_bounds_on_jetBox
    {a b c C B L : ℝ} (hab : a < b) (hsize : b - a ≤ 1)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p ∧ w p ≤ C)
    (hGwU : ∀ p ∈ closedCoordTriangle a b, |Gw p (1, 0)| ≤ L)
    (hGfU : ∀ p ∈ closedCoordTriangle a b, |Gf p (1, 0)| ≤ L)
    (hGfV : ∀ p ∈ closedCoordTriangle a b, |Gf p (0, 1)| ≤ B)
    (hc : 0 < c) (hB : 0 ≤ B) (hL : 0 ≤ L)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |weightedDiagonalError w f p| ≤ B * (p.2 - p.1) ∧
    |(fderivWithin ℝ (weightedDiagonalError w f)
      (closedCoordTriangle a b) p) (1, 0)| ≤
      weightedDiagonalErrorDerivativeCoefficient c C B L ∧
    |(fderivWithin ℝ (weightedDiagonalError w f)
      (closedCoordTriangle a b) p) (0, 1)| ≤
      weightedDiagonalErrorDerivativeCoefficient c C B L := by
  have hjet : ∀ z ∈ closedCoordTriangle a b,
      HasFDerivWithinAt f (Gf z) (closedCoordTriangle a b) z := by
    intro z hz
    exact (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
      (isClosed_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      hf hGf hdf hderivf hz
  have hv := abs_weightedDiagonalError_le_of_jet hw hf
    (fun z hz => (hweight z hz).1) hc hB hjet
    (fun z hz => by simpa only [Real.norm_eq_abs] using hGfV z hz)
    hp.1 hp.2.1 hp.2.2
  have hu := abs_fderivWithin_weightedDiagonalError_horizontal_le hab hsize
    hw hf hGw hGf hdw hdf hderivw hderivf hweight hGwU hGfU hGfV
    hc hB hL hp
  have hv' := abs_fderivWithin_weightedDiagonalError_vertical_le hab
    hw hf hGw hGf hdw hdf hderivw hderivf hweight hGfV hc hB hp
  refine ⟨hv, ?_, ?_⟩
  · exact hu.trans (le_max_left _ _)
  · exact hv'.trans (le_max_right _ _)

/-- Value and both coordinate derivative differences of a weighted diagonal
error are controlled by the maximum of three *sum* distances of first jets. -/
theorem weightedDiagonalError_difference_bounds_threeJetDistanceOn
    {a b c C B L D : ℝ} (hab : a < b) (hsize : b - a ≤ 1)
    {w₁ w₂ g₁ g₂ f₁ f₂ : ℝ × ℝ → ℝ}
    {Gw₁ Gw₂ Gg₁ Gg₂ G₁ G₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw₁ : ContinuousOn w₁ (closedCoordTriangle a b))
    (hw₂ : ContinuousOn w₂ (closedCoordTriangle a b))
    (_hg₁ : ContinuousOn g₁ (closedCoordTriangle a b))
    (_hg₂ : ContinuousOn g₂ (closedCoordTriangle a b))
    (hf₁ : ContinuousOn f₁ (closedCoordTriangle a b))
    (hf₂ : ContinuousOn f₂ (closedCoordTriangle a b))
    (hGw₁ : ContinuousOn Gw₁ (closedCoordTriangle a b))
    (hGw₂ : ContinuousOn Gw₂ (closedCoordTriangle a b))
    (_hGg₁ : ContinuousOn Gg₁ (closedCoordTriangle a b))
    (_hGg₂ : ContinuousOn Gg₂ (closedCoordTriangle a b))
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
    (hG₁U : ∀ p ∈ closedCoordTriangle a b, |G₁ p (1, 0)| ≤ L)
    (hG₂U : ∀ p ∈ closedCoordTriangle a b, |G₂ p (1, 0)| ≤ L)
    (hG₁V : ∀ p ∈ closedCoordTriangle a b, |G₁ p (0, 1)| ≤ B)
    (hG₂V : ∀ p ∈ closedCoordTriangle a b, |G₂ p (0, 1)| ≤ B)
    (hc : 0 < c) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hD : D = threeJetDistanceOn (closedCoordTriangle a b)
      w₁ w₂ g₁ g₂ f₁ f₂ Gw₁ Gw₂ Gg₁ Gg₂ G₁ G₂)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |weightedDiagonalError w₁ f₁ p - weightedDiagonalError w₂ f₂ p| ≤
      weightedDiagonalErrorValueDifferenceCoefficient c C B * (p.2 - p.1) * D ∧
    |(fderivWithin ℝ (weightedDiagonalError w₁ f₁)
        (closedCoordTriangle a b) p) (1, 0) -
      (fderivWithin ℝ (weightedDiagonalError w₂ f₂)
        (closedCoordTriangle a b) p) (1, 0)| ≤
      weightedDiagonalErrorDerivativeDifferenceCoefficient c C B L * D ∧
    |(fderivWithin ℝ (weightedDiagonalError w₁ f₁)
        (closedCoordTriangle a b) p) (0, 1) -
      (fderivWithin ℝ (weightedDiagonalError w₂ f₂)
        (closedCoordTriangle a b) p) (0, 1)| ≤
      weightedDiagonalErrorDerivativeDifferenceCoefficient c C B L * D := by
  let K := closedCoordTriangle a b
  have hK : IsCompact K := isCompact_closedCoordTriangle a b
  have hne : K.Nonempty := by
    refine ⟨(a, a), ?_⟩
    exact ⟨le_rfl, le_rfl, hab.le⟩
  have hDw : coordinateJetDistanceOn K w₁ w₂ Gw₁ Gw₂ ≤ D := by
    rw [hD]
    exact coordinateJetDistanceOn_first_le_threeJetDistanceOn K
      w₁ w₂ g₁ g₂ f₁ f₂ Gw₁ Gw₂ Gg₁ Gg₂ G₁ G₂
  have hDf : coordinateJetDistanceOn K f₁ f₂ G₁ G₂ ≤ D := by
    rw [hD]
    exact coordinateJetDistanceOn_third_le_threeJetDistanceOn K
      w₁ w₂ g₁ g₂ f₁ f₂ Gw₁ Gw₂ Gg₁ Gg₂ G₁ G₂
  have hDnonneg : 0 ≤ D :=
    (coordinateJetDistanceOn_nonneg hK hne hw₁ hw₂ hGw₁ hGw₂).trans hDw
  have hwdiff : ∀ z ∈ K, |w₁ z - w₂ z| ≤ D := by
    intro z hz
    exact (abs_value_sub_le_coordinateJetDistanceOn hK hne
      hw₁ hw₂ hGw₁ hGw₂ hz).trans hDw
  have hGwUDiff : ∀ z ∈ K, |Gw₁ z (1, 0) - Gw₂ z (1, 0)| ≤ D := by
    intro z hz
    exact (abs_horizontal_sub_le_coordinateJetDistanceOn hK hne
      hw₁ hw₂ hGw₁ hGw₂ hz).trans hDw
  have hGUDiff : ∀ z ∈ K, |G₁ z (1, 0) - G₂ z (1, 0)| ≤ D := by
    intro z hz
    exact (abs_horizontal_sub_le_coordinateJetDistanceOn hK hne
      hf₁ hf₂ hG₁ hG₂ hz).trans hDf
  have hGVDiff : ∀ z ∈ K, |G₁ z (0, 1) - G₂ z (0, 1)| ≤ D := by
    intro z hz
    exact (abs_vertical_sub_le_coordinateJetDistanceOn hK hne
      hf₁ hf₂ hG₁ hG₂ hz).trans hDf
  have hjet₁ : ∀ z ∈ K, HasFDerivWithinAt f₁ (G₁ z) K z := by
    intro z hz
    exact (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
      (isClosed_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      hf₁ hG₁ hdf₁ hderiv₁ hz
  have hjet₂ : ∀ z ∈ K, HasFDerivWithinAt f₂ (G₂ z) K z := by
    intro z hz
    exact (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
      (isClosed_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      hf₂ hG₂ hdf₂ hderiv₂ hz
  have hpoint : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
  let M := weightedDiagonalErrorValueDifferenceCoefficient c C B
  let U := 1 + (B + C * M + B + L * (1 + M) + L + C) / c +
    (C * B + L * B + C * L) / c ^ 2
  let V := 1 + (B + C * M) / c + C * B / c ^ 2
  have hMval : M = (B + C) / (2 * c) + C * B / (2 * c ^ 2) := rfl
  have hcoef : weightedDiagonalErrorDerivativeDifferenceCoefficient c C B L =
      max U V := rfl
  have hH : |weightedDiagonalError w₁ f₁ p - weightedDiagonalError w₂ f₂ p| ≤
      M * (p.2 - p.1) * D := by
    exact abs_weightedDiagonalError_sub_le_of_jets hc hDnonneg hw₁ hw₂ hf₁ hf₂
      (fun z hz => (hweight₁ z hz).1) hweight₂ hwdiff
      hjet₁ hjet₂ hG₁V hG₂V hGVDiff hpoint.1 hpoint.2.1 hpoint.2.2
  have hU : |(fderivWithin ℝ (weightedDiagonalError w₁ f₁) K p) (1, 0) -
      (fderivWithin ℝ (weightedDiagonalError w₂ f₂) K p) (1, 0)| ≤ U * D := by
    simpa only [U, M, weightedDiagonalErrorValueDifferenceCoefficient] using
      abs_fderivWithin_weightedDiagonalError_horizontal_sub_le hab hsize
        hw₁ hw₂ hf₁ hf₂ hGw₁ hGw₂ hG₁ hG₂ hdw₁ hdw₂ hdf₁ hdf₂
        hderivw₁ hderivw₂ hderiv₁ hderiv₂ hweight₁ hweight₂ hwdiff
        hGw₁U hGw₂U hG₁U hG₂U hG₁V hG₂V hGwUDiff hGUDiff hGVDiff
        hc hB hL hDnonneg hp
  have hV : |(fderivWithin ℝ (weightedDiagonalError w₁ f₁) K p) (0, 1) -
      (fderivWithin ℝ (weightedDiagonalError w₂ f₂) K p) (0, 1)| ≤ V * D := by
    simpa only [V, M, weightedDiagonalErrorValueDifferenceCoefficient] using
      abs_fderivWithin_weightedDiagonalError_vertical_sub_le hab
        hw₁ hw₂ hf₁ hf₂ hGw₁ hGw₂ hG₁ hG₂ hdw₁ hdw₂ hdf₁ hdf₂
        hderivw₁ hderivw₂ hderiv₁ hderiv₂ hweight₁ hweight₂ hwdiff
        hG₁V hG₂V hGVDiff hc hB hDnonneg hp
  refine ⟨hH, ?_, ?_⟩
  · rw [hcoef]
    exact hU.trans (mul_le_mul_of_nonneg_right (le_max_left U V) hDnonneg)
  · rw [hcoef]
    exact hV.trans (mul_le_mul_of_nonneg_right (le_max_right U V) hDnonneg)

end intervalIntegral

end
