module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraPrimitiveBounds
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Box estimates for diagonal Volterra primitives

The three-coordinate primitive inherits the exact half-square value bounds
and the first-jet bounds from the quotient kernel on a positive three-jet
box. The horizontal jet retains the sharper interval length `v-w`.
-/

public section

open Set

namespace intervalIntegral

/-- The Volterra primitive and its three continuous jet candidates satisfy
the two-input box estimates. The horizontal bounds use the exact integration
length, while the upper and lower endpoint jets are kernel evaluations. -/
theorem weightedDiagonalVolterraPrimitive_jet_bounds_threeJetDistanceOn
    {a b c C B L D : ℝ} (hab : a < b) (hsize : b - a ≤ 1)
    {w₁ w₂ g₁ g₂ f₁ f₂ : ℝ × ℝ → ℝ}
    {Gw₁ Gw₂ Gg₁ Gg₂ Gf₁ Gf₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
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
    (hGf₁ : ContinuousOn Gf₁ (closedCoordTriangle a b))
    (hGf₂ : ContinuousOn Gf₂ (closedCoordTriangle a b))
    (hdw₁ : DifferentiableOn ℝ w₁ (interior (closedCoordTriangle a b)))
    (hdw₂ : DifferentiableOn ℝ w₂ (interior (closedCoordTriangle a b)))
    (hdf₁ : DifferentiableOn ℝ f₁ (interior (closedCoordTriangle a b)))
    (hdf₂ : DifferentiableOn ℝ f₂ (interior (closedCoordTriangle a b)))
    (hderivw₁ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w₁ p = Gw₁ p)
    (hderivw₂ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w₂ p = Gw₂ p)
    (hderivf₁ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f₁ p = Gf₁ p)
    (hderivf₂ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f₂ p = Gf₂ p)
    (hweight₁ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₁ p ∧ w₁ p ≤ C)
    (hweight₂ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₂ p ∧ w₂ p ≤ C)
    (hGw₁U : ∀ p ∈ closedCoordTriangle a b, |Gw₁ p (1, 0)| ≤ L)
    (hGw₂U : ∀ p ∈ closedCoordTriangle a b, |Gw₂ p (1, 0)| ≤ L)
    (hGw₁V : ∀ p ∈ closedCoordTriangle a b, |Gw₁ p (0, 1)| ≤ L)
    (hGw₂V : ∀ p ∈ closedCoordTriangle a b, |Gw₂ p (0, 1)| ≤ L)
    (hGf₁U : ∀ p ∈ closedCoordTriangle a b, |Gf₁ p (1, 0)| ≤ L)
    (hGf₂U : ∀ p ∈ closedCoordTriangle a b, |Gf₂ p (1, 0)| ≤ L)
    (hGf₁V : ∀ p ∈ closedCoordTriangle a b, |Gf₁ p (0, 1)| ≤ B)
    (hGf₂V : ∀ p ∈ closedCoordTriangle a b, |Gf₂ p (0, 1)| ≤ B)
    (hc : 0 < c) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hD : D = threeJetDistanceOn (closedCoordTriangle a b)
      w₁ w₂ g₁ g₂ f₁ f₂ Gw₁ Gw₂ Gg₁ Gg₂ Gf₁ Gf₂)
    {u lower upper : ℝ} (hu : a ≤ u) (hulower : u ≤ lower)
    (hlowerupper : lower ≤ upper) (hupper : upper ≤ b) :
    (0 ≤ weightedDiagonalVolterraPrimitive w₁ f₁ u lower upper ∧
      weightedDiagonalVolterraPrimitive w₁ f₁ u lower upper ≤
        weightedDiagonalQuotientValueCoefficient c C B * (upper - u) ^ 2 / 2) ∧
    |weightedDiagonalVolterraPrimitive w₁ f₁ u lower upper -
      weightedDiagonalVolterraPrimitive w₂ f₂ u lower upper| ≤
      weightedDiagonalQuotientValueDifferenceCoefficient c C B *
        (upper - u) ^ 2 * D / 2 ∧
    |verticalVolterraFirstJet
      (fderivWithin ℝ (weightedDiagonalQuotientKernel w₁ f₁)
        (closedCoordTriangle a b)) ((u, lower), upper)| ≤
      weightedDiagonalQuotientDerivativeCoefficient c C B L (C + L) *
        (upper - lower) ∧
    |verticalVolterraFirstJet
        (fderivWithin ℝ (weightedDiagonalQuotientKernel w₁ f₁)
          (closedCoordTriangle a b)) ((u, lower), upper) -
      verticalVolterraFirstJet
        (fderivWithin ℝ (weightedDiagonalQuotientKernel w₂ f₂)
          (closedCoordTriangle a b)) ((u, lower), upper)| ≤
      weightedDiagonalQuotientDerivativeDifferenceCoefficient
        c C B L (C + L) 2 * (upper - lower) * D ∧
    |weightedDiagonalQuotientKernel w₁ f₁ (u, upper)| ≤
      weightedDiagonalQuotientValueCoefficient c C B * (upper - u) ∧
    |weightedDiagonalQuotientKernel w₁ f₁ (u, upper) -
      weightedDiagonalQuotientKernel w₂ f₂ (u, upper)| ≤
      weightedDiagonalQuotientValueDifferenceCoefficient c C B * (upper - u) * D ∧
    |weightedDiagonalQuotientKernel w₁ f₁ (u, lower)| ≤
      weightedDiagonalQuotientValueCoefficient c C B * (lower - u) ∧
    |weightedDiagonalQuotientKernel w₁ f₁ (u, lower) -
      weightedDiagonalQuotientKernel w₂ f₂ (u, lower)| ≤
      weightedDiagonalQuotientValueDifferenceCoefficient c C B * (lower - u) * D := by
  let K := closedCoordTriangle a b
  let k₁ := weightedDiagonalQuotientKernel w₁ f₁
  let k₂ := weightedDiagonalQuotientKernel w₂ f₂
  let G₁ := fderivWithin ℝ k₁ K
  let G₂ := fderivWithin ℝ k₂ K
  let k₀ := weightedDiagonalQuotientValueCoefficient c C B
  let k₁c := weightedDiagonalQuotientDerivativeCoefficient c C B L (C + L)
  let kΔ₀ := weightedDiagonalQuotientValueDifferenceCoefficient c C B
  let kΔ₁ := weightedDiagonalQuotientDerivativeDifferenceCoefficient
    c C B L (C + L) 2
  have hC : 0 ≤ C := by
    have hp : (u, u) ∈ K := ⟨hu, le_rfl, hulower.trans (hlowerupper.trans hupper)⟩
    exact (hc.le.trans (hweight₁ _ hp).1).trans (hweight₁ _ hp).2
  have hk₀ : 0 ≤ k₀ := by
    dsimp [k₀, weightedDiagonalQuotientValueCoefficient]
    positivity
  have hkΔ₀ : 0 ≤ kΔ₀ := by
    dsimp [kΔ₀, weightedDiagonalQuotientValueDifferenceCoefficient,
      weightedDiagonalQuadraticValueCoefficient,
      weightedDiagonalQuadraticValueDifferenceCoefficient,
      weightedDiagonalErrorValueDifferenceCoefficient]
    positivity
  have hK : IsCompact K := isCompact_closedCoordTriangle a b
  have hne : K.Nonempty := by
    refine ⟨(a, a), ?_⟩
    exact ⟨le_rfl, le_rfl, hab.le⟩
  have hDw : coordinateJetDistanceOn K w₁ w₂ Gw₁ Gw₂ ≤ D := by
    rw [hD]
    exact coordinateJetDistanceOn_first_le_threeJetDistanceOn K
      w₁ w₂ g₁ g₂ f₁ f₂ Gw₁ Gw₂ Gg₁ Gg₂ Gf₁ Gf₂
  have hDnonneg : 0 ≤ D :=
    (coordinateJetDistanceOn_nonneg hK hne hw₁ hw₂ hGw₁ hGw₂).trans hDw
  have hC1₁ := contDiffOn_weightedDiagonalQuotientKernel hab
    hw₁ hf₁ hGw₁ hGf₁ hdw₁ hdf₁ hderivw₁ hderivf₁
    (fun z hz => (hweight₁ z hz).1) hc
  have hC1₂ := contDiffOn_weightedDiagonalQuotientKernel hab
    hw₂ hf₂ hGw₂ hGf₂ hdw₂ hdf₂ hderivw₂ hderivf₂
    (fun z hz => (hweight₂ z hz).1) hc
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hk₁cont : ContinuousOn k₁ K := hC1₁.continuousOn
  have hk₂cont : ContinuousOn k₂ K := hC1₂.continuousOn
  have hG₁cont : ContinuousOn G₁ K :=
    hC1₁.continuousOn_fderivWithin hunique (by norm_num)
  have hG₂cont : ContinuousOn G₂ K :=
    hC1₂.continuousOn_fderivWithin hunique (by norm_num)
  have hjetf₁ : ∀ z ∈ K, HasFDerivWithinAt f₁ (Gf₁ z) K z := by
    intro z hz
    exact (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
      (isClosed_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      hf₁ hGf₁ hdf₁ hderivf₁ hz
  have hk₁bound : ∀ z ∈ K, 0 ≤ k₁ z ∧ k₁ z ≤ k₀ * (z.2 - z.1) := by
    intro z hz
    exact weightedDiagonalQuotientKernel_bounds_on_jetBox hw₁ hf₁ hweight₁
      hc hB hjetf₁ hGf₁V hz
  have hkdiff : ∀ z ∈ K, |k₁ z - k₂ z| ≤ kΔ₀ * (z.2 - z.1) * D := by
    intro z hz
    exact (weightedDiagonalQuotientKernel_difference_bounds_threeJetDistanceOn
      hab hsize hw₁ hw₂ hg₁ hg₂ hf₁ hf₂ hGw₁ hGw₂ hGg₁ hGg₂ hGf₁ hGf₂
      hdw₁ hdw₂ hdf₁ hdf₂ hderivw₁ hderivw₂ hderivf₁ hderivf₂
      hweight₁ hweight₂ hGw₁U hGw₂U hGw₂V hGf₁U hGf₂U hGf₁V hGf₂V
      hc hB hL hD hz).1
  have hG₁bound : ∀ z ∈ K, |G₁ z (1, 0)| ≤ k₁c := by
    intro z hz
    exact (weightedDiagonalQuotientKernel_derivative_bounds_on_jetBox
      hab hsize hw₁ hf₁ hGw₁ hGf₁ hdw₁ hdf₁ hderivw₁ hderivf₁
      hweight₁ hGw₁U hGw₁V hGf₁U hGf₁V hc hB hL hz).1
  have hGdiff : ∀ z ∈ K, |G₁ z (1, 0) - G₂ z (1, 0)| ≤ kΔ₁ * D := by
    intro z hz
    exact (weightedDiagonalQuotientKernel_difference_bounds_threeJetDistanceOn
      hab hsize hw₁ hw₂ hg₁ hg₂ hf₁ hf₂ hGw₁ hGw₂ hGg₁ hGg₂ hGf₁ hGf₂
      hdw₁ hdw₂ hdf₁ hdf₂ hderivw₁ hderivw₂ hderivf₁ hderivf₂
      hweight₁ hweight₂ hGw₁U hGw₂U hGw₂V hGf₁U hGf₂U hGf₁V hGf₂V
      hc hB hL hD hz).2.1
  have h := verticalVolterraPrimitive_jet_bounds_of_bounds
    hk₁cont hk₂cont hG₁cont hG₂cont hk₀ hkΔ₀ hDnonneg
    hk₁bound hkdiff hG₁bound hGdiff hu hulower hlowerupper hupper
  simpa only [weightedDiagonalVolterraPrimitive, k₁, k₂, G₁, G₂,
    k₀, k₁c, kΔ₀, kΔ₁] using h

end intervalIntegral

end
