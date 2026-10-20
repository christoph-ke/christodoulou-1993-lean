module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointPair
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraQuotientBox
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Two-input attenuation estimates for the axis Picard map

The attenuated Volterra pair box requires a linear difference for the
attenuation kernel and uniform bounds for its coordinate-jet differences.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- Both Volterra kernels associated to a boxed input have continuous first
jets up to the diagonal, as required by the attenuated pair box. -/
theorem Box.massSource_attenuation_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) :
    ContDiffOn ℝ 1 x.1.toTriple.massSource (closedCoordTriangle a b) ∧
      ContDiffOn ℝ 1 x.1.toTriple.attenuation (closedCoordTriangle a b) := by
  have hdxw : DifferentiableOn ℝ x.1.1.extendValue
      (interior (closedCoordTriangle a b)) :=
    (x.lam_c1.differentiableOn (by norm_num)).mono interior_subset
  have hdxf : DifferentiableOn ℝ x.1.2.2.extendValue
      (interior (closedCoordTriangle a b)) :=
    (x.h_c1.differentiableOn (by norm_num)).mono interior_subset
  have hderivxw : ∀ q ∈ interior (closedCoordTriangle a b),
      fderiv ℝ x.1.1.extendValue q = x.1.1.extendDerivative q := by
    intro q hq
    exact x.1.1.fderiv_eq_extendDerivative_interior hab x.2.2.1 hq
  have hderivxf : ∀ q ∈ interior (closedCoordTriangle a b),
      fderiv ℝ x.1.2.2.extendValue q = x.1.2.2.extendDerivative q := by
    intro q hq
    exact x.1.2.2.fderiv_eq_extendDerivative_interior hab x.2.2.2.2 hq
  have hweight : ∀ q ∈ closedCoordTriangle a b,
      (1 / 4 : ℝ) ≤ x.1.1.extendValue q := by
    intro q hq
    exact (x.lam_value_bounds hq).1
  have hj := intervalIntegral.contDiffOn_weightedDiagonalQuadraticKernel hab
    x.1.1.continuousOn_extendValue x.1.2.2.continuousOn_extendValue
    x.1.1.continuousOn_extendDerivative x.1.2.2.continuousOn_extendDerivative
    hdxw hdxf hderivxw hderivxf hweight (by norm_num)
  have hk := intervalIntegral.contDiffOn_weightedDiagonalQuotientKernel hab
    x.1.1.continuousOn_extendValue x.1.2.2.continuousOn_extendValue
    x.1.1.continuousOn_extendDerivative x.1.2.2.continuousOn_extendDerivative
    hdxw hdxf hderivxw hderivxf hweight (by norm_num)
  have hj_eq : x.1.toTriple.massSource =
      intervalIntegral.weightedDiagonalQuadraticKernel
        x.1.1.extendValue x.1.2.2.extendValue := by
    funext q
    rfl
  have hk_eq : x.1.toTriple.attenuation =
      intervalIntegral.weightedDiagonalQuotientKernel
        x.1.1.extendValue x.1.2.2.extendValue := by
    funext q
    rfl
  rw [hj_eq, hk_eq]
  exact ⟨hj, hk⟩

/-- The two attenuation kernels have the exact value and coordinate-jet
difference bounds of the weighted diagonal quotient ledger. -/
theorem Box.attenuation_difference_bounds {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsize : b - a ≤ 1) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) :
    let D := x.1.coordinateDistance y.1
    let TΔ₀ := intervalIntegral.weightedDiagonalQuotientValueDifferenceCoefficient
      (1 / 4) (3 / 4) (2 * M)
    let TΔ₁ := intervalIntegral.weightedDiagonalQuotientDerivativeDifferenceCoefficient
      (1 / 4) (3 / 4) (2 * M) (2 * M) (3 / 4 + 2 * M) 2
    |x.1.toTriple.attenuation p - y.1.toTriple.attenuation p| ≤
        TΔ₀ * (p.2 - p.1) * D ∧
    |(fderivWithin ℝ x.1.toTriple.attenuation (closedCoordTriangle a b) p) (1, 0) -
      (fderivWithin ℝ y.1.toTriple.attenuation (closedCoordTriangle a b) p) (1, 0)| ≤
        TΔ₁ * D ∧
    |(fderivWithin ℝ x.1.toTriple.attenuation (closedCoordTriangle a b) p) (0, 1) -
      (fderivWithin ℝ y.1.toTriple.attenuation (closedCoordTriangle a b) p) (0, 1)| ≤
        TΔ₁ * D := by
  dsimp only
  have hdxw : DifferentiableOn ℝ x.1.1.extendValue
      (interior (closedCoordTriangle a b)) :=
    (x.lam_c1.differentiableOn (by norm_num)).mono interior_subset
  have hdyw : DifferentiableOn ℝ y.1.1.extendValue
      (interior (closedCoordTriangle a b)) :=
    (y.lam_c1.differentiableOn (by norm_num)).mono interior_subset
  have hdxf : DifferentiableOn ℝ x.1.2.2.extendValue
      (interior (closedCoordTriangle a b)) :=
    (x.h_c1.differentiableOn (by norm_num)).mono interior_subset
  have hdyf : DifferentiableOn ℝ y.1.2.2.extendValue
      (interior (closedCoordTriangle a b)) :=
    (y.h_c1.differentiableOn (by norm_num)).mono interior_subset
  have hderivxw : ∀ q ∈ interior (closedCoordTriangle a b),
      fderiv ℝ x.1.1.extendValue q = x.1.1.extendDerivative q := by
    intro q hq
    exact x.1.1.fderiv_eq_extendDerivative_interior hab x.2.2.1 hq
  have hderivyw : ∀ q ∈ interior (closedCoordTriangle a b),
      fderiv ℝ y.1.1.extendValue q = y.1.1.extendDerivative q := by
    intro q hq
    exact y.1.1.fderiv_eq_extendDerivative_interior hab y.2.2.1 hq
  have hderivxf : ∀ q ∈ interior (closedCoordTriangle a b),
      fderiv ℝ x.1.2.2.extendValue q = x.1.2.2.extendDerivative q := by
    intro q hq
    exact x.1.2.2.fderiv_eq_extendDerivative_interior hab x.2.2.2.2 hq
  have hderivyf : ∀ q ∈ interior (closedCoordTriangle a b),
      fderiv ℝ y.1.2.2.extendValue q = y.1.2.2.extendDerivative q := by
    intro q hq
    exact y.1.2.2.fderiv_eq_extendDerivative_interior hab y.2.2.2.2 hq
  have hlamxU : ∀ q ∈ closedCoordTriangle a b,
      |x.1.1.extendDerivative q (1, 0)| ≤ 2 * M := by
    intro q hq
    simpa [coordinateDirection] using x.lam_coordinate_bound hq (0 : Fin 2)
  have hlamyU : ∀ q ∈ closedCoordTriangle a b,
      |y.1.1.extendDerivative q (1, 0)| ≤ 2 * M := by
    intro q hq
    simpa [coordinateDirection] using y.lam_coordinate_bound hq (0 : Fin 2)
  have hlamyV : ∀ q ∈ closedCoordTriangle a b,
      |y.1.1.extendDerivative q (0, 1)| ≤ 2 * M := by
    intro q hq
    simpa [coordinateDirection] using y.lam_coordinate_bound hq (1 : Fin 2)
  have hhxU : ∀ q ∈ closedCoordTriangle a b,
      |x.1.2.2.extendDerivative q (1, 0)| ≤ 2 * M := by
    intro q hq
    simpa [coordinateDirection] using x.h_coordinate_bound hq (0 : Fin 2)
  have hhyU : ∀ q ∈ closedCoordTriangle a b,
      |y.1.2.2.extendDerivative q (1, 0)| ≤ 2 * M := by
    intro q hq
    simpa [coordinateDirection] using y.h_coordinate_bound hq (0 : Fin 2)
  have hhxV : ∀ q ∈ closedCoordTriangle a b,
      |x.1.2.2.extendDerivative q (0, 1)| ≤ 2 * M := by
    intro q hq
    simpa [coordinateDirection] using x.h_coordinate_bound hq (1 : Fin 2)
  have hhyV : ∀ q ∈ closedCoordTriangle a b,
      |y.1.2.2.extendDerivative q (0, 1)| ≤ 2 * M := by
    intro q hq
    simpa [coordinateDirection] using y.h_coordinate_bound hq (1 : Fin 2)
  have h := intervalIntegral.weightedDiagonalQuotientKernel_difference_bounds_threeJetDistanceOn
    (D := x.1.coordinateDistance y.1) hab hsize
    x.1.1.continuousOn_extendValue y.1.1.continuousOn_extendValue
    x.1.2.1.continuousOn_extendValue y.1.2.1.continuousOn_extendValue
    x.1.2.2.continuousOn_extendValue y.1.2.2.continuousOn_extendValue
    x.1.1.continuousOn_extendDerivative y.1.1.continuousOn_extendDerivative
    x.1.2.1.continuousOn_extendDerivative y.1.2.1.continuousOn_extendDerivative
    x.1.2.2.continuousOn_extendDerivative y.1.2.2.continuousOn_extendDerivative
    hdxw hdyw hdxf hdyf hderivxw hderivyw hderivxf hderivyf
    (fun q hq => x.lam_value_bounds hq)
    (fun q hq => y.lam_value_bounds hq)
    hlamxU hlamyU hlamyV hhxU hhyU hhxV hhyV
    (by norm_num) (by linarith only [hM]) (by linarith only [hM]) rfl hp
  have hx : x.1.toTriple.attenuation =
      intervalIntegral.weightedDiagonalQuotientKernel
        x.1.1.extendValue x.1.2.2.extendValue := by
    funext q
    rfl
  have hy : y.1.toTriple.attenuation =
      intervalIntegral.weightedDiagonalQuotientKernel
        y.1.1.extendValue y.1.2.2.extendValue := by
    funext q
    rfl
  rw [hx, hy]
  exact h

end ChristodoulouBV.AxisPicard

end
