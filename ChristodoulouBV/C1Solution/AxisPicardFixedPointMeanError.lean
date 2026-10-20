module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointVolterraPair
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMeanJetBoxEstimates
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Source-factor differences for the axis Picard coefficient box

The weighted diagonal error is the removable source factor in the rational
coefficient box. Its two-input value difference vanishes linearly at the
axis; its coordinate-jet differences are uniformly bounded.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- The weighted source factor of one boxed input vanishes linearly at the
axis and has uniformly bounded coordinate derivatives. -/
theorem Box.meanError_bounds {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsize : b - a ≤ 1) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) :
    let H₁ := intervalIntegral.weightedDiagonalErrorDerivativeCoefficient
      (1 / 4) (3 / 4) (2 * M) (2 * M)
    |x.1.toTriple.meanError p| ≤ 2 * M * (p.2 - p.1) ∧
    |(fderivWithin ℝ x.1.toTriple.meanError
      (closedCoordTriangle a b) p) (1, 0)| ≤ H₁ ∧
    |(fderivWithin ℝ x.1.toTriple.meanError
      (closedCoordTriangle a b) p) (0, 1)| ≤ H₁ := by
  dsimp only
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
  have hlamU : ∀ q ∈ closedCoordTriangle a b,
      |x.1.1.extendDerivative q (1, 0)| ≤ 2 * M := by
    intro q hq
    simpa [coordinateDirection] using x.lam_coordinate_bound hq (0 : Fin 2)
  have hhU : ∀ q ∈ closedCoordTriangle a b,
      |x.1.2.2.extendDerivative q (1, 0)| ≤ 2 * M := by
    intro q hq
    simpa [coordinateDirection] using x.h_coordinate_bound hq (0 : Fin 2)
  have hhV : ∀ q ∈ closedCoordTriangle a b,
      |x.1.2.2.extendDerivative q (0, 1)| ≤ 2 * M := by
    intro q hq
    simpa [coordinateDirection] using x.h_coordinate_bound hq (1 : Fin 2)
  have h := intervalIntegral.weightedDiagonalError_bounds_on_jetBox hab hsize
    x.1.1.continuousOn_extendValue x.1.2.2.continuousOn_extendValue
    x.1.1.continuousOn_extendDerivative x.1.2.2.continuousOn_extendDerivative
    hdxw hdxf hderivxw hderivxf
    (fun q hq => x.lam_value_bounds hq) hlamU hhU hhV
    (by norm_num) (by linarith only [hM]) (by linarith only [hM]) hp
  have hx : x.1.toTriple.meanError =
      intervalIntegral.weightedDiagonalError
        x.1.1.extendValue x.1.2.2.extendValue := by
    funext q
    rfl
  rw [hx]
  exact h

/-- The source factors of two boxed inputs satisfy the exact value and
first-jet difference coefficients of the weighted diagonal ledger. -/
theorem Box.meanError_difference_bounds {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsize : b - a ≤ 1) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) :
    let D := x.1.coordinateDistance y.1
    let HΔ₀ := intervalIntegral.weightedDiagonalErrorValueDifferenceCoefficient
      (1 / 4) (3 / 4) (2 * M)
    let HΔ₁ := intervalIntegral.weightedDiagonalErrorDerivativeDifferenceCoefficient
      (1 / 4) (3 / 4) (2 * M) (2 * M)
    |x.1.toTriple.meanError p - y.1.toTriple.meanError p| ≤
        HΔ₀ * (p.2 - p.1) * D ∧
    |(fderivWithin ℝ x.1.toTriple.meanError (closedCoordTriangle a b) p) (1, 0) -
      (fderivWithin ℝ y.1.toTriple.meanError (closedCoordTriangle a b) p) (1, 0)| ≤
        HΔ₁ * D ∧
    |(fderivWithin ℝ x.1.toTriple.meanError (closedCoordTriangle a b) p) (0, 1) -
      (fderivWithin ℝ y.1.toTriple.meanError (closedCoordTriangle a b) p) (0, 1)| ≤
        HΔ₁ * D := by
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
  have h := intervalIntegral.weightedDiagonalError_difference_bounds_threeJetDistanceOn
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
    hlamxU hlamyU hhxU hhyU hhxV hhyV
    (by norm_num) (by linarith only [hM]) (by linarith only [hM]) rfl hp
  have hx : x.1.toTriple.meanError =
      intervalIntegral.weightedDiagonalError
        x.1.1.extendValue x.1.2.2.extendValue := by
    funext q
    rfl
  have hy : y.1.toTriple.meanError =
      intervalIntegral.weightedDiagonalError
        y.1.1.extendValue y.1.2.2.extendValue := by
    funext q
    rfl
  rw [hx, hy]
  exact h

end ChristodoulouBV.AxisPicard

end
