module

public import ChristodoulouBV.C1Solution.AxisPicardContraction
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraRadiusJet
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraKernelBox
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Two-input radius estimates for the axis Picard map

The common coefficient box needs the radius difference to vanish at the axis,
and it needs both coordinate derivatives of that difference. These estimates
use the coordinate distance on the complete three-field jet space.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- A scalar jet's value difference is bounded by its coefficient distance
at every point of the closed triangle. -/
theorem ScalarJet.value_sub_le_coordinateDistance {a b : ℝ}
    (hab : a ≤ b) (f g : ScalarJet a b)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |f.extendValue p - g.extendValue p| ≤ f.coordinateDistance g := by
  have hne : (closedCoordTriangle a b).Nonempty := by
    refine ⟨(a, a), ?_⟩
    simpa only [closedCoordTriangle, Set.mem_ofPred_eq] using
      (show a ≤ a ∧ a ≤ a ∧ a ≤ b from ⟨le_rfl, le_rfl, hab⟩)
  exact abs_value_sub_le_coordinateJetDistanceOn
    (isCompact_closedCoordTriangle a b) hne
    f.continuousOn_extendValue g.continuousOn_extendValue
    f.continuousOn_extendDerivative g.continuousOn_extendDerivative hp

/-- Each coordinate derivative difference of two scalar jets is bounded
by their coefficient distance. -/
theorem ScalarJet.derivative_sub_le_coordinateDistance {a b : ℝ}
    (hab : a ≤ b) (f g : ScalarJet a b)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) (i : Fin 2) :
    |f.extendDerivative p (coordinateDirection i) -
      g.extendDerivative p (coordinateDirection i)| ≤ f.coordinateDistance g := by
  have hne : (closedCoordTriangle a b).Nonempty := by
    refine ⟨(a, a), ?_⟩
    simpa only [closedCoordTriangle, Set.mem_ofPred_eq] using
      (show a ≤ a ∧ a ≤ a ∧ a ≤ b from ⟨le_rfl, le_rfl, hab⟩)
  have hu := abs_horizontal_sub_le_coordinateJetDistanceOn
    (isCompact_closedCoordTriangle a b) hne
    f.continuousOn_extendValue g.continuousOn_extendValue
    f.continuousOn_extendDerivative g.continuousOn_extendDerivative hp
  have hv := abs_vertical_sub_le_coordinateJetDistanceOn
    (isCompact_closedCoordTriangle a b) hne
    f.continuousOn_extendValue g.continuousOn_extendValue
    f.continuousOn_extendDerivative g.continuousOn_extendDerivative hp
  fin_cases i
  · simpa [coordinateDirection, ScalarJet.coordinateDistance] using hu
  · simpa [coordinateDirection, ScalarJet.coordinateDistance] using hv

/-- Every value and coordinate-jet difference of two boxed input triples
is bounded by their common coefficient distance. -/
theorem Box.input_difference_bounds {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x y : Box a b M g hEdge) (hab : a ≤ b)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (|x.1.1.extendValue p - y.1.1.extendValue p| ≤
        x.1.coordinateDistance y.1 ∧
      |x.1.2.1.extendValue p - y.1.2.1.extendValue p| ≤
        x.1.coordinateDistance y.1 ∧
      |x.1.2.2.extendValue p - y.1.2.2.extendValue p| ≤
        x.1.coordinateDistance y.1) ∧
    ∀ i : Fin 2,
      |x.1.1.extendDerivative p (coordinateDirection i) -
        y.1.1.extendDerivative p (coordinateDirection i)| ≤
          x.1.coordinateDistance y.1 ∧
      |x.1.2.1.extendDerivative p (coordinateDirection i) -
        y.1.2.1.extendDerivative p (coordinateDirection i)| ≤
          x.1.coordinateDistance y.1 ∧
      |x.1.2.2.extendDerivative p (coordinateDirection i) -
        y.1.2.2.extendDerivative p (coordinateDirection i)| ≤
          x.1.coordinateDistance y.1 := by
  have hlam : x.1.1.coordinateDistance y.1.1 ≤
      x.1.coordinateDistance y.1 := le_max_left _ _
  have hnu : x.1.2.1.coordinateDistance y.1.2.1 ≤
      x.1.coordinateDistance y.1 :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hh : x.1.2.2.coordinateDistance y.1.2.2 ≤
      x.1.coordinateDistance y.1 :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨⟨(x.1.1.value_sub_le_coordinateDistance hab y.1.1 hp).trans hlam,
      (x.1.2.1.value_sub_le_coordinateDistance hab y.1.2.1 hp).trans hnu,
      (x.1.2.2.value_sub_le_coordinateDistance hab y.1.2.2 hp).trans hh⟩, ?_⟩
  intro i
  exact ⟨(x.1.1.derivative_sub_le_coordinateDistance hab y.1.1 hp i).trans hlam,
    (x.1.2.1.derivative_sub_le_coordinateDistance hab y.1.2.1 hp i).trans hnu,
    (x.1.2.2.derivative_sub_le_coordinateDistance hab y.1.2.2 hp i).trans hh⟩

/-- Both coordinate jets of a boxed input's radius obey the common
`C + L` coefficient on a triangle of width at most one. -/
theorem Box.radius_jet_bound {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsize : b - a ≤ 1) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) (i : Fin 2) :
    |(fderivWithin ℝ x.1.toTriple.radius (closedCoordTriangle a b) p)
      (coordinateDirection i)| ≤ 3 / 4 + 2 * M := by
  have hdx : DifferentiableOn ℝ x.1.1.extendValue
      (interior (closedCoordTriangle a b)) :=
    (x.lam_c1.differentiableOn (by norm_num)).mono interior_subset
  have hderivx : ∀ q ∈ interior (closedCoordTriangle a b),
      fderiv ℝ x.1.1.extendValue q = x.1.1.extendDerivative q := by
    intro q hq
    exact x.1.1.fderiv_eq_extendDerivative_interior hab x.2.2.1 hq
  have hw : ∀ q ∈ closedCoordTriangle a b,
      |x.1.1.extendValue q| ≤ 3 / 4 := by
    intro q hq
    have hq' := x.lam_value_bounds hq
    rw [abs_of_nonneg (by linarith only [hq'.1])]
    exact hq'.2
  have hGu : ∀ q ∈ closedCoordTriangle a b,
      |x.1.1.extendDerivative q (1, 0)| ≤ 2 * M := by
    intro q hq
    simpa [coordinateDirection] using x.lam_coordinate_bound hq (0 : Fin 2)
  have h := intervalIntegral.abs_fderivWithin_weightedDiagonalRadius_apply_le
    hab x.1.1.continuousOn_extendValue x.1.1.continuousOn_extendDerivative
    hdx hderivx hw hGu hp
  have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
  have hgap : p.2 - p.1 ≤ 1 := by linarith only [hcoord.1, hcoord.2.2, hsize]
  have hmul : 2 * M * (p.2 - p.1) ≤ 2 * M := by
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hgap (by linarith only [hM] : 0 ≤ 2 * M))
  have hx : x.1.toTriple.radius =
      intervalIntegral.weightedDiagonalRadius x.1.1.extendValue := by
    funext q
    rfl
  rw [hx]
  fin_cases i
  · simpa [coordinateDirection] using (h.1.trans (by linarith only [hmul]))
  · simpa [coordinateDirection] using (h.2.trans (by linarith only [hM]))

/-- Two boxed Picard inputs have radii whose value difference vanishes
linearly at the axis. Their horizontal and vertical radius jets differ by
at most two and one times the three-field coordinate distance. -/
theorem Box.radius_difference_bounds {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x y : Box a b M g hEdge) (hab : a < b) (hsize : b - a ≤ 1)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |x.1.toTriple.radius p - y.1.toTriple.radius p| ≤
        (p.2 - p.1) * x.1.coordinateDistance y.1 ∧
    |(fderivWithin ℝ x.1.toTriple.radius (closedCoordTriangle a b) p) (1, 0) -
      (fderivWithin ℝ y.1.toTriple.radius (closedCoordTriangle a b) p) (1, 0)| ≤
        2 * x.1.coordinateDistance y.1 ∧
    |(fderivWithin ℝ x.1.toTriple.radius (closedCoordTriangle a b) p) (0, 1) -
      (fderivWithin ℝ y.1.toTriple.radius (closedCoordTriangle a b) p) (0, 1)| ≤
        x.1.coordinateDistance y.1 := by
  have hwx := x.1.1.continuousOn_extendValue
  have hwy := y.1.1.continuousOn_extendValue
  have hGx := x.1.1.continuousOn_extendDerivative
  have hGy := y.1.1.continuousOn_extendDerivative
  have hdx : DifferentiableOn ℝ x.1.1.extendValue
      (interior (closedCoordTriangle a b)) :=
    (x.lam_c1.differentiableOn (by norm_num)).mono interior_subset
  have hdy : DifferentiableOn ℝ y.1.1.extendValue
      (interior (closedCoordTriangle a b)) :=
    (y.lam_c1.differentiableOn (by norm_num)).mono interior_subset
  have hderivx : ∀ q ∈ interior (closedCoordTriangle a b),
      fderiv ℝ x.1.1.extendValue q = x.1.1.extendDerivative q := by
    intro q hq
    exact x.1.1.fderiv_eq_extendDerivative_interior hab x.2.2.1 hq
  have hderivy : ∀ q ∈ interior (closedCoordTriangle a b),
      fderiv ℝ y.1.1.extendValue q = y.1.1.extendDerivative q := by
    intro q hq
    exact y.1.1.fderiv_eq_extendDerivative_interior hab y.2.2.1 hq
  have h := intervalIntegral.weightedDiagonalRadius_difference_bounds_threeJetDistanceOn
    (D := x.1.coordinateDistance y.1) hab hsize
    hwx hwy hGx hGy hdx hdy hderivx hderivy rfl hp
  have hx : x.1.toTriple.radius =
      intervalIntegral.weightedDiagonalRadius x.1.1.extendValue := by
    funext q
    rfl
  have hy : y.1.toTriple.radius =
      intervalIntegral.weightedDiagonalRadius y.1.1.extendValue := by
    funext q
    rfl
  rw [hx, hy]
  exact h

/-- The two quadratic mass sources have the exact value and coordinate-jet
difference bounds supplied by the weighted diagonal kernel ledger. -/
theorem Box.massSource_difference_bounds {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsize : b - a ≤ 1) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) :
    let D := x.1.coordinateDistance y.1
    let SΔ₀ := intervalIntegral.weightedDiagonalQuadraticValueDifferenceCoefficient
      (1 / 4) (3 / 4) (2 * M)
    let SΔ₁ := intervalIntegral.weightedDiagonalQuadraticDerivativeDifferenceCoefficient
      (1 / 4) (3 / 4) (2 * M) (2 * M)
    |x.1.toTriple.massSource p - y.1.toTriple.massSource p| ≤
        SΔ₀ * (p.2 - p.1) ^ 2 * D ∧
    |(fderivWithin ℝ x.1.toTriple.massSource (closedCoordTriangle a b) p) (1, 0) -
      (fderivWithin ℝ y.1.toTriple.massSource (closedCoordTriangle a b) p) (1, 0)| ≤
        SΔ₁ * (p.2 - p.1) * D ∧
    |(fderivWithin ℝ x.1.toTriple.massSource (closedCoordTriangle a b) p) (0, 1) -
      (fderivWithin ℝ y.1.toTriple.massSource (closedCoordTriangle a b) p) (0, 1)| ≤
        SΔ₁ * (p.2 - p.1) * D := by
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
  have h := intervalIntegral.weightedDiagonalQuadraticKernel_difference_bounds_threeJetDistanceOn
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
  have hx : x.1.toTriple.massSource =
      intervalIntegral.weightedDiagonalQuadraticKernel
        x.1.1.extendValue x.1.2.2.extendValue := by
    funext q
    rfl
  have hy : y.1.toTriple.massSource =
      intervalIntegral.weightedDiagonalQuadraticKernel
        y.1.1.extendValue y.1.2.2.extendValue := by
    funext q
    rfl
  rw [hx, hy]
  exact h

end ChristodoulouBV.AxisPicard

end
