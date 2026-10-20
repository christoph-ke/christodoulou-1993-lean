module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointPairOutput
import Mathlib.Tactic

/-! # Two-input outgoing and scalar Picard jets -/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- The outgoing Picard coordinate jets contract with one width factor. -/
theorem Box.picard_lam_coordinate_sub_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (p : closedCoordTriangle a b) (i : Fin 2) :
    |(x.picardJets D hab hM hsmall).1.1.2 p (coordinateDirection i) -
      (y.picardJets D hab hM hsmall).1.1.2 p (coordinateDirection i)| ≤
      ((numericalLedger M).KΔ₀ + (numericalLedger M).KΔ₁) *
        (b - a) * x.1.coordinateDistance y.1 := by
  change |(fderivWithin ℝ (x.1.toTriple.picard a g hEdge).lam
    (closedCoordTriangle a b) p.1) (coordinateDirection i) -
    (fderivWithin ℝ (y.1.toTriple.picard a g hEdge).lam
    (closedCoordTriangle a b) p.1) (coordinateDirection i)| ≤ _
  rw [x.picard_lam_fderiv_apply D hab hM hsmall p.2,
    y.picard_lam_fderiv_apply D hab hM hsmall p.2]
  convert x.picard_lam_primitive_coordinate_sub_bound y hab hM hsmall p.2 i using 1
  ring

/-- The scalar Picard coordinate jets contract with two width factors. -/
theorem Box.picard_h_coordinate_sub_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (p : closedCoordTriangle a b) (i : Fin 2) :
    |(x.picardJets D hab hM hsmall).2.2.1.2 p (coordinateDirection i) -
      (y.picardJets D hab hM hsmall).2.2.1.2 p (coordinateDirection i)| ≤
      ((numericalLedger M).QΔ₀ + (numericalLedger M).QΔ₁) *
        (b - a) ^ 2 * x.1.coordinateDistance y.1 := by
  change |(fderivWithin ℝ (x.1.toTriple.picard a g hEdge).h
    (closedCoordTriangle a b) p.1) (coordinateDirection i) -
    (fderivWithin ℝ (y.1.toTriple.picard a g hEdge).h
    (closedCoordTriangle a b) p.1) (coordinateDirection i)| ≤ _
  rw [x.picard_h_fderiv_apply D hab hM hsmall p.2,
    y.picard_h_fderiv_apply D hab hM hsmall p.2]
  convert x.picard_h_primitive_coordinate_sub_bound y hab hM hsmall p.2 i using 1
  ring

end ChristodoulouBV.AxisPicard

end
