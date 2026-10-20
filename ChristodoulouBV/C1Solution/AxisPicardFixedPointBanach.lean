module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointPairContract
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-!
# Banach fixed point for the axis Picard box

The invariant update is a strict contraction in the complete box metric.
Its fixed point is the unique boxed Picard solution at the explicit lifetime.
-/

public section

noncomputable section

open scoped NNReal

namespace ChristodoulouBV.AxisPicard

/-- The invariant axis Picard map has Lipschitz constant one half in the
complete box metric. -/
theorem Box.picardMap_contracting {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (D : EdgeData a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    ContractingWith (1 / 2 : ℝ≥0) (Box.picardMap D hab hM hsmall) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  let B := numericalLedger M
  let T := b - a
  let Z := x.1.coordinateDistance y.1
  have hT : 0 ≤ T := sub_nonneg.mpr hab.le
  have hC : 0 ≤ B.Cstar M := by
    linarith only [(B.coefficients_le_Cstar hM).1]
  have hCT : B.Cstar M * T ≤ 1 / 100 := by
    exact B.coefficient_mul_width_le hab hM hsmall (le_refl _)
  have hD := Box.coordinateDistance_le_three_dist hab.le x y
  have hBox := Box.dist_le_coordinateDistance hab.le
    (Box.picardMap D hab hM hsmall x)
    (Box.picardMap D hab hM hsmall y)
  have hCoord := x.picardJets_coordinateDistance_bound D y hab hM hsmall
  have hNonneg : 0 ≤ dist x y := dist_nonneg
  have hZnonneg : 0 ≤ Z := (dist_nonneg).trans
    (x.1.dist_le_coordinateDistance hab.le y.1)
  have hOutput : dist (Box.picardMap D hab hM hsmall x)
      (Box.picardMap D hab hM hsmall y) ≤
      7 * B.Cstar M * T * Z :=
    hBox.trans hCoord
  have hMultiply : 7 * B.Cstar M * T * Z ≤
      7 * B.Cstar M * T * (3 * dist x y) := by
    exact mul_le_mul_of_nonneg_left hD
      (mul_nonneg (mul_nonneg (by norm_num) hC) hT)
  have hFinal : 7 * B.Cstar M * T * (3 * dist x y) ≤
      (1 / 2 : ℝ) * dist x y := by
    have hCT' : 0 ≤ B.Cstar M * T := mul_nonneg hC hT
    nlinarith only [hCT, hCT', hNonneg,
      mul_nonneg (sub_nonneg.mpr hCT) hNonneg]
  simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
    hOutput.trans (hMultiply.trans hFinal)

/-- The boxed axis Picard fixed point selected by the contraction theorem. -/
@[expose] noncomputable def Box.picardFixedPoint {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    Box a b M g hEdge := by
  haveI : Nonempty (Box a b M g hEdge) := D.nonempty_box hab hM
  exact (Box.picardMap_contracting D hab hM hsmall).fixedPoint
    (Box.picardMap D hab hM hsmall)

/-- The selected point is fixed by the invariant Picard map. -/
theorem Box.picardFixedPoint_eq {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    Box.picardMap D hab hM hsmall
      (Box.picardFixedPoint D hab hM hsmall) =
      Box.picardFixedPoint D hab hM hsmall := by
  haveI : Nonempty (Box a b M g hEdge) := D.nonempty_box hab hM
  exact (Box.picardMap_contracting D hab hM hsmall).fixedPoint_isFixedPt

/-- Every boxed fixed point agrees with the selected one. -/
theorem Box.picardFixedPoint_unique {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (x : Box a b M g hEdge)
    (hx : Box.picardMap D hab hM hsmall x = x) :
    x = Box.picardFixedPoint D hab hM hsmall := by
  haveI : Nonempty (Box a b M g hEdge) := D.nonempty_box hab hM
  exact (Box.picardMap_contracting D hab hM hsmall).fixedPoint_unique hx

/-- There exists exactly one boxed Picard fixed point at the explicit
lifetime. -/
theorem Box.existsUnique_picardFixedPoint {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    ∃! x : Box a b M g hEdge,
      Box.picardMap D hab hM hsmall x = x := by
  refine ⟨Box.picardFixedPoint D hab hM hsmall,
    Box.picardFixedPoint_eq D hab hM hsmall, ?_⟩
  intro x hx
  exact x.picardFixedPoint_unique D hab hM hsmall hx

end ChristodoulouBV.AxisPicard

end
