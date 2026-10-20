module

public import ChristodoulouBV.C1Solution.AxisReconstructionFixedPoint
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Geometric equations of the reconstructed axis solution

The removable Picard coefficient agrees with the geometric quotient away
from the axis. The fixed-point jets therefore give both radius equations.
-/

public section

noncomputable section

namespace ChristodoulouBV.AxisPicard

/-- The Picard gravitational coefficient is the usual geometric quotient
strictly above the regular axis. -/
theorem Box.gravitational_off_axis {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hstrict : p.1 < p.2) :
    x.1.toTriple.gravitational p =
      x.1.toTriple.massRatio p * x.1.toTriple.lam p *
        x.1.toTriple.nu p /
        ((1 - x.1.toTriple.massRatio p) * x.1.toTriple.radius p) := by
  have hr : x.1.toTriple.radius p ≠ 0 := (x.radius_pos hp hstrict).ne'
  have hden : 1 - x.1.toTriple.massRatio p ≠ 0 := by
    have hm := (x.massRatio_bounds hab hM hsmall hp).2
    linarith
  simp only [Triple.gravitational, intervalIntegral.rationalCubicCoefficient,
    intervalIntegral.cubicSquaredQuotient,
    intervalIntegral.cubicLinearQuotient, ite_eq_left hstrict,
    Triple.massRatio]
  field_simp [hr, hden]

/-- Christodoulou's first geometric equation (1.14a). -/
theorem Box.radius_uv_equation {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hstrict : p.1 < p.2) :
    (fderivWithin ℝ x.1.toTriple.lam
      (closedCoordTriangle a b) p) (1, 0) =
      x.1.toTriple.massRatio p * x.1.toTriple.lam p *
        x.1.toTriple.nu p /
        ((1 - x.1.toTriple.massRatio p) * x.1.toTriple.radius p) := by
  rw [x.lam_u hab hM hsmall hfixed hp]
  exact x.gravitational_off_axis hab hM hsmall hp hstrict

/-- Christodoulou's second geometric equation (1.14b). -/
theorem Box.nu_v_equation {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hstrict : p.1 < p.2) :
    (fderivWithin ℝ x.1.toTriple.nu
      (closedCoordTriangle a b) p) (0, 1) =
      x.1.toTriple.massRatio p * x.1.toTriple.lam p *
        x.1.toTriple.nu p /
        ((1 - x.1.toTriple.massRatio p) * x.1.toTriple.radius p) := by
  rw [x.nu_v hab hM hsmall hfixed hp]
  exact x.gravitational_off_axis hab hM hsmall hp hstrict

end ChristodoulouBV.AxisPicard

end
