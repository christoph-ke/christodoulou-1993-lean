module

public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamDirectJets
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Physical scalar incoming jet on the Route B seam

The radius and rescaled scalar have matching incoming jets. Their product
identity `r φ = ψ`, positive radius, and matching values determine `φᵤ`.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Equality of radius and rescaled-scalar incoming jets gives equality of
the physical scalar incoming jet on the full closed seam. -/
theorem routeB_vertical_phi_horizontal_jet_eq
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (hStarb : vStar < b) (SLow SAx : Fields)
    (hLowC1 : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hAxC1 : RouteBFieldsC1On SAx (closedCoordTriangle a b))
    (hRadius : ∀ v ∈ Icc vStar b, SLow.r a v = SAx.r a v)
    (hRadiusPos : ∀ v ∈ Icc vStar b, 0 < SLow.r a v)
    (hPhi : ∀ v ∈ Icc vStar b, SLow.phi a v = SAx.phi a v)
    (hRadiusJet : ∀ v ∈ Icc vStar b,
      (fderivWithin ℝ (routeBField SLow .radius)
        (routeBLowerRegion a vStar b) (a, v)) (1, 0) =
      (fderivWithin ℝ (routeBField SAx .radius)
        (closedCoordTriangle a b) (a, v)) (1, 0))
    (hPsiJet : ∀ v ∈ Icc vStar b,
      (fderivWithin ℝ
        (routeBScalarExpression routeBScalarRadiusExpr SLow)
        (routeBLowerRegion a vStar b) (a, v)) (1, 0) =
      (fderivWithin ℝ
        (routeBScalarExpression routeBScalarRadiusExpr SAx)
        (closedCoordTriangle a b) (a, v)) (1, 0)) :
    ∀ v ∈ Icc vStar b,
      (fderivWithin ℝ (routeBField SLow .scalar)
        (routeBLowerRegion a vStar b) (a, v)) (1, 0) =
      (fderivWithin ℝ (routeBField SAx .scalar)
        (closedCoordTriangle a b) (a, v)) (1, 0) := by
  have hLowUnique : UniqueDiffOn ℝ (routeBLowerRegion a vStar b) :=
    uniqueDiffOn_convex (routeBLowerRegion_closed_convex a vStar b).2
      (routeBLowerRegion_interior_nonempty ha hStarb)
  have hAxUnique : UniqueDiffOn ℝ (closedCoordTriangle a b) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b) (by
      rw [interior_closedCoordTriangle]
      exact openCoordTriangle_nonempty (haStar.trans hStarb))
  intro v hv
  have hpLow : (a, v) ∈ routeBLowerRegion a vStar b :=
    ⟨⟨ha.le, le_rfl⟩, hv⟩
  have hpAx : (a, v) ∈ closedCoordTriangle a b :=
    ⟨le_rfl, haStar.le.trans hv.1, hv.2⟩
  have hProdLow :
      (fderivWithin ℝ
        (routeBScalarExpression routeBScalarRadiusExpr SLow)
        (routeBLowerRegion a vStar b) (a, v)) (1, 0) =
      SLow.r a v *
        (fderivWithin ℝ (routeBField SLow .scalar)
          (routeBLowerRegion a vStar b) (a, v)) (1, 0) +
      SLow.phi a v *
        (fderivWithin ℝ (routeBField SLow .radius)
          (routeBLowerRegion a vStar b) (a, v)) (1, 0) := by
    have hrDiff := (hLowC1 .radius).differentiableOn (by norm_num) _ hpLow
    have hφDiff := (hLowC1 .scalar).differentiableOn (by norm_num) _ hpLow
    change (fderivWithin ℝ
      (routeBField SLow .radius * routeBField SLow .scalar)
      (routeBLowerRegion a vStar b) (a, v)) (1, 0) = _
    rw [fderivWithin_mul (hLowUnique _ hpLow) hrDiff hφDiff]
    simp only [add_apply, smul_apply, smul_eq_mul, routeBField]
  have hProdAx :
      (fderivWithin ℝ
        (routeBScalarExpression routeBScalarRadiusExpr SAx)
        (closedCoordTriangle a b) (a, v)) (1, 0) =
      SAx.r a v *
        (fderivWithin ℝ (routeBField SAx .scalar)
          (closedCoordTriangle a b) (a, v)) (1, 0) +
      SAx.phi a v *
        (fderivWithin ℝ (routeBField SAx .radius)
          (closedCoordTriangle a b) (a, v)) (1, 0) := by
    have hrDiff := (hAxC1 .radius).differentiableOn (by norm_num) _ hpAx
    have hφDiff := (hAxC1 .scalar).differentiableOn (by norm_num) _ hpAx
    change (fderivWithin ℝ
      (routeBField SAx .radius * routeBField SAx .scalar)
      (closedCoordTriangle a b) (a, v)) (1, 0) = _
    rw [fderivWithin_mul (hAxUnique _ hpAx) hrDiff hφDiff]
    simp only [add_apply, smul_apply, smul_eq_mul, routeBField]
  rw [← hRadius v hv, ← hPhi v hv] at hProdAx
  rw [← hRadiusJet v hv] at hProdAx
  have hMul := (hProdLow.symm.trans ((hPsiJet v hv).trans hProdAx))
  have hMul' :
      SLow.r a v *
        (fderivWithin ℝ (routeBField SLow .scalar)
          (routeBLowerRegion a vStar b) (a, v)) (1, 0) =
      SLow.r a v *
        (fderivWithin ℝ (routeBField SAx .scalar)
          (closedCoordTriangle a b) (a, v)) (1, 0) := by
    linarith only [hMul]
  exact (mul_left_cancel₀ (ne_of_gt (hRadiusPos v hv))) hMul'

end ChristodoulouBV.Uniqueness

end
