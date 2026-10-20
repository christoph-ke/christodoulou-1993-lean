module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesEquationTransfer
import Mathlib.Tactic

/-!
# Transfer of all classical equations from lower tiles

The finite C¹ glue inherits each of the twelve reduced equations from its
closed rectangles. The generic transfer lemma handles tile joins and edge
points, so the statement only needs classical jets on the actual tiles.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Classical jet equations on each tile pass to the glued seven-field
state on the complete lower strip. -/
theorem LowerCoverMarch.classical_jet_on_assembled_state
    {a vStar L b : ℝ} {D : LowerCoverBaseData a vStar L}
    {u : ℕ → ℝ} {B : ℕ → C1Solution.SafeRectangleBox} {n : ℕ}
    (M : LowerCoverMarch D u B n)
    (hstep : ∀ i ≤ n, u i < u (i + 1))
    (Z : ℝ × ℝ → C1Solution.RectangleState)
    (hZ : ContDiffOn ℝ 1 Z
      (Goursat.rectangle (u 0) (u (n + 1)) vStar
        (vStar + M.height)))
    (hsafe : ∀ p ∈ Goursat.rectangle (u 0) (u (n + 1))
      vStar (vStar + M.height), C1Solution.IsSafeRectangleState (Z p))
    (hmatch : ∀ i : ℕ, (hi : i ≤ n) → EqOn Z
      (fun p => ((M.tile i hi).incoming p, (M.tile i hi).outgoing p))
      (Goursat.rectangle (u i) (u (i + 1)) vStar
        (vStar + M.height)))
    (hTile : ∀ i : ℕ, (hi : i ≤ n) →
      RouteBClassicalJetOn b
        (Goursat.rectangle (u i) (u (i + 1)) vStar
          (vStar + M.height))
        (rectangleStateFields fun p =>
          ((M.tile i hi).incoming p, (M.tile i hi).outgoing p))) :
    RouteBClassicalJetOn b
      (Goursat.rectangle (u 0) (u (n + 1)) vStar
        (vStar + M.height))
      (rectangleStateFields Z) := by
  let K := Goursat.rectangle (u 0) (u (n + 1)) vStar
    (vStar + M.height)
  let S := rectangleStateFields Z
  have hS : RouteBFieldsC1On S K :=
    routeBFieldsC1On_rectangleStateFields hZ hsafe
  have hcoord (c : RouteBField) : ContDiffOn ℝ 1
      (routeBScalarExpression (routeBSelector c) S) K := by
    change ContDiffOn ℝ 1 (routeBField S c) K
    exact hS c
  have hpsi : ContDiffOn ℝ 1
      (routeBScalarExpression routeBScalarRadiusExpr S) K := by
    change ContDiffOn ℝ 1
      (fun p => routeBField S .radius p * routeBField S .scalar p) K
    exact (hS .radius).mul (hS .scalar)
  have htheta : ContDiffOn ℝ 1
      (routeBScalarExpression routeBThetaExpr S) K := by
    change ContDiffOn ℝ 1
      (fun p => routeBField S .outgoing p -
        routeBField S .expansion p * routeBField S .scalar p) K
    exact (hS .outgoing).sub ((hS .expansion).mul (hS .scalar))
  have hzeta : ContDiffOn ℝ 1
      (routeBScalarExpression routeBZetaExpr S) K := by
    change ContDiffOn ℝ 1
      (fun p => routeBField S .incoming p -
        routeBField S .contraction p * routeBField S .scalar p) K
    exact (hS .incoming).sub ((hS .contraction).mul (hS .scalar))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact M.local_jet_equation_on_assembled_state hstep Z hmatch
      _ _ _ (hcoord .radius) (fun i hi => (hTile i hi).radius_out)
  · exact M.local_jet_equation_on_assembled_state hstep Z hmatch
      _ _ _ (hcoord .radius) (fun i hi => (hTile i hi).radius_in)
  · exact M.local_jet_equation_on_assembled_state hstep Z hmatch
      _ _ _ hpsi (fun i hi => (hTile i hi).scalar_radius_out)
  · exact M.local_jet_equation_on_assembled_state hstep Z hmatch
      _ _ _ hpsi (fun i hi => (hTile i hi).scalar_radius_in)
  · exact M.local_jet_equation_on_assembled_state hstep Z hmatch
      _ _ _ (hcoord .mass) (fun i hi => (hTile i hi).mass_out)
  · exact M.local_jet_equation_on_assembled_state hstep Z hmatch
      _ _ _ (hcoord .mass) (fun i hi => (hTile i hi).mass_in)
  · exact M.local_jet_equation_on_assembled_state hstep Z hmatch
      _ _ _ (hcoord .expansion) (fun i hi => (hTile i hi).expansion_in)
  · exact M.local_jet_equation_on_assembled_state hstep Z hmatch
      _ _ _ (hcoord .contraction) (fun i hi => (hTile i hi).contraction_out)
  · exact M.local_jet_equation_on_assembled_state hstep Z hmatch
      _ _ _ htheta (fun i hi => (hTile i hi).theta_in)
  · exact M.local_jet_equation_on_assembled_state hstep Z hmatch
      _ _ _ hzeta (fun i hi => (hTile i hi).zeta_out)
  · exact M.local_jet_equation_on_assembled_state hstep Z hmatch
      _ _ _ (hcoord .outgoing) (fun i hi => (hTile i hi).outgoing_in)
  · exact M.local_jet_equation_on_assembled_state hstep Z hmatch
      _ _ _ (hcoord .incoming) (fun i hi => (hTile i hi).incoming_out)

end ChristodoulouBV.Uniqueness

end
