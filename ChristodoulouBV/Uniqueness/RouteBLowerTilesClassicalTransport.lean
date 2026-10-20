module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesClassicalPrimitives
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# Transport and mass equations on a lower tile

The characteristic equations, the propagated mass constraint, and the safe
state identities supply six more classical first-jet equations.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Mass, expansion, contraction, outgoing, and incoming transport equations
as full relative jets on a closed lower tile. -/
theorem LowerCoverTile.transport_classical_jets
    {a vStar L u₀ u₁ H b : ℝ} {D : LowerCoverBaseData a vStar L}
    {B : C1Solution.SafeRectangleBox}
    (T : LowerCoverTile D B u₀ u₁ H)
    (hu : u₀ < u₁) (hH : 0 < H)
    (hu₀ : 0 ≤ u₀) (hu₁ : u₁ ≤ a) :
    let K := Goursat.rectangle u₀ u₁ vStar (vStar + H)
    let S := rectangleStateFields fun p => (T.incoming p, T.outgoing p)
    RouteBLocalJetEquation b K S
      (routeBSelector .mass) routeBMassOutgoingExpr (0, 1) ∧
    RouteBLocalJetEquation b K S
      (routeBSelector .mass) routeBMassIncomingExpr (1, 0) ∧
    RouteBLocalJetEquation b K S
      (routeBSelector .expansion) routeBMixedExpr (1, 0) ∧
    RouteBLocalJetEquation b K S
      (routeBSelector .contraction) routeBMixedExpr (0, 1) ∧
    RouteBLocalJetEquation b K S
      (routeBSelector .outgoing) routeBMixedScalarExpr (1, 0) ∧
    RouteBLocalJetEquation b K S
      (routeBSelector .incoming) routeBMixedScalarExpr (0, 1) := by
  dsimp only
  let K := Goursat.rectangle u₀ u₁ vStar (vStar + H)
  let Z : ℝ × ℝ → C1Solution.RectangleState :=
    fun p => (T.incoming p, T.outgoing p)
  let S := rectangleStateFields Z
  have hZ : ContDiffOn ℝ 1 Z K :=
    T.incoming_c1.prodMk T.outgoing_c1
  have hsafe : ∀ p ∈ K, C1Solution.IsSafeRectangleState (Z p) := by
    intro p hp
    exact B.safe (T.safe p hp)
  have hS : RouteBFieldsC1On S K :=
    routeBFieldsC1On_rectangleStateFields hZ hsafe
  have hgrav : ∀ p ∈ K,
      C1Solution.stateGrav (Z p) =
        routeBMixedExpr (fun c => routeBField S c p) := by
    intro p hp
    have hr : C1Solution.stateRadius (Z p) ≠ 0 :=
      ne_of_gt (hsafe p hp).1
    have hgap : C1Solution.stateMassGap (Z p) ≠ 0 :=
      ne_of_gt (hsafe p hp).2.2.2
    change 2 * C1Solution.stateMass (Z p) *
        C1Solution.stateLam (Z p) * C1Solution.stateNu (Z p) /
        (C1Solution.stateRadius (Z p) *
          (C1Solution.stateRadius (Z p) -
            2 * C1Solution.stateMass (Z p))) =
      ((2 * C1Solution.stateMass (Z p) /
        C1Solution.stateRadius (Z p)) *
          C1Solution.stateLam (Z p) * C1Solution.stateNu (Z p)) /
        ((1 - 2 * C1Solution.stateMass (Z p) /
          C1Solution.stateRadius (Z p)) *
          C1Solution.stateRadius (Z p))
    exact (mixed_coefficient_eq_rectangle_grav hr hgap).symm
  have hmassOut : ∀ p ∈ K,
      C1Solution.stateMassGap (Z p) /
          C1Solution.stateRadius (Z p) *
          C1Solution.stateTheta (Z p) ^ 2 /
          (2 * C1Solution.stateLam (Z p)) =
        routeBMassOutgoingExpr (fun c => routeBField S c p) := by
    intro p hp
    have hr : C1Solution.stateRadius (Z p) ≠ 0 :=
      ne_of_gt (hsafe p hp).1
    change ((C1Solution.stateRadius (Z p) -
        2 * C1Solution.stateMass (Z p)) /
          C1Solution.stateRadius (Z p)) *
          C1Solution.stateTheta (Z p) ^ 2 /
          (2 * C1Solution.stateLam (Z p)) =
      (1 - 2 * C1Solution.stateMass (Z p) /
        C1Solution.stateRadius (Z p)) *
        C1Solution.stateTheta (Z p) ^ 2 /
        (2 * C1Solution.stateLam (Z p))
    exact (mass_out_density_eq_rectangle_density hr).symm
  have hc := T.incoming_constraints hu hH hu₀ hu₁
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp _
    rcases p with ⟨u, v⟩
    have hp' : (u, v) ∈ Icc u₀ u₁ ×ˢ Icc vStar (vStar + H) := by
      simpa only [Goursat.rectangle] using hp
    have hY := (T.characteristic_jets u hp'.1 v hp'.2).2
    have hm : HasDerivWithinAt
        (fun t => C1Solution.stateMass (Z (u, t)))
        (C1Solution.stateMassGap (Z (u, v)) /
          C1Solution.stateRadius (Z (u, v)) *
          C1Solution.stateTheta (Z (u, v)) ^ 2 /
          (2 * C1Solution.stateLam (Z (u, v))))
        (Icc vStar (vStar + H)) v := by
      convert hY.snd.snd.fst using 1; rfl
    change (fderivWithin ℝ
      (fun q => C1Solution.stateMass (Z q)) K (u, v)) (0, 1) =
        routeBMassOutgoingExpr (fun c => routeBField S c (u, v))
    rw [← hmassOut (u, v) hp]
    exact vertical_jet_eq_of_slice_derivative hu
      (by linarith only [hH]) (hS .mass) hp'.1 hp'.2 hm
  · intro p hp _
    rcases p with ⟨u, v⟩
    have hp' : (u, v) ∈ Icc u₀ u₁ ×ˢ Icc vStar (vStar + H) := by
      simpa only [Goursat.rectangle] using hp
    change (fderivWithin ℝ
      (fun q => C1Solution.stateMass (Z q)) K (u, v)) (1, 0) =
        routeBMassIncomingExpr (fun c => routeBField S c (u, v))
    exact hc.2.2 u hp'.1 v hp'.2
  · intro p hp _
    rcases p with ⟨u, v⟩
    have hp' : (u, v) ∈ Icc u₀ u₁ ×ˢ Icc vStar (vStar + H) := by
      simpa only [Goursat.rectangle] using hp
    have hX := (T.characteristic_jets u hp'.1 v hp'.2).1
    have hlam : HasDerivWithinAt
        (fun s => C1Solution.stateLam (Z (s, v)))
        (C1Solution.stateGrav (Z (u, v))) (Icc u₀ u₁) u := by
      convert hX.fst using 1; rfl
    change (fderivWithin ℝ
      (fun q => C1Solution.stateLam (Z q)) K (u, v)) (1, 0) =
        routeBMixedExpr (fun c => routeBField S c (u, v))
    rw [← hgrav (u, v) hp]
    exact horizontal_jet_eq_of_slice_derivative hu
      (by linarith only [hH]) (hS .expansion) hp'.1 hp'.2 hlam
  · intro p hp _
    rcases p with ⟨u, v⟩
    have hp' : (u, v) ∈ Icc u₀ u₁ ×ˢ Icc vStar (vStar + H) := by
      simpa only [Goursat.rectangle] using hp
    have hY := (T.characteristic_jets u hp'.1 v hp'.2).2
    have hnu : HasDerivWithinAt
        (fun t => C1Solution.stateNu (Z (u, t)))
        (C1Solution.stateGrav (Z (u, v)))
        (Icc vStar (vStar + H)) v := by
      convert hY.fst using 1; rfl
    change (fderivWithin ℝ
      (fun q => C1Solution.stateNu (Z q)) K (u, v)) (0, 1) =
        routeBMixedExpr (fun c => routeBField S c (u, v))
    rw [← hgrav (u, v) hp]
    exact vertical_jet_eq_of_slice_derivative hu
      (by linarith only [hH]) (hS .contraction) hp'.1 hp'.2 hnu
  · intro p hp _
    rcases p with ⟨u, v⟩
    have hp' : (u, v) ∈ Icc u₀ u₁ ×ˢ Icc vStar (vStar + H) := by
      simpa only [Goursat.rectangle] using hp
    have hX := (T.characteristic_jets u hp'.1 v hp'.2).1
    have halpha : HasDerivWithinAt
        (fun s => C1Solution.stateAlpha (Z (s, v)))
        (C1Solution.stateGrav (Z (u, v)) *
          C1Solution.statePhi (Z (u, v))) (Icc u₀ u₁) u := by
      convert hX.snd using 1; rfl
    change (fderivWithin ℝ
      (fun q => C1Solution.stateAlpha (Z q)) K (u, v)) (1, 0) =
        routeBMixedExpr (fun c => routeBField S c (u, v)) *
          C1Solution.statePhi (Z (u, v))
    rw [← hgrav (u, v) hp]
    exact horizontal_jet_eq_of_slice_derivative hu
      (by linarith only [hH]) (hS .outgoing) hp'.1 hp'.2 halpha
  · intro p hp _
    rcases p with ⟨u, v⟩
    have hp' : (u, v) ∈ Icc u₀ u₁ ×ˢ Icc vStar (vStar + H) := by
      simpa only [Goursat.rectangle] using hp
    have hY := (T.characteristic_jets u hp'.1 v hp'.2).2
    have hbeta : HasDerivWithinAt
        (fun t => C1Solution.stateBeta (Z (u, t)))
        (C1Solution.stateGrav (Z (u, v)) *
          C1Solution.statePhi (Z (u, v)))
        (Icc vStar (vStar + H)) v := by
      convert hY.snd.fst using 1; rfl
    change (fderivWithin ℝ
      (fun q => C1Solution.stateBeta (Z q)) K (u, v)) (0, 1) =
        routeBMixedExpr (fun c => routeBField S c (u, v)) *
          C1Solution.statePhi (Z (u, v))
    rw [← hgrav (u, v) hp]
    exact vertical_jet_eq_of_slice_derivative hu
      (by linarith only [hH]) (hS .incoming) hp'.1 hp'.2 hbeta

end ChristodoulouBV.Uniqueness

end
