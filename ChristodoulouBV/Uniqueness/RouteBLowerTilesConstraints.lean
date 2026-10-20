module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesFiniteMarch
public import ChristodoulouBV.C1Solution.RectangleMassConstraintState
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# Incoming constraints on every lower-cover tile

The canonical terminal base satisfies the three tangential equations. The
rectangle propagation theorem carries them through each safe tile, including
its closed top and side edges.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The incoming mass derivative at the bottom of an arbitrary lower-cover
tile is the derivative of the canonical terminal base. -/
theorem LowerCoverTile.mass_bottom_jet
    {a vStar L u₀ u₁ H : ℝ} {D : LowerCoverBaseData a vStar L}
    {B : C1Solution.SafeRectangleBox}
    (T : LowerCoverTile D B u₀ u₁ H)
    (hu : u₀ < u₁) (hH : 0 < H)
    (hu₀ : 0 ≤ u₀) (hu₁ : u₁ ≤ a) :
    ∀ u ∈ Icc u₀ u₁,
      (fderivWithin ℝ
        (fun p => C1Solution.stateMass (T.incoming p, T.outgoing p))
        (Goursat.rectangle u₀ u₁ vStar (vStar + H)) (u, vStar)) (1, 0) =
        (1 - 2 * C1Solution.stateMass
          (T.incoming (u, vStar), T.outgoing (u, vStar)) /
          C1Solution.stateRadius
            (T.incoming (u, vStar), T.outgoing (u, vStar))) *
          C1Solution.stateZeta
            (T.incoming (u, vStar), T.outgoing (u, vStar)) ^ 2 /
          (2 * C1Solution.stateNu
            (T.incoming (u, vStar), T.outgoing (u, vStar))) := by
  let P : C1Solution.OutgoingState →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × ℝ))).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × (ℝ × ℝ)))))
  have hYedge (u : ℝ) (hu' : u ∈ Icc u₀ u₁) :
      T.outgoing (u, vStar) = (D.base u).2 :=
    congrArg Prod.snd (T.terminal_trace u hu')
  have hderiv (u : ℝ) (hu' : u ∈ Icc u₀ u₁) :
      HasDerivWithinAt (fun t => (D.base t).2)
        (D.baseOutgoingPrime u) (Icc u₀ u₁) u :=
    (D.baseOutgoing_deriv u ⟨hu₀.trans hu'.1, hu'.2.trans hu₁⟩).mono
      (fun _ ht => ⟨hu₀.trans ht.1, ht.2.trans hu₁⟩)
  intro u hu'
  have hm := C1Solution.projected_outgoing_bottom_jet_eq
    hu (by linarith only [hH]) P T.outgoing
    (fun t => (D.base t).2) D.baseOutgoingPrime
    T.outgoing_c1 hYedge hderiv hu'
  change (fderivWithin ℝ
      (fun p => C1Solution.stateMass (T.incoming p, T.outgoing p))
      (Goursat.rectangle u₀ u₁ vStar (vStar + H)) (u, vStar)) (1, 0) =
      (D.baseOutgoingPrime u).2.2.1 at hm
  rw [hm, D.baseOutgoingPrime_mass u
    ⟨hu₀.trans hu'.1, hu'.2.trans hu₁⟩]
  rw [T.terminal_trace u hu']

/-- All three incoming constraints hold throughout a safe lower-cover tile. -/
theorem LowerCoverTile.incoming_constraints
    {a vStar L u₀ u₁ H : ℝ} {D : LowerCoverBaseData a vStar L}
    {B : C1Solution.SafeRectangleBox}
    (T : LowerCoverTile D B u₀ u₁ H)
    (hu : u₀ < u₁) (hH : 0 < H)
    (hu₀ : 0 ≤ u₀) (hu₁ : u₁ ≤ a) :
    (∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc vStar (vStar + H),
      (fderivWithin ℝ
        (fun p => C1Solution.stateRadius (T.incoming p, T.outgoing p))
        (Goursat.rectangle u₀ u₁ vStar (vStar + H)) (u, v)) (1, 0) =
        C1Solution.stateNu (T.incoming (u, v), T.outgoing (u, v))) ∧
    (∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc vStar (vStar + H),
      (fderivWithin ℝ
        (fun p => C1Solution.statePsi (T.incoming p, T.outgoing p))
        (Goursat.rectangle u₀ u₁ vStar (vStar + H)) (u, v)) (1, 0) =
        C1Solution.stateBeta (T.incoming (u, v), T.outgoing (u, v))) ∧
    (∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc vStar (vStar + H),
      (fderivWithin ℝ
        (fun p => C1Solution.stateMass (T.incoming p, T.outgoing p))
        (Goursat.rectangle u₀ u₁ vStar (vStar + H)) (u, v)) (1, 0) =
        (1 - 2 * C1Solution.stateMass
          (T.incoming (u, v), T.outgoing (u, v)) /
          C1Solution.stateRadius
            (T.incoming (u, v), T.outgoing (u, v))) *
          C1Solution.stateZeta
            (T.incoming (u, v), T.outgoing (u, v)) ^ 2 /
          (2 * C1Solution.stateNu
            (T.incoming (u, v), T.outgoing (u, v)))) := by
  have hYedge (u : ℝ) (hu' : u ∈ Icc u₀ u₁) :
      T.outgoing (u, vStar) = (D.base u).2 :=
    congrArg Prod.snd (T.terminal_trace u hu')
  have hderiv (u : ℝ) (hu' : u ∈ Icc u₀ u₁) :
      HasDerivWithinAt (fun t => (D.base t).2)
        (D.baseOutgoingPrime u) (Icc u₀ u₁) u :=
    (D.baseOutgoing_deriv u ⟨hu₀.trans hu'.1, hu'.2.trans hu₁⟩).mono
      (fun _ ht => ⟨hu₀.trans ht.1, ht.2.trans hu₁⟩)
  apply C1Solution.rectangle_incoming_constraints_of_lower_edge
    hu (by linarith only [hH]) B T.incoming T.outgoing
    (fun t => (D.base t).2) D.baseOutgoingPrime
    T.incoming_c1 T.outgoing_c1 T.safe T.characteristic_jets
    hYedge hderiv
  · intro u hu'
    have h := D.baseOutgoingPrime_radius u
      ⟨hu₀.trans hu'.1, hu'.2.trans hu₁⟩
    simpa only [C1Solution.stateNu] using h
  · intro u hu'
    have h := D.baseOutgoingPrime_psi u
      ⟨hu₀.trans hu'.1, hu'.2.trans hu₁⟩
    simpa only [C1Solution.stateBeta] using h
  · exact T.mass_bottom_jet hu hH hu₀ hu₁

end ChristodoulouBV.Uniqueness

end
