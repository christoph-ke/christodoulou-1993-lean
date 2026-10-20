module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesClassicalTransport
import ChristodoulouBV.C1Solution.RectangleMassConstraintState
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# Amplitude equations on a lower tile

The rectangle transport calculus derives the theta and zeta equations from
the semilinear seven-state system and propagated radius constraints.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Both derived scalar amplitudes satisfy their closed-tile classical
relative-jet equations. -/
theorem LowerCoverTile.amplitude_classical_jets
    {a vStar L u₀ u₁ H b : ℝ} {D : LowerCoverBaseData a vStar L}
    {B : C1Solution.SafeRectangleBox}
    (T : LowerCoverTile D B u₀ u₁ H)
    (hu : u₀ < u₁) (hH : 0 < H)
    (hu₀ : 0 ≤ u₀) (hu₁ : u₁ ≤ a) :
    let K := Goursat.rectangle u₀ u₁ vStar (vStar + H)
    let S := rectangleStateFields fun p => (T.incoming p, T.outgoing p)
    RouteBLocalJetEquation b K S
      routeBThetaExpr routeBThetaIncomingExpr (1, 0) ∧
    RouteBLocalJetEquation b K S
      routeBZetaExpr routeBZetaOutgoingExpr (0, 1) := by
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
  have hrC1 : ContDiffOn ℝ 1
      (fun p => C1Solution.stateRadius (Z p)) K := hS .radius
  have hψC1 : ContDiffOn ℝ 1
      (fun p => C1Solution.statePsi (Z p)) K := by
    change ContDiffOn ℝ 1 (fun p => (T.outgoing p).2.2.2.2) K
    exact T.outgoing_c1.snd.snd.snd.snd
  have hThetaC1 : ContDiffOn ℝ 1
      (fun p => C1Solution.stateTheta (Z p)) K := by
    change ContDiffOn ℝ 1 (fun p =>
      C1Solution.stateAlpha (Z p) -
        C1Solution.stateLam (Z p) * C1Solution.statePhi (Z p)) K
    exact (hS .outgoing).sub ((hS .expansion).mul (hS .scalar))
  have hZetaC1 : ContDiffOn ℝ 1
      (fun p => C1Solution.stateZeta (Z p)) K := by
    change ContDiffOn ℝ 1 (fun p =>
      C1Solution.stateBeta (Z p) -
        C1Solution.stateNu (Z p) * C1Solution.statePhi (Z p)) K
    exact (hS .incoming).sub ((hS .contraction).mul (hS .scalar))
  have hc := T.incoming_constraints hu hH hu₀ hu₁
  have hru : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc vStar (vStar + H),
      HasDerivWithinAt
        (fun s => C1Solution.stateRadius (Z (s, v)))
        (C1Solution.stateNu (Z (u, v))) (Icc u₀ u₁) u := by
    intro u hu' v hv'
    have hcoord :=
      (C1Solution.coordinate_derivatives_of_contDiffOn_rectangle
        hu (by linarith only [hH]) hrC1 hu' hv').1
    rw [hc.1 u hu' v hv'] at hcoord
    exact hcoord
  have hψu : ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc vStar (vStar + H),
      HasDerivWithinAt
        (fun s => C1Solution.statePsi (Z (s, v)))
        (C1Solution.stateBeta (Z (u, v))) (Icc u₀ u₁) u := by
    intro u hu' v hv'
    have hcoord :=
      (C1Solution.coordinate_derivatives_of_contDiffOn_rectangle
        hu (by linarith only [hH]) hψC1 hu' hv').1
    rw [hc.2.1 u hu' v hv'] at hcoord
    exact hcoord
  constructor
  · intro p hp _
    rcases p with ⟨u, v⟩
    have hp' : (u, v) ∈ Icc u₀ u₁ ×ˢ Icc vStar (vStar + H) := by
      simpa only [Goursat.rectangle] using hp
    have htrans := C1Solution.rectangle_mass_transport_derivatives
      B T.incoming T.outgoing T.safe T.characteristic_jets
        hru hψu hp'.1 hp'.2
    have htheta := htrans.2.1
    change (fderivWithin ℝ
      (fun q => C1Solution.stateTheta (Z q)) K (u, v)) (1, 0) =
        routeBThetaIncomingExpr (fun c => routeBField S c (u, v))
    have hjet := horizontal_jet_eq_of_slice_derivative hu
      (by linarith only [hH]) hThetaC1 hp'.1 hp'.2 htheta
    have hrhs : routeBThetaIncomingExpr
        (fun c => routeBField S c (u, v)) =
        -C1Solution.stateLam (Z (u, v)) *
          C1Solution.stateZeta (Z (u, v)) /
          C1Solution.stateRadius (Z (u, v)) := by
      change -(C1Solution.stateLam (Z (u, v)) /
        C1Solution.stateRadius (Z (u, v)) *
          C1Solution.stateZeta (Z (u, v))) = _
      ring
    rw [hrhs]
    exact hjet
  · intro p hp _
    rcases p with ⟨u, v⟩
    have hp' : (u, v) ∈ Icc u₀ u₁ ×ˢ Icc vStar (vStar + H) := by
      simpa only [Goursat.rectangle] using hp
    have htrans := C1Solution.rectangle_mass_transport_derivatives
      B T.incoming T.outgoing T.safe T.characteristic_jets
        hru hψu hp'.1 hp'.2
    have hzeta := htrans.2.2.2.2.2
    change (fderivWithin ℝ
      (fun q => C1Solution.stateZeta (Z q)) K (u, v)) (0, 1) =
        routeBZetaOutgoingExpr (fun c => routeBField S c (u, v))
    have hjet := vertical_jet_eq_of_slice_derivative hu
      (by linarith only [hH]) hZetaC1 hp'.1 hp'.2 hzeta
    have hrhs : routeBZetaOutgoingExpr
        (fun c => routeBField S c (u, v)) =
        -C1Solution.stateNu (Z (u, v)) *
          C1Solution.stateTheta (Z (u, v)) /
          C1Solution.stateRadius (Z (u, v)) := by
      change -(C1Solution.stateNu (Z (u, v)) /
        C1Solution.stateRadius (Z (u, v)) *
          C1Solution.stateTheta (Z (u, v))) = _
      ring
    rw [hrhs]
    exact hjet

end ChristodoulouBV.Uniqueness

end
