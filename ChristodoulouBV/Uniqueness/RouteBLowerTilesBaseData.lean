module

public import ChristodoulouBV.Uniqueness.RouteBLowerTiles
public import ChristodoulouBV.C1Solution.RectangleMassConstraintState
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# Tangential data for the Route B lower tiles

The characteristic rectangle theorem prescribes only two incoming and five
outgoing variables. The canonical terminal trace has three additional
incoming equations. They are needed to propagate the radius, scalar-radius,
and mass constraints into each tile.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Characteristic data with the three lower-edge constraints and the
prescribed initial gauge. The incoming lower-edge equations are already
fields of `LowerTileEdgeData`. -/
structure LowerCoverBaseData (a vStar L : ℝ)
    extends LowerTileEdgeData a vStar L where
  alpha₀ : ℝ → ℝ
  baseOutgoingPrime_radius : ∀ u ∈ Icc 0 a,
    (baseOutgoingPrime u).2.2.2.1 = C1Solution.stateNu (base u)
  baseOutgoingPrime_psi : ∀ u ∈ Icc 0 a,
    (baseOutgoingPrime u).2.2.2.2 = C1Solution.stateBeta (base u)
  baseOutgoingPrime_mass : ∀ u ∈ Icc 0 a,
    (baseOutgoingPrime u).2.2.1 =
      (1 - 2 * C1Solution.stateMass (base u) /
        C1Solution.stateRadius (base u)) *
        C1Solution.stateZeta (base u) ^ 2 /
        (2 * C1Solution.stateNu (base u))
  initial_incoming_gauge : ∀ v ∈ Icc vStar (vStar + L),
    initialIncoming v = (1 / 2, alpha₀ v)
  initial_radius_corner : C1Solution.stateRadius (base 0) = vStar / 2

/-- The lower-edge mass derivative of a tile is the derivative supplied by
the canonical base trace. -/
theorem LowerCoverBaseData.mass_bottom_jet
    {a vStar L h : ℝ} (D : LowerCoverBaseData a vStar L)
    (hh : 0 < h) (hha : h ≤ a)
    (X : ℝ × ℝ → C1Solution.IncomingState)
    (Y : ℝ × ℝ → C1Solution.OutgoingState)
    (hY : ContDiffOn ℝ 1 Y
      (Goursat.rectangle 0 h vStar (vStar + h)))
    (hbase : ∀ u ∈ Icc 0 h,
      (X (u, vStar), Y (u, vStar)) = D.base u) :
    ∀ u ∈ Icc 0 h,
      (fderivWithin ℝ (fun p => C1Solution.stateMass (X p, Y p))
        (Goursat.rectangle 0 h vStar (vStar + h)) (u, vStar)) (1, 0) =
        (1 - 2 * C1Solution.stateMass (X (u, vStar), Y (u, vStar)) /
          C1Solution.stateRadius (X (u, vStar), Y (u, vStar))) *
          C1Solution.stateZeta (X (u, vStar), Y (u, vStar)) ^ 2 /
          (2 * C1Solution.stateNu (X (u, vStar), Y (u, vStar))) := by
  let P : C1Solution.OutgoingState →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × ℝ))).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × (ℝ × ℝ)))))
  have hYedge (u : ℝ) (hu : u ∈ Icc 0 h) :
      Y (u, vStar) = (D.base u).2 :=
    congrArg Prod.snd (hbase u hu)
  have hderiv (u : ℝ) (hu : u ∈ Icc 0 h) :
      HasDerivWithinAt (fun t => (D.base t).2)
        (D.baseOutgoingPrime u) (Icc 0 h) u :=
    (D.baseOutgoing_deriv u ⟨hu.1, hu.2.trans hha⟩).mono
      (fun _ ht => ⟨ht.1, ht.2.trans hha⟩)
  intro u hu
  have hm := C1Solution.projected_outgoing_bottom_jet_eq
    hh (by linarith only [hh]) P Y
    (fun t => (D.base t).2) D.baseOutgoingPrime
    hY hYedge hderiv hu
  change (fderivWithin ℝ
      (fun p => C1Solution.stateMass (X p, Y p))
      (Goursat.rectangle 0 h vStar (vStar + h)) (u, vStar)) (1, 0) = _
  change (fderivWithin ℝ
      (fun p => C1Solution.stateMass (X p, Y p))
      (Goursat.rectangle 0 h vStar (vStar + h)) (u, vStar)) (1, 0) =
      (D.baseOutgoingPrime u).2.2.1 at hm
  rw [hm, D.baseOutgoingPrime_mass u ⟨hu.1, hu.2.trans hha⟩]
  rw [hbase u hu]

/-- The lower-edge tangential equations propagate the three incoming
constraints through any safe first tile with the canonical base trace. -/
theorem LowerCoverBaseData.first_tile_incoming_constraints
    {a vStar L h : ℝ} (D : LowerCoverBaseData a vStar L)
    (hh : 0 < h) (hha : h ≤ a)
    (B : C1Solution.SafeRectangleBox)
    (X : ℝ × ℝ → C1Solution.IncomingState)
    (Y : ℝ × ℝ → C1Solution.OutgoingState)
    (hX : ContDiffOn ℝ 1 X
      (Goursat.rectangle 0 h vStar (vStar + h)))
    (hY : ContDiffOn ℝ 1 Y
      (Goursat.rectangle 0 h vStar (vStar + h)))
    (hball : ∀ p ∈ Goursat.rectangle 0 h vStar (vStar + h),
      (X p, Y p) ∈ B.carrier)
    (hjet : ∀ u ∈ Icc 0 h, ∀ v ∈ Icc vStar (vStar + h),
      HasDerivWithinAt (fun s => X (s, v))
        (C1Solution.rectangleF (X (u, v), Y (u, v))) (Icc 0 h) u ∧
      HasDerivWithinAt (fun t => Y (u, t))
        (C1Solution.rectangleG (X (u, v), Y (u, v)))
          (Icc vStar (vStar + h)) v)
    (hbase : ∀ u ∈ Icc 0 h,
      (X (u, vStar), Y (u, vStar)) = D.base u) :
    (∀ u ∈ Icc 0 h, ∀ v ∈ Icc vStar (vStar + h),
      (fderivWithin ℝ (fun p => C1Solution.stateRadius (X p, Y p))
        (Goursat.rectangle 0 h vStar (vStar + h)) (u, v)) (1, 0) =
        C1Solution.stateNu (X (u, v), Y (u, v))) ∧
    (∀ u ∈ Icc 0 h, ∀ v ∈ Icc vStar (vStar + h),
      (fderivWithin ℝ (fun p => C1Solution.statePsi (X p, Y p))
        (Goursat.rectangle 0 h vStar (vStar + h)) (u, v)) (1, 0) =
        C1Solution.stateBeta (X (u, v), Y (u, v))) ∧
    (∀ u ∈ Icc 0 h, ∀ v ∈ Icc vStar (vStar + h),
      (fderivWithin ℝ (fun p => C1Solution.stateMass (X p, Y p))
        (Goursat.rectangle 0 h vStar (vStar + h)) (u, v)) (1, 0) =
        (1 - 2 * C1Solution.stateMass (X (u, v), Y (u, v)) /
          C1Solution.stateRadius (X (u, v), Y (u, v))) *
          C1Solution.stateZeta (X (u, v), Y (u, v)) ^ 2 /
          (2 * C1Solution.stateNu (X (u, v), Y (u, v)))) := by
  have hYedge (u : ℝ) (hu : u ∈ Icc 0 h) :
      Y (u, vStar) = (D.base u).2 :=
    congrArg Prod.snd (hbase u hu)
  have hderiv (u : ℝ) (hu : u ∈ Icc 0 h) :
      HasDerivWithinAt (fun t => (D.base t).2)
        (D.baseOutgoingPrime u) (Icc 0 h) u :=
    (D.baseOutgoing_deriv u ⟨hu.1, hu.2.trans hha⟩).mono
      (fun _ ht => ⟨ht.1, ht.2.trans hha⟩)
  apply C1Solution.rectangle_incoming_constraints_of_lower_edge
    hh (by linarith only [hh]) B X Y
    (fun t => (D.base t).2) D.baseOutgoingPrime
    hX hY hball hjet hYedge hderiv
  · intro u hu
    have h := D.baseOutgoingPrime_radius u ⟨hu.1, hu.2.trans hha⟩
    simpa only [C1Solution.stateNu] using h
  · intro u hu
    have h := D.baseOutgoingPrime_psi u ⟨hu.1, hu.2.trans hha⟩
    simpa only [C1Solution.stateBeta] using h
  · exact D.mass_bottom_jet hh hha X Y hY hbase

end ChristodoulouBV.Uniqueness

end
