module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesBaseData
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# First constrained Route B lower tile

The first rectangle has the canonical terminal base, the prescribed incoming
gauge on `u = 0`, and the three propagated incoming constraints. Its outgoing
initial-edge state is constructed by the rectangle theorem.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A safe first lower tile with its prescribed characteristic data and the
three incoming constraints. -/
structure LowerCoverFirstTile {a vStar L : ℝ}
    (D : LowerCoverBaseData a vStar L)
    (B : C1Solution.SafeRectangleBox) where
  height : ℝ
  height_pos : 0 < height
  height_lt_a : height < a
  height_lt_L : height < L
  incoming : ℝ × ℝ → C1Solution.IncomingState
  outgoing : ℝ × ℝ → C1Solution.OutgoingState
  incoming_cont : Continuous incoming
  outgoing_cont : Continuous outgoing
  safe : ∀ p ∈ Goursat.rectangle 0 height vStar (vStar + height),
    (incoming p, outgoing p) ∈ B.carrier
  integral_equations :
    ∀ p ∈ Goursat.rectangle 0 height vStar (vStar + height),
      incoming p = D.initialIncoming p.2 + ∫ s in (0 : ℝ)..p.1,
        C1Solution.rectangleF (incoming (s, p.2), outgoing (s, p.2)) ∧
      outgoing p = (D.base p.1).2 + ∫ t in vStar..p.2,
        C1Solution.rectangleG (incoming (p.1, t), outgoing (p.1, t))
  incoming_c1 : ContDiffOn ℝ 1 incoming
    (Goursat.rectangle 0 height vStar (vStar + height))
  outgoing_c1 : ContDiffOn ℝ 1 outgoing
    (Goursat.rectangle 0 height vStar (vStar + height))
  characteristic_jets :
    ∀ u ∈ Icc 0 height, ∀ v ∈ Icc vStar (vStar + height),
      HasDerivWithinAt (fun s => incoming (s, v))
        (C1Solution.rectangleF (incoming (u, v), outgoing (u, v)))
          (Icc 0 height) u ∧
      HasDerivWithinAt (fun t => outgoing (u, t))
        (C1Solution.rectangleG (incoming (u, v), outgoing (u, v)))
          (Icc vStar (vStar + height)) v
  terminal_trace : ∀ u ∈ Icc 0 height,
    (incoming (u, vStar), outgoing (u, vStar)) = D.base u
  initial_pair : ∀ v ∈ Icc vStar (vStar + height),
    incoming (0, v) = D.initialIncoming v
  radius_in : ∀ u ∈ Icc 0 height, ∀ v ∈ Icc vStar (vStar + height),
    (fderivWithin ℝ
      (fun p => C1Solution.stateRadius (incoming p, outgoing p))
      (Goursat.rectangle 0 height vStar (vStar + height)) (u, v)) (1, 0) =
        C1Solution.stateNu (incoming (u, v), outgoing (u, v))
  psi_in : ∀ u ∈ Icc 0 height, ∀ v ∈ Icc vStar (vStar + height),
    (fderivWithin ℝ
      (fun p => C1Solution.statePsi (incoming p, outgoing p))
      (Goursat.rectangle 0 height vStar (vStar + height)) (u, v)) (1, 0) =
        C1Solution.stateBeta (incoming (u, v), outgoing (u, v))
  mass_in : ∀ u ∈ Icc 0 height, ∀ v ∈ Icc vStar (vStar + height),
    (fderivWithin ℝ
      (fun p => C1Solution.stateMass (incoming p, outgoing p))
      (Goursat.rectangle 0 height vStar (vStar + height)) (u, v)) (1, 0) =
        (1 - 2 * C1Solution.stateMass (incoming (u, v), outgoing (u, v)) /
          C1Solution.stateRadius (incoming (u, v), outgoing (u, v))) *
          C1Solution.stateZeta (incoming (u, v), outgoing (u, v)) ^ 2 /
          (2 * C1Solution.stateNu (incoming (u, v), outgoing (u, v)))

/-- The prescribed initial incoming state fixes `λ` and `α` on `u = 0`. -/
theorem LowerCoverFirstTile.initial_incoming_gauge
    {a vStar L : ℝ} {D : LowerCoverBaseData a vStar L}
    {B : C1Solution.SafeRectangleBox} (T : LowerCoverFirstTile D B)
    {v : ℝ} (hv : v ∈ Icc vStar (vStar + T.height)) :
    T.incoming (0, v) = (1 / 2, D.alpha₀ v) := by
  rw [T.initial_pair v hv]
  exact D.initial_incoming_gauge v
    ⟨hv.1, by linarith only [hv.2, T.height_lt_L]⟩

/-- The corrected characteristic input produces a safe first tile with the
canonical terminal state, incoming gauge, and all incoming constraints. -/
theorem LowerCoverBaseData.exists_first_constrained_tile
    {a vStar L : ℝ} (D : LowerCoverBaseData a vStar L)
    (ha : 0 < a) (hL : 0 < L) (hoff : a < vStar)
    (B : C1Solution.SafeRectangleBox)
    (hcenter : B.center = D.base 0) :
    Nonempty (LowerCoverFirstTile D B) := by
  obtain ⟨h, hh, hha, hhL, X, Y, hX, hY, hball, heq,
    hCX, hCY, hjet, hbase⟩ :=
    D.toLowerTileEdgeData.exists_first_tile ha hL hoff B hcenter
  have hball' : ∀ p ∈ Goursat.rectangle 0 h vStar (vStar + h),
      (X p, Y p) ∈ B.carrier := by
    intro p hp
    simpa only [C1Solution.SafeRectangleBox.carrier,
      Metric.mem_closedBall] using hball p hp
  have hleft : ∀ v ∈ Icc vStar (vStar + h),
      X (0, v) = D.initialIncoming v := by
    intro v hv
    have he := (heq (0, v)
      (Goursat.pair_mem_rectangle ⟨le_rfl, hh.le⟩ hv)).1
    simpa only [intervalIntegral.integral_same, add_zero] using he
  have hconstraints := D.first_tile_incoming_constraints hh hha.le B
    X Y hCX hCY hball' hjet hbase
  exact ⟨{
    height := h
    height_pos := hh
    height_lt_a := hha
    height_lt_L := hhL
    incoming := X
    outgoing := Y
    incoming_cont := hX
    outgoing_cont := hY
    safe := hball'
    integral_equations := heq
    incoming_c1 := hCX
    outgoing_c1 := hCY
    characteristic_jets := hjet
    terminal_trace := hbase
    initial_pair := hleft
    radius_in := hconstraints.1
    psi_in := hconstraints.2.1
    mass_in := hconstraints.2.2
  }⟩

/-- The outgoing radius equation and the corner value recover the initial
radius gauge throughout the first tile. -/
theorem LowerCoverFirstTile.initial_radius_gauge
    {a vStar L : ℝ} {D : LowerCoverBaseData a vStar L}
    {B : C1Solution.SafeRectangleBox} (T : LowerCoverFirstTile D B) :
    ∀ v ∈ Icc vStar (vStar + T.height),
      C1Solution.stateRadius (T.incoming (0, v), T.outgoing (0, v)) =
        v / 2 := by
  let P : C1Solution.OutgoingState →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
        ((ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × ℝ))).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × (ℝ × ℝ))))))
  let e : ℝ → ℝ := fun v =>
    C1Solution.stateRadius (T.incoming (0, v), T.outgoing (0, v)) - v / 2
  have hecont : ContinuousOn e (Icc vStar (vStar + T.height)) := by
    have hpath : Continuous (fun v : ℝ => ((0 : ℝ), v)) :=
      continuous_const.prodMk continuous_id
    have hR : Continuous (fun v : ℝ => P (T.outgoing (0, v))) :=
      P.continuous.comp (T.outgoing_cont.comp hpath)
    exact hR.continuousOn.sub (continuous_id.div_const 2).continuousOn
  have hederiv : ∀ v ∈ Icc vStar (vStar + T.height),
      HasDerivWithinAt e 0 (Icc vStar (vStar + T.height)) v := by
    intro v hv
    have hY := (T.characteristic_jets 0 ⟨le_rfl, T.height_pos.le⟩ v hv).2
    have hR := P.hasFDerivAt.comp_hasDerivWithinAt v hY
    change HasDerivWithinAt
      (fun t => C1Solution.stateRadius (T.incoming (0, t), T.outgoing (0, t)))
      (C1Solution.stateLam (T.incoming (0, v), T.outgoing (0, v)))
      (Icc vStar (vStar + T.height)) v at hR
    have hLam : C1Solution.stateLam
        (T.incoming (0, v), T.outgoing (0, v)) = 1 / 2 := by
      change (T.incoming (0, v)).1 = 1 / 2
      rw [T.initial_incoming_gauge hv]
    rw [hLam] at hR
    have hid : HasDerivWithinAt (fun t : ℝ => t / 2) (1 / 2)
        (Icc vStar (vStar + T.height)) v :=
      ((hasDerivAt_id v).div_const 2).hasDerivWithinAt
    convert hR.sub hid using 1
    simp only [sub_self]
  have hinit : e vStar = 0 := by
    have h := T.terminal_trace 0 ⟨le_rfl, T.height_pos.le⟩
    dsimp [e]
    rw [h, D.initial_radius_corner]
    ring
  intro v hv
  have hz := C1Solution.eq_zero_of_zero_vertical_derivative
    (b₀ := vStar) (b₁ := vStar + T.height)
    (by linarith only [T.height_pos]) hecont hederiv hinit v hv
  exact sub_eq_zero.mp hz

end ChristodoulouBV.Uniqueness

end
