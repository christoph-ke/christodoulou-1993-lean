module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesNext
import ChristodoulouBV.C1Solution.RectangleSeams
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# Matched successor tiles for the Route B lower cover

The incoming trace supplied to the next rectangle is the previous tile's
vertical edge. Vertical ODE uniqueness identifies the remaining five edge
values, including at both corners.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A safe rectangle with the canonical seven-state terminal trace. -/
structure LowerCoverTile {a vStar L : ℝ} (D : LowerCoverBaseData a vStar L)
    (B : C1Solution.SafeRectangleBox) (u₀ u₁ H : ℝ) where
  incoming : ℝ × ℝ → C1Solution.IncomingState
  outgoing : ℝ × ℝ → C1Solution.OutgoingState
  incoming_cont : Continuous incoming
  outgoing_cont : Continuous outgoing
  safe : ∀ p ∈ Goursat.rectangle u₀ u₁ vStar (vStar + H),
    (incoming p, outgoing p) ∈ B.carrier
  incoming_c1 : ContDiffOn ℝ 1 incoming
    (Goursat.rectangle u₀ u₁ vStar (vStar + H))
  outgoing_c1 : ContDiffOn ℝ 1 outgoing
    (Goursat.rectangle u₀ u₁ vStar (vStar + H))
  characteristic_jets :
    ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc vStar (vStar + H),
      HasDerivWithinAt (fun s => incoming (s, v))
        (C1Solution.rectangleF (incoming (u, v), outgoing (u, v)))
          (Icc u₀ u₁) u ∧
      HasDerivWithinAt (fun t => outgoing (u, t))
        (C1Solution.rectangleG (incoming (u, v), outgoing (u, v)))
          (Icc vStar (vStar + H)) v
  terminal_trace : ∀ u ∈ Icc u₀ u₁,
    (incoming (u, vStar), outgoing (u, vStar)) = D.base u

/-- View the constrained first rectangle as the first member of a march. -/
def LowerCoverFirstTile.toLowerCoverTile
    {a vStar L : ℝ} {D : LowerCoverBaseData a vStar L}
    {B : C1Solution.SafeRectangleBox} (T : LowerCoverFirstTile D B) :
    LowerCoverTile D B 0 T.height T.height where
  incoming := T.incoming
  outgoing := T.outgoing
  incoming_cont := T.incoming_cont
  outgoing_cont := T.outgoing_cont
  safe := T.safe
  incoming_c1 := T.incoming_c1
  outgoing_c1 := T.outgoing_c1
  characteristic_jets := T.characteristic_jets
  terminal_trace := T.terminal_trace

/-- Restrict a tile to a smaller positive height without changing its fields. -/
@[expose] def LowerCoverTile.restrict
    {a vStar L u₀ u₁ H η : ℝ} {D : LowerCoverBaseData a vStar L}
    {B : C1Solution.SafeRectangleBox}
    (T : LowerCoverTile D B u₀ u₁ H) (hη : η ≤ H) :
    LowerCoverTile D B u₀ u₁ η where
  incoming := T.incoming
  outgoing := T.outgoing
  incoming_cont := T.incoming_cont
  outgoing_cont := T.outgoing_cont
  safe := by
    intro p hp
    exact T.safe p (by
      have hp' : p ∈ Icc u₀ u₁ ×ˢ Icc vStar (vStar + η) := hp
      exact Goursat.pair_mem_rectangle hp'.1
        ⟨hp'.2.1, by linarith only [hp'.2.2, hη]⟩)
  incoming_c1 := T.incoming_c1.mono (by
    intro p hp
    have hp' : p ∈ Icc u₀ u₁ ×ˢ Icc vStar (vStar + η) := hp
    exact Goursat.pair_mem_rectangle hp'.1
      ⟨hp'.2.1, by linarith only [hp'.2.2, hη]⟩)
  outgoing_c1 := T.outgoing_c1.mono (by
    intro p hp
    have hp' : p ∈ Icc u₀ u₁ ×ˢ Icc vStar (vStar + η) := hp
    exact Goursat.pair_mem_rectangle hp'.1
      ⟨hp'.2.1, by linarith only [hp'.2.2, hη]⟩)
  characteristic_jets := by
    intro u hu v hv
    obtain ⟨hXu, hYv⟩ := T.characteristic_jets u hu v
      ⟨hv.1, by linarith only [hv.2, hη]⟩
    exact ⟨hXu, hYv.mono (by
      intro t ht
      exact ⟨ht.1, by linarith only [ht.2, hη]⟩)⟩
  terminal_trace := T.terminal_trace

/-- A matched positive-height successor tile exists below any given safe
tile. Its full state equals the preceding tile's state on the vertical join. -/
theorem LowerCoverBaseData.exists_matched_next_tile
    {a vStar L uPrev u₀ u₁ H : ℝ} (D : LowerCoverBaseData a vStar L)
    (hPrev : uPrev < u₀) (hu₀ : 0 ≤ u₀) (hu : u₀ < u₁)
    (hu₁a : u₁ ≤ a) (hoff : u₁ < vStar) (hH : 0 < H)
    (B₁ B₂ : C1Solution.SafeRectangleBox)
    (T : LowerCoverTile D B₁ uPrev u₀ H)
    (hcenter : B₂.center = D.base u₀)
    (hbaseNear : ∀ u ∈ Icc u₀ u₁,
      dist (D.base u) (D.base u₀) ≤ B₂.radius / 4)
    (hwidthSize : B₂.radius / 2 + B₂.valueBound * (u₁ - u₀) < B₂.radius)
    (hwidthSmall : (B₂.derivBound : ℝ) * (u₁ - u₀) < 1) :
    ∃ η : ℝ, 0 < η ∧ η < H ∧
      ∃ T₂ : LowerCoverTile D B₂ u₀ u₁ η,
        ∀ v ∈ Icc vStar (vStar + η),
          (T.incoming (u₀, v), T.outgoing (u₀, v)) =
            (T₂.incoming (u₀, v), T₂.outgoing (u₀, v)) := by
  let x₀ : ℝ → C1Solution.IncomingState := fun v => T.incoming (u₀, v)
  let Z : ℝ → C1Solution.RectangleState :=
    fun v => (T.incoming (u₀, v), T.outgoing (u₀, v))
  have hu₀prev : u₀ ∈ Icc uPrev u₀ := ⟨hPrev.le, le_rfl⟩
  have hcorner : Z vStar = D.base u₀ := T.terminal_trace u₀ hu₀prev
  have hZcont : Continuous Z :=
    (T.incoming_cont.comp (continuous_const.prodMk continuous_id)).prodMk
      (T.outgoing_cont.comp (continuous_const.prodMk continuous_id))
  obtain ⟨δ, hδ, hnear⟩ := (Metric.continuousAt_iff.mp
    (show ContinuousAt Z vStar from hZcont.continuousAt))
      B₂.radius B₂.radius_pos
  let H' := min (H / 2) (δ / 2)
  have hH' : 0 < H' := lt_min (by linarith only [hH])
    (by linarith only [hδ])
  have hH'H : H' < H := by
    have hle : H' ≤ H / 2 := min_le_left _ _
    linarith only [hle, hH]
  have hH'δ : H' ≤ δ / 2 := min_le_right _ _
  have hx₀ : Continuous x₀ :=
    T.incoming_cont.comp (continuous_const.prodMk continuous_id)
  obtain ⟨x₀', hx₀'cont, hx₀'deriv⟩ :=
    exists_vertical_edge_derivative_data hPrev (by linarith only [hH])
      T.incoming T.incoming_c1 hu₀prev
  have hx₀'cont' : ContinuousOn x₀' (Icc vStar (vStar + H')) :=
    hx₀'cont.mono (by
      intro v hv
      exact ⟨hv.1, by linarith only [hv.2, hH'H]⟩)
  have hx₀'deriv' : ∀ v ∈ Icc vStar (vStar + H'),
      HasDerivWithinAt x₀ (x₀' v) (Icc vStar (vStar + H')) v := by
    intro v hv
    exact (hx₀'deriv v ⟨hv.1, by linarith only [hv.2, hH'H]⟩).mono
      (by intro t ht; exact ⟨ht.1, by linarith only [ht.2, hH'H]⟩)
  obtain ⟨η, hη, hηH', X, Y, hX, hY, hball, hCX, hCY,
    hjet, hleft, hbottom⟩ :=
    D.exists_next_tile hu₀ hu hu₁a hoff hH' B₂ hcenter
      hbaseNear hwidthSize hwidthSmall x₀ x₀' hx₀ hx₀'cont'
      hx₀'deriv' (congrArg Prod.fst hcorner)
  have hηH : η < H := hηH'.trans hH'H
  have hZball : ∀ v ∈ Icc vStar (vStar + η), Z v ∈ B₂.carrier := by
    intro v hv
    rw [C1Solution.SafeRectangleBox.carrier, Metric.mem_closedBall, hcenter]
    rw [← hcorner]
    exact (hnear (by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hv.1)]
      linarith only [hv.2, hηH', hH'δ, hδ])).le
  have hYedge : ∀ v ∈ Icc vStar (vStar + η),
      (X (u₀, v), Y (u₀, v)) = Z v := by
    apply C1Solution.left_full_trace_eq (by linarith only [hη])
      B₂ x₀ X Y Z
    · exact (hY.comp (continuous_const.prodMk continuous_id)).continuousOn
    · exact hZcont.snd.continuousOn
    · exact hleft
    · intro v hv; rfl
    · intro v hv
      rw [← hleft v hv]
      exact hball (u₀, v) (Goursat.pair_mem_rectangle
        ⟨le_rfl, hu.le⟩ hv)
    · exact hZball
    · intro v hv
      simpa only [hleft v hv] using (hjet u₀ ⟨le_rfl, hu.le⟩ v hv).2
    · intro v hv
      exact (T.characteristic_jets u₀ hu₀prev v
        ⟨hv.1, by linarith only [hv.2, hηH]⟩).2.mono (by
          intro t ht
          exact ⟨ht.1, by linarith only [ht.2, hηH]⟩)
    · exact congrArg Prod.snd ((hbottom u₀ ⟨le_rfl, hu.le⟩).trans
        hcorner.symm)
  let T₂ : LowerCoverTile D B₂ u₀ u₁ η := {
    incoming := X
    outgoing := Y
    incoming_cont := hX
    outgoing_cont := hY
    safe := hball
    incoming_c1 := hCX
    outgoing_c1 := hCY
    characteristic_jets := hjet
    terminal_trace := hbottom
  }
  refine ⟨η, hη, hηH, T₂, ?_⟩
  intro v hv
  exact (hYedge v hv).symm

end ChristodoulouBV.Uniqueness

end
