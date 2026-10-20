module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesGaugeMarch
public import ChristodoulouBV.Uniqueness.RouteBLowerTilesFields
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# Assembly of a finite lower-tile march

The full-jet tile glue supplies one relative C¹ seven-state field. The
first-tile preservation result passes its prescribed initial gauge through
the whole march.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A marched finite cover has one safe C¹ state, the canonical terminal
trace, and the prescribed incoming pair and radius on `u = 0`. -/
theorem LowerCoverMarch.exists_assembled_state_with_gauge
    {a vStar L : ℝ} {D : LowerCoverBaseData a vStar L}
    {u : ℕ → ℝ} {B : ℕ → C1Solution.SafeRectangleBox} {n : ℕ}
    (M : LowerCoverMarch D u B n)
    (T₀ : LowerCoverFirstTile D (B 0))
    (hu₀ : u 0 = 0) (hu₁ : u 1 = T₀.height)
    (huLast : u (n + 1) = a)
    (hstep : ∀ i ≤ n, u i < u (i + 1))
    (hmem : ∀ i ≤ n + 1, u i ∈ Icc 0 a)
    (hheight : M.height ≤ T₀.height)
    (hfirstX : (M.tile 0 (Nat.zero_le n)).incoming = T₀.incoming)
    (hfirstY : (M.tile 0 (Nat.zero_le n)).outgoing = T₀.outgoing) :
    ∃ Z : ℝ × ℝ → C1Solution.RectangleState,
      ContDiffOn ℝ 1 Z
        (Goursat.rectangle 0 a vStar (vStar + M.height)) ∧
      (∀ p ∈ Goursat.rectangle 0 a vStar (vStar + M.height),
        C1Solution.IsSafeRectangleState (Z p)) ∧
      (∀ t ∈ Icc 0 a, Z (t, vStar) = D.base t) ∧
      (∀ v ∈ Icc vStar (vStar + M.height),
        (Z (0, v)).1 = (1 / 2, D.alpha₀ v)) ∧
      (∀ v ∈ Icc vStar (vStar + M.height),
        C1Solution.stateRadius (Z (0, v)) = v / 2) ∧
      (∀ i : ℕ, (hi : i ≤ n) → EqOn Z
        (fun p => ((M.tile i hi).incoming p,
          (M.tile i hi).outgoing p))
        (Goursat.rectangle (u i) (u (i + 1)) vStar
          (vStar + M.height))) := by
  obtain ⟨Z, hZ, hmatch, hbase⟩ :=
    M.exists_contDiffOn_rectangle_state_glue_with_terminal_trace
      hstep hmem
  refine ⟨Z, ?_, ?_, ?_, ?_, ?_, hmatch⟩
  · simpa only [hu₀, huLast] using hZ
  · intro p hp
    exact M.state_glue_safe_of_tile_match hstep Z hmatch p
      (by simpa only [hu₀, huLast] using hp)
  · intro t ht
    exact hbase t (by simpa only [hu₀, huLast] using ht)
  · intro v hv
    have hp : (0, v) ∈ Goursat.rectangle (u 0) (u 1)
        vStar (vStar + M.height) := by
      rw [hu₀, hu₁]
      exact Goursat.pair_mem_rectangle
        ⟨le_rfl, T₀.height_pos.le⟩ hv
    have he := hmatch 0 (Nat.zero_le n) hp
    rw [hfirstX, hfirstY] at he
    rw [he]
    exact T₀.initial_incoming_gauge
      ⟨hv.1, by linarith only [hv.2, hheight]⟩
  · intro v hv
    have hp : (0, v) ∈ Goursat.rectangle (u 0) (u 1)
        vStar (vStar + M.height) := by
      rw [hu₀, hu₁]
      exact Goursat.pair_mem_rectangle
        ⟨le_rfl, T₀.height_pos.le⟩ hv
    have he := hmatch 0 (Nat.zero_le n) hp
    rw [hfirstX, hfirstY] at he
    rw [he]
    exact T₀.initial_radius_gauge v
      ⟨hv.1, by linarith only [hv.2, hheight]⟩

end ChristodoulouBV.Uniqueness

end
