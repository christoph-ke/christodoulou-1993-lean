module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesFiniteMarch
import Mathlib.Tactic

/-!
# The initial trace during the finite lower-tile march

The finite march retains the original first tile by restriction. Recording
this equality makes the prescribed gauge available after gluing.
-/

public section

namespace ChristodoulouBV.Uniqueness

private theorem first_tile_at_equal_endpoints
    {a vStar L x₀ x₁ : ℝ} {D : LowerCoverBaseData a vStar L}
    {B : C1Solution.SafeRectangleBox}
    (T₀ : LowerCoverFirstTile D B)
    (hx₀ : x₀ = 0) (hx₁ : x₁ = T₀.height) :
    ∃ T : LowerCoverTile D B x₀ x₁ T₀.height,
      T.incoming = T₀.incoming ∧ T.outgoing = T₀.outgoing := by
  subst x₀
  subst x₁
  refine ⟨{
    incoming := T₀.incoming
    outgoing := T₀.outgoing
    incoming_cont := T₀.incoming_cont
    outgoing_cont := T₀.outgoing_cont
    safe := T₀.safe
    incoming_c1 := T₀.incoming_c1
    outgoing_c1 := T₀.outgoing_c1
    characteristic_jets := T₀.characteristic_jets
    terminal_trace := T₀.terminal_trace
  }, rfl, rfl⟩

/-- A finite march beginning with a specified constrained first tile keeps
both of its state functions on the first tile. -/
theorem LowerCoverBaseData.exists_finite_march_with_first_tile
    {a vStar L : ℝ} (D : LowerCoverBaseData a vStar L)
    (u : ℕ → ℝ) (B : ℕ → C1Solution.SafeRectangleBox)
    (T₀ : LowerCoverFirstTile D (B 0))
    (hu₀ : u 0 = 0) (hu₁ : u 1 = T₀.height)
    (n : ℕ)
    (hPrev : ∀ i ≤ n, u i < u (i + 1))
    (hzero : ∀ i ≤ n + 1, 0 ≤ u i)
    (hbound : ∀ i ≤ n + 1, u i ≤ a)
    (hoff : ∀ i ≤ n + 1, u i < vStar)
    (hcenter : ∀ i < n,
      (B (i + 1)).center = D.base (u (i + 1)))
    (hbaseNear : ∀ i < n, ∀ t ∈ Set.Icc (u (i + 1)) (u (i + 2)),
      dist (D.base t) (D.base (u (i + 1))) ≤
        (B (i + 1)).radius / 4)
    (hwidthSize : ∀ i < n, (B (i + 1)).radius / 2 +
      (B (i + 1)).valueBound * (u (i + 2) - u (i + 1)) <
        (B (i + 1)).radius)
    (hwidthSmall : ∀ i < n, ((B (i + 1)).derivBound : ℝ) *
      (u (i + 2) - u (i + 1)) < 1) :
    ∃ M : LowerCoverMarch D u B n,
      M.height ≤ T₀.height ∧
      (M.tile 0 (Nat.zero_le n)).incoming = T₀.incoming ∧
      (M.tile 0 (Nat.zero_le n)).outgoing = T₀.outgoing := by
  induction n with
  | zero =>
      obtain ⟨hT, hTX, hTY⟩ :=
        first_tile_at_equal_endpoints T₀ hu₀ hu₁
      let M : LowerCoverMarch D u B 0 := {
        height := T₀.height
        height_pos := T₀.height_pos
        tile := by
          intro i hi
          have hi0 : i = 0 := by omega
          subst i
          exact hT
        seam := by
          intro i hi
          omega
      }
      refine ⟨M, le_rfl, ?_, ?_⟩
      · simpa only [M] using hTX
      · simpa only [M] using hTY
  | succ n ih =>
      have hPrev' : ∀ i ≤ n, u i < u (i + 1) :=
        fun i hi => hPrev i (by omega)
      have hzero' : ∀ i ≤ n + 1, 0 ≤ u i :=
        fun i hi => hzero i (by omega)
      have hbound' : ∀ i ≤ n + 1, u i ≤ a :=
        fun i hi => hbound i (by omega)
      have hoff' : ∀ i ≤ n + 1, u i < vStar :=
        fun i hi => hoff i (by omega)
      obtain ⟨M, hMH, hX₀, hY₀⟩ := ih hPrev' hzero' hbound'
        hoff' (fun i hi => hcenter i (by omega))
        (fun i hi => hbaseNear i (by omega))
        (fun i hi => hwidthSize i (by omega))
        (fun i hi => hwidthSmall i (by omega))
      obtain ⟨η, hη, hηH, T₁, hjoin⟩ :=
        D.exists_matched_next_tile (hPrev n (by omega))
          (hzero (n + 1) (by omega))
          (hPrev (n + 1) (by omega))
          (hbound (n + 2) (by omega))
          (hoff (n + 2) (by omega)) M.height_pos
          (B n) (B (n + 1)) (M.tile n le_rfl)
          (hcenter n (by omega)) (hbaseNear n (by omega))
          (hwidthSize n (by omega)) (hwidthSmall n (by omega))
      let Mr := M.restrict hη hηH.le
      let M' : LowerCoverMarch D u B (n + 1) := {
        height := η
        height_pos := hη
        tile := by
          intro i hi
          by_cases hin : i ≤ n
          · exact Mr.tile i hin
          · have hieq : i = n + 1 := by omega
            subst i
            exact T₁
        seam := by
          intro i hi v hv
          by_cases hin : i < n
          · have hOld := Mr.seam i hin v hv
            have hinsucc : i + 1 ≤ n := by omega
            simpa [hin.le, hinsucc] using hOld
          · have hieq : i = n := by omega
            subst i
            have hnot : ¬ n + 1 ≤ n := by omega
            simpa [hnot, Mr, LowerCoverMarch.restrict,
              LowerCoverTile.restrict] using hjoin v hv
      }
      refine ⟨M', hηH.le.trans hMH, ?_, ?_⟩
      · simpa [M', Mr, LowerCoverMarch.restrict,
          LowerCoverTile.restrict] using hX₀
      · simpa [M', Mr, LowerCoverMarch.restrict,
          LowerCoverTile.restrict] using hY₀

end ChristodoulouBV.Uniqueness

end
