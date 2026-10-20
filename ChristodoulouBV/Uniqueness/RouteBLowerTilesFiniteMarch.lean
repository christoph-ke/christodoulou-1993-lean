module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesSuccessor
import ChristodoulouBV.C1Solution.RectangleJetSeams
import Mathlib.Tactic

/-!
# Finite successor march for the Route B lower cover

A prescribed finite mesh is marched from left to right. Earlier rectangles are
restricted whenever a new successor requires a shorter height. Thus every
finite chain has one common positive height, with full state agreement on its
vertical joins.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A chain of the first `n + 1` closed rectangles at a common height. -/
structure LowerCoverMarch {a vStar L : ℝ} (D : LowerCoverBaseData a vStar L)
    (u : ℕ → ℝ) (B : ℕ → C1Solution.SafeRectangleBox)
    (n : ℕ) where
  height : ℝ
  height_pos : 0 < height
  tile : ∀ i : ℕ, i ≤ n →
    LowerCoverTile D (B i) (u i) (u (i + 1)) height
  seam : ∀ i : ℕ, (hi : i < n) →
    ∀ v ∈ Icc vStar (vStar + height),
      ((tile i hi.le).incoming (u (i + 1), v),
        (tile i hi.le).outgoing (u (i + 1), v)) =
      ((tile (i + 1) (Nat.succ_le_of_lt hi)).incoming (u (i + 1), v),
        (tile (i + 1) (Nat.succ_le_of_lt hi)).outgoing (u (i + 1), v))

/-- The first tile is a one-tile march. -/
def LowerCoverMarch.singleton
    {a vStar L H : ℝ} {D : LowerCoverBaseData a vStar L}
    {u : ℕ → ℝ} {B : ℕ → C1Solution.SafeRectangleBox}
    (hH : 0 < H)
    (T : LowerCoverTile D (B 0) (u 0) (u 1) H) :
    LowerCoverMarch D u B 0 where
  height := H
  height_pos := hH
  tile := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa using T
  seam := by
    intro i hi
    omega

/-- Restrict every rectangle in a finite march to the same smaller height. -/
@[expose] def LowerCoverMarch.restrict
    {a vStar L η : ℝ} {D : LowerCoverBaseData a vStar L}
    {u : ℕ → ℝ} {B : ℕ → C1Solution.SafeRectangleBox} {n : ℕ}
    (M : LowerCoverMarch D u B n) (hη : 0 < η)
    (hηM : η ≤ M.height) : LowerCoverMarch D u B n where
  height := η
  height_pos := hη
  tile := fun i hi => (M.tile i hi).restrict hηM
  seam := by
    intro i hi v hv
    simpa only [LowerCoverTile.restrict] using
      M.seam i hi v ⟨hv.1, by linarith only [hv.2, hηM]⟩

/-- Extend a finite march by one matched successor. Only the positive common
height changes; every earlier tile is retained by restriction. -/
theorem LowerCoverBaseData.exists_march_succ
    {a vStar L : ℝ} (D : LowerCoverBaseData a vStar L)
    {u : ℕ → ℝ} {B : ℕ → C1Solution.SafeRectangleBox} {n : ℕ}
    (M : LowerCoverMarch D u B n)
    (hPrev : u n < u (n + 1))
    (hu₀ : 0 ≤ u (n + 1))
    (hu : u (n + 1) < u (n + 2))
    (hu₁a : u (n + 2) ≤ a)
    (hoff : u (n + 2) < vStar)
    (hcenter : (B (n + 1)).center = D.base (u (n + 1)))
    (hbaseNear : ∀ t ∈ Icc (u (n + 1)) (u (n + 2)),
      dist (D.base t) (D.base (u (n + 1))) ≤ (B (n + 1)).radius / 4)
    (hwidthSize : (B (n + 1)).radius / 2 +
      (B (n + 1)).valueBound * (u (n + 2) - u (n + 1)) <
        (B (n + 1)).radius)
    (hwidthSmall : ((B (n + 1)).derivBound : ℝ) *
      (u (n + 2) - u (n + 1)) < 1) :
    ∃ M' : LowerCoverMarch D u B (n + 1), M'.height < M.height := by
  obtain ⟨η, hη, hηH, T₂, hjoin⟩ :=
    D.exists_matched_next_tile hPrev hu₀ hu hu₁a hoff M.height_pos
      (B n) (B (n + 1)) (M.tile n le_rfl) hcenter hbaseNear
      hwidthSize hwidthSmall
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
        exact T₂
    seam := by
      intro i hi v hv
      by_cases hin : i < n
      · have hOld := Mr.seam i hin v hv
        have hinsucc : i + 1 ≤ n := by omega
        simpa [hin.le, hinsucc] using hOld
      · have hieq : i = n := by omega
        subst i
        have hnot : ¬ n + 1 ≤ n := by omega
        simpa [hnot,
          Mr, LowerCoverMarch.restrict, LowerCoverTile.restrict] using
          hjoin v hv
  }
  exact ⟨M', hηH⟩

/-- Any prescribed finite safe mesh can be marched from a first tile. The
mesh hypotheses concern only the canonical base and its safe boxes; no
later tile or seam is assumed. -/
theorem LowerCoverBaseData.exists_finite_march
    {a vStar L H : ℝ} (D : LowerCoverBaseData a vStar L)
    (u : ℕ → ℝ) (B : ℕ → C1Solution.SafeRectangleBox)
    (hH : 0 < H)
    (T₀ : LowerCoverTile D (B 0) (u 0) (u 1) H)
    (n : ℕ)
    (hPrev : ∀ i ≤ n, u i < u (i + 1))
    (hu₀ : ∀ i ≤ n + 1, 0 ≤ u i)
    (hu₁a : ∀ i ≤ n + 1, u i ≤ a)
    (hoff : ∀ i ≤ n + 1, u i < vStar)
    (hcenter : ∀ i < n,
      (B (i + 1)).center = D.base (u (i + 1)))
    (hbaseNear : ∀ i < n, ∀ t ∈ Icc (u (i + 1)) (u (i + 2)),
      dist (D.base t) (D.base (u (i + 1))) ≤
        (B (i + 1)).radius / 4)
    (hwidthSize : ∀ i < n, (B (i + 1)).radius / 2 +
      (B (i + 1)).valueBound * (u (i + 2) - u (i + 1)) <
        (B (i + 1)).radius)
    (hwidthSmall : ∀ i < n, ((B (i + 1)).derivBound : ℝ) *
      (u (i + 2) - u (i + 1)) < 1) :
    Nonempty (LowerCoverMarch D u B n) := by
  induction n with
  | zero => exact ⟨LowerCoverMarch.singleton hH T₀⟩
  | succ n ih =>
      have hPrev' : ∀ i ≤ n, u i < u (i + 1) := by
        intro i hi
        exact hPrev i (by omega)
      have hu₀' : ∀ i ≤ n + 1, 0 ≤ u i := by
        intro i hi
        exact hu₀ i (by omega)
      have hu₁a' : ∀ i ≤ n + 1, u i ≤ a := by
        intro i hi
        exact hu₁a i (by omega)
      have hoff' : ∀ i ≤ n + 1, u i < vStar := by
        intro i hi
        exact hoff i (by omega)
      have hcenter' : ∀ i < n,
          (B (i + 1)).center = D.base (u (i + 1)) := by
        intro i hi
        exact hcenter i (by omega)
      have hbaseNear' : ∀ i < n,
          ∀ t ∈ Icc (u (i + 1)) (u (i + 2)),
            dist (D.base t) (D.base (u (i + 1))) ≤
              (B (i + 1)).radius / 4 := by
        intro i hi
        exact hbaseNear i (by omega)
      have hwidthSize' : ∀ i < n, (B (i + 1)).radius / 2 +
          (B (i + 1)).valueBound * (u (i + 2) - u (i + 1)) <
            (B (i + 1)).radius := by
        intro i hi
        exact hwidthSize i (by omega)
      have hwidthSmall' : ∀ i < n, ((B (i + 1)).derivBound : ℝ) *
          (u (i + 2) - u (i + 1)) < 1 := by
        intro i hi
        exact hwidthSmall i (by omega)
      obtain ⟨M⟩ := ih hPrev' hu₀' hu₁a' hoff' hcenter'
        hbaseNear' hwidthSize' hwidthSmall'
      obtain ⟨M', _⟩ := D.exists_march_succ M (hPrev n (by omega))
        (hu₀ (n + 1) (by omega)) (hPrev (n + 1) (by omega))
        (hu₁a (n + 2) (by omega))
        (hoff (n + 2) (by omega)) (hcenter n (by omega))
        (hbaseNear n (by omega))
        (hwidthSize n (by omega)) (hwidthSmall n (by omega))
      exact ⟨M'⟩

/-- The complete relative first jets match at every vertical join of a
finite march. The corner transverse derivative is the same canonical
lower-edge derivative on both adjacent rectangles. -/
theorem LowerCoverMarch.full_first_jets_eq_on_seam
    {a vStar L : ℝ} {D : LowerCoverBaseData a vStar L}
    {u : ℕ → ℝ} {B : ℕ → C1Solution.SafeRectangleBox} {n : ℕ}
    (M : LowerCoverMarch D u B n)
    (hstep : ∀ i ≤ n, u i < u (i + 1))
    (hmem : ∀ i ≤ n + 1, u i ∈ Icc 0 a)
    {i : ℕ} (hi : i < n) :
    ∀ v ∈ Icc vStar (vStar + M.height),
      fderivWithin ℝ (M.tile i hi.le).incoming
        (Goursat.rectangle (u i) (u (i + 1)) vStar
          (vStar + M.height)) (u (i + 1), v) =
        fderivWithin ℝ (M.tile (i + 1) (Nat.succ_le_of_lt hi)).incoming
          (Goursat.rectangle (u (i + 1)) (u (i + 2)) vStar
            (vStar + M.height)) (u (i + 1), v) ∧
      fderivWithin ℝ (M.tile i hi.le).outgoing
        (Goursat.rectangle (u i) (u (i + 1)) vStar
          (vStar + M.height)) (u (i + 1), v) =
        fderivWithin ℝ (M.tile (i + 1) (Nat.succ_le_of_lt hi)).outgoing
          (Goursat.rectangle (u (i + 1)) (u (i + 2)) vStar
            (vStar + M.height)) (u (i + 1), v) := by
  let T₁ := M.tile i hi.le
  let T₂ := M.tile (i + 1) (Nat.succ_le_of_lt hi)
  have hleft : u i < u (i + 1) := hstep i hi.le
  have hright : u (i + 1) < u (i + 2) :=
    hstep (i + 1) (Nat.succ_le_of_lt hi)
  have hmid : u (i + 1) ∈ Icc 0 a :=
    hmem (i + 1) (by omega)
  have hbaseDeriv := D.baseOutgoing_deriv (u (i + 1)) hmid
  have hderiv₁ : HasDerivWithinAt
      (fun s => (D.base s).2) (D.baseOutgoingPrime (u (i + 1)))
      (Icc (u i) (u (i + 1))) (u (i + 1)) :=
    hbaseDeriv.mono (by
      intro s hs
      exact ⟨(hmem i (by omega)).1.trans hs.1,
        hs.2.trans hmid.2⟩)
  have hderiv₂ : HasDerivWithinAt
      (fun s => (D.base s).2) (D.baseOutgoingPrime (u (i + 1)))
      (Icc (u (i + 1)) (u (i + 2))) (u (i + 1)) :=
    hbaseDeriv.mono (by
      intro s hs
      exact ⟨hmid.1.trans hs.1,
        hs.2.trans (hmem (i + 2) (by omega)).2⟩)
  have hcorner₁ : HasDerivWithinAt
      (fun s => T₁.outgoing (s, vStar))
      (D.baseOutgoingPrime (u (i + 1)))
      (Icc (u i) (u (i + 1))) (u (i + 1)) := by
    apply hderiv₁.congr
    · intro s hs
      exact congrArg Prod.snd (T₁.terminal_trace s hs)
    · exact congrArg Prod.snd
        (T₁.terminal_trace (u (i + 1)) ⟨hleft.le, le_rfl⟩)
  have hcorner₂ : HasDerivWithinAt
      (fun s => T₂.outgoing (s, vStar))
      (D.baseOutgoingPrime (u (i + 1)))
      (Icc (u (i + 1)) (u (i + 2))) (u (i + 1)) := by
    apply hderiv₂.congr
    · intro s hs
      exact congrArg Prod.snd (T₂.terminal_trace s hs)
    · exact congrArg Prod.snd
        (T₂.terminal_trace (u (i + 1)) ⟨le_rfl, hright.le⟩)
  exact C1Solution.full_first_jets_eq_on_vertical_seam_of_corner_data
    hleft hright (by linarith only [M.height_pos]) (B i) (B (i + 1))
    T₁.incoming T₁.outgoing T₂.incoming T₂.outgoing
    T₁.incoming_c1 T₁.outgoing_c1 T₂.incoming_c1 T₂.outgoing_c1
    T₁.safe T₂.safe T₁.characteristic_jets T₂.characteristic_jets
    (M.seam i hi) (D.baseOutgoingPrime (u (i + 1)))
    hcorner₁ hcorner₂

end ChristodoulouBV.Uniqueness

end
