module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesClassical
public import ChristodoulouBV.Uniqueness.RouteBLowerTilesClassicalTransfer
import Mathlib.Tactic

/-!
# Classical equations on a finite lower tile march

Each constrained tile has all twelve classical jets. The established finite
full-jet glue transfers them to the assembled strip state.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A safely assembled finite march satisfies the full classical reduced
system on the complete closed strip. -/
theorem LowerCoverMarch.classical_jet_on_glued_strip
    {a vStar L b : ℝ} {D : LowerCoverBaseData a vStar L}
    {u : ℕ → ℝ} {B : ℕ → C1Solution.SafeRectangleBox} {n : ℕ}
    (M : LowerCoverMarch D u B n)
    (hu₀ : u 0 = 0) (huLast : u (n + 1) = a)
    (hstep : ∀ i ≤ n, u i < u (i + 1))
    (hmem : ∀ i ≤ n + 1, u i ∈ Icc 0 a)
    (Z : ℝ × ℝ → C1Solution.RectangleState)
    (hZ : ContDiffOn ℝ 1 Z
      (Goursat.rectangle 0 a vStar (vStar + M.height)))
    (hsafe : ∀ p ∈ Goursat.rectangle 0 a vStar (vStar + M.height),
      C1Solution.IsSafeRectangleState (Z p))
    (hmatch : ∀ i : ℕ, (hi : i ≤ n) → EqOn Z
      (fun p => ((M.tile i hi).incoming p, (M.tile i hi).outgoing p))
      (Goursat.rectangle (u i) (u (i + 1)) vStar
        (vStar + M.height))) :
    RouteBClassicalJetOn b
      (Goursat.rectangle 0 a vStar (vStar + M.height))
      (rectangleStateFields Z) := by
  have hTile : ∀ i : ℕ, (hi : i ≤ n) →
      RouteBClassicalJetOn b
        (Goursat.rectangle (u i) (u (i + 1)) vStar
          (vStar + M.height))
        (rectangleStateFields fun p =>
          ((M.tile i hi).incoming p, (M.tile i hi).outgoing p)) := by
    intro i hi
    exact (M.tile i hi).classical_jet_on (hstep i hi)
      M.height_pos (hmem i (by omega)).1
      (hmem (i + 1) (by omega)).2
  have hZ' : ContDiffOn ℝ 1 Z
      (Goursat.rectangle (u 0) (u (n + 1)) vStar
        (vStar + M.height)) := by
    simpa only [hu₀, huLast] using hZ
  have hsafe' : ∀ p ∈ Goursat.rectangle (u 0) (u (n + 1))
      vStar (vStar + M.height),
      C1Solution.IsSafeRectangleState (Z p) := by
    simpa only [hu₀, huLast] using hsafe
  have h := M.classical_jet_on_assembled_state hstep Z hZ'
    hsafe' hmatch hTile
  simpa only [hu₀, huLast] using h

end ChristodoulouBV.Uniqueness

end
