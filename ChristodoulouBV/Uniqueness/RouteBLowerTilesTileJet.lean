module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesLocalJet
import Mathlib.Tactic

/-!
# Full coordinate jets on a safe lower tile

The characteristic rectangle theorem gives slice derivatives. Relative C¹
on a nondegenerate rectangle identifies them with the full first jet even
at its boundary.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The two semilinear characteristic equations hold as evaluations of the
full relative first jets throughout a lower tile. -/
theorem LowerCoverTile.characteristic_full_jets
    {a vStar L u₀ u₁ H : ℝ} {D : LowerCoverBaseData a vStar L}
    {B : C1Solution.SafeRectangleBox}
    (T : LowerCoverTile D B u₀ u₁ H)
    (hu : u₀ < u₁) (hH : 0 < H) :
    ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc vStar (vStar + H),
      (fderivWithin ℝ T.incoming
        (Goursat.rectangle u₀ u₁ vStar (vStar + H))
        (u, v)) (1, 0) =
          C1Solution.rectangleF (T.incoming (u, v), T.outgoing (u, v)) ∧
      (fderivWithin ℝ T.outgoing
        (Goursat.rectangle u₀ u₁ vStar (vStar + H))
        (u, v)) (0, 1) =
          C1Solution.rectangleG (T.incoming (u, v), T.outgoing (u, v)) := by
  intro u hu' v hv'
  have hcoordX :=
    (C1Solution.coordinate_derivatives_of_contDiffOn_rectangle
      hu (by linarith only [hH]) T.incoming_c1 hu' hv').1
  have hcoordY :=
    (C1Solution.coordinate_derivatives_of_contDiffOn_rectangle
      hu (by linarith only [hH]) T.outgoing_c1 hu' hv').2
  obtain ⟨hcharX, hcharY⟩ := T.characteristic_jets u hu' v hv'
  constructor
  · have hunique := (uniqueDiffOn_Icc hu) u hu'
    exact (hcoordX.derivWithin hunique).symm.trans
      (hcharX.derivWithin hunique)
  · have hunique := (uniqueDiffOn_Icc (by linarith only [hH])) v hv'
    exact (hcoordY.derivWithin hunique).symm.trans
      (hcharY.derivWithin hunique)

end ChristodoulouBV.Uniqueness

end
