module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesUniformBounds
public import ChristodoulouBV.Uniqueness.RouteBLowerTilesAssemble
public import ChristodoulouBV.Uniqueness.RouteBLowerTilesClassicalGlue
import Mathlib.Tactic

/-!
# A safe lower strip from canonical characteristic data

The first constrained rectangle, compact safe-box bound, finite mesh, march,
and full-jet glue produce one relative C¹ seven-state strip. The terminal
state and the prescribed initial gauge hold on the closed edges.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

private theorem first_tile_at_equal_box
    {a vStar L : ℝ} {D : LowerCoverBaseData a vStar L}
    {B B₀ : C1Solution.SafeRectangleBox}
    (hB : B = B₀) (T₀ : LowerCoverFirstTile D B₀) :
    ∃ T : LowerCoverFirstTile D B,
      T.height = T₀.height ∧ T.incoming = T₀.incoming ∧
        T.outgoing = T₀.outgoing := by
  subst B₀
  exact ⟨T₀, rfl, rfl, rfl⟩

/-- Uniform safe boxes along the compact base suffice to construct a
positive-height C¹ lower strip with the canonical terminal state and the
prescribed initial gauge. -/
theorem LowerCoverBaseData.exists_safe_lower_strip_state
    {a vStar L δ b : ℝ} (D : LowerCoverBaseData a vStar L)
    (ha : 0 < a) (hL : 0 < L) (hoff : a < vStar)
    (hboxes : ∀ t ∈ Icc 0 a,
      ∃ B : C1Solution.SafeRectangleBox,
        B.center = D.base t ∧ B.radius = δ) :
    ∃ η : ℝ, 0 < η ∧ η < L ∧
      ∃ Z : ℝ × ℝ → C1Solution.RectangleState,
        ContDiffOn ℝ 1 Z
          (Goursat.rectangle 0 a vStar (vStar + η)) ∧
        (∀ p ∈ Goursat.rectangle 0 a vStar (vStar + η),
          C1Solution.IsSafeRectangleState (Z p)) ∧
        RouteBClassicalJetOn b
          (Goursat.rectangle 0 a vStar (vStar + η))
          (rectangleStateFields Z) ∧
        (∀ t ∈ Icc 0 a, Z (t, vStar) = D.base t) ∧
        (∀ v ∈ Icc vStar (vStar + η),
          (Z (0, v)).1 = (1 / 2, D.alpha₀ v)) ∧
        (∀ v ∈ Icc vStar (vStar + η),
          C1Solution.stateRadius (Z (0, v)) = v / 2) := by
  have hzero : (0 : ℝ) ∈ Icc 0 a := ⟨le_rfl, ha.le⟩
  obtain ⟨B₀, hB₀, hBδ⟩ := hboxes 0 hzero
  have hδ : 0 < δ := by rw [← hBδ]; exact B₀.radius_pos
  obtain ⟨T₀⟩ := D.exists_first_constrained_tile ha hL hoff B₀ hB₀
  obtain ⟨C, hC, hbound⟩ := D.exists_uniform_safe_box_bounds hboxes
  have hbounded : ∀ t ∈ Icc 0 a,
      ∃ B : C1Solution.SafeRectangleBox,
        B.center = D.base t ∧ B.radius = δ ∧
        B.valueBound ≤ C ∧ (B.derivBound : ℝ) ≤ C := by
    intro t ht
    obtain ⟨B, hc, hr⟩ := hboxes t ht
    exact ⟨B, hc, hr, (hbound t ht B hc hr).1,
      (hbound t ht B hc hr).2⟩
  obtain ⟨n, u, B, M, hB, hu₀, hu₁, huLast, hstep,
    hmem, hheight, hfirstX, hfirstY⟩ :=
    D.exists_safe_finite_march_of_uniform_box_bounds
      hoff B₀ T₀ hδ hC hbounded
  obtain ⟨hT, hTheight, hTX, hTY⟩ := first_tile_at_equal_box hB T₀
  have hheight' : M.height ≤ hT.height := by
    rw [hTheight]
    exact hheight
  have hfirstX' : (M.tile 0 (Nat.zero_le n)).incoming = hT.incoming := by
    exact hfirstX.trans hTX.symm
  have hfirstY' : (M.tile 0 (Nat.zero_le n)).outgoing = hT.outgoing := by
    exact hfirstY.trans hTY.symm
  obtain ⟨Z, hZ, hsafe, hbase, hinit, hradius, hmatch⟩ :=
    M.exists_assembled_state_with_gauge hT hu₀
      (hu₁.trans hTheight.symm) huLast hstep hmem
      hheight' hfirstX' hfirstY'
  refine ⟨M.height, M.height_pos, ?_, Z, hZ, hsafe, ?_, hbase,
    ?_, hradius⟩
  · exact lt_of_le_of_lt hheight T₀.height_lt_L
  · exact M.classical_jet_on_glued_strip hu₀ huLast hstep hmem
      Z hZ hsafe hmatch
  · simpa only [hB] using hinit

end ChristodoulouBV.Uniqueness

end
