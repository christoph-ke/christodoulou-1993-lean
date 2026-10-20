module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesMesh
import Mathlib.Tactic

/-!
# Safe finite meshes for the lower cover

A uniform bound on the safe-box vector fields turns uniform continuity of
the terminal state into the quantitative width conditions used by the finite
march. The first tile is fixed before this mesh is chosen.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Uniformly bounded safe boxes centered along the canonical base admit a
finite safe mesh starting with the already constructed first tile. -/
theorem LowerCoverBaseData.exists_safe_finite_march_of_uniform_box_bounds
    {a vStar L δ C : ℝ} (D : LowerCoverBaseData a vStar L)
    (hoff : a < vStar)
    (B₀ : C1Solution.SafeRectangleBox)
    (T₀ : LowerCoverFirstTile D B₀)
    (hδ : 0 < δ) (hC : 0 ≤ C)
    (hboxes : ∀ t ∈ Icc 0 a,
      ∃ B : C1Solution.SafeRectangleBox,
        B.center = D.base t ∧ B.radius = δ ∧
        B.valueBound ≤ C ∧ (B.derivBound : ℝ) ≤ C) :
    ∃ (n : ℕ) (u : ℕ → ℝ)
      (B : ℕ → C1Solution.SafeRectangleBox)
      (M : LowerCoverMarch D u B n),
      B 0 = B₀ ∧ u 0 = 0 ∧ u 1 = T₀.height ∧
      u (n + 1) = a ∧
      (∀ i ≤ n, u i < u (i + 1)) ∧
      (∀ i ≤ n + 1, u i ∈ Icc 0 a) ∧
      M.height ≤ T₀.height ∧
      (M.tile 0 (Nat.zero_le n)).incoming = T₀.incoming ∧
      (M.tile 0 (Nat.zero_le n)).outgoing = T₀.outgoing := by
  have huc := (isCompact_Icc : IsCompact (Icc 0 a))
    |>.uniformContinuousOn_of_continuous D.base_cont.continuousOn
  obtain ⟨ρ, hρ, hmod⟩ :=
    (Metric.uniformContinuousOn_iff.mp huc) (δ / 4)
      (by linarith only [hδ])
  let ε := min ρ (min (δ / (8 * (C + 1))) (1 / (2 * (C + 1))))
  have hC1 : 0 < C + 1 := by linarith only [hC]
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hρ (lt_min (div_pos hδ (by positivity))
      (div_pos (by norm_num) (by positivity)))
  obtain ⟨n, u, s, hs, hsε, hu₀, hu₁, huLast, hstep, hmem,
    hwidth⟩ := exists_finite_mesh_after_first
      T₀.height_pos T₀.height_lt_a hε
  have hsρ : s < ρ := hsε.trans_le (min_le_left _ _)
  have hsValue : s < δ / (8 * (C + 1)) :=
    hsε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsDeriv : s < 1 / (2 * (C + 1)) :=
    hsε.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let B : ℕ → C1Solution.SafeRectangleBox := fun i =>
    if hi : i = 0 then B₀
    else if ht : u i ∈ Icc 0 a then (hboxes (u i) ht).choose
    else B₀
  have hB₀ : B 0 = B₀ := by simp [B]
  have hB (i : ℕ) (hi : 0 < i) (himem : u i ∈ Icc 0 a) :
      (B i).center = D.base (u i) ∧ (B i).radius = δ ∧
        (B i).valueBound ≤ C ∧ ((B i).derivBound : ℝ) ≤ C := by
    have hin : i ≠ 0 := Nat.ne_of_gt hi
    simpa only [B, dite_eq_right hin, dite_eq_left himem] using
      (hboxes (u i) himem).choose_spec
  have hcenter : ∀ i < n,
      (B (i + 1)).center = D.base (u (i + 1)) := by
    intro i hi
    exact (hB (i + 1) (by omega) (hmem (i + 1) (by omega))).1
  have hnear : ∀ i < n, ∀ t ∈ Icc (u (i + 1)) (u (i + 2)),
      dist (D.base t) (D.base (u (i + 1))) ≤
        (B (i + 1)).radius / 4 := by
    intro i hi t ht
    have hleft := hmem (i + 1) (by omega)
    have hright := hmem (i + 2) (by omega)
    have htmem : t ∈ Icc 0 a :=
      ⟨hleft.1.trans ht.1, ht.2.trans hright.2⟩
    have hdist : dist t (u (i + 1)) < ρ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
      have hw := hwidth i hi
      linarith only [ht.2, hw, hsρ]
    have h := (hB (i + 1) (by omega) hleft).2.1
    rw [h]
    exact (hmod t htmem (u (i + 1)) hleft hdist).le
  have hwidthSize : ∀ i < n, (B (i + 1)).radius / 2 +
      (B (i + 1)).valueBound * (u (i + 2) - u (i + 1)) <
        (B (i + 1)).radius := by
    intro i hi
    obtain ⟨_, hr, hV, _⟩ := hB (i + 1) (by omega)
      (hmem (i + 1) (by omega))
    rw [hr, hwidth i hi]
    have hVnonneg : 0 ≤ (B (i + 1)).valueBound :=
      le_max_left _ _
    have hprod := mul_le_mul_of_nonneg_right hV hs.le
    have hden : 0 < 8 * (C + 1) := by positivity
    have hsmall : C * s < δ / 8 := by
      have hmul := (lt_div_iff₀ hden).mp hsValue
      nlinarith only [hmul, hC, hs]
    linarith only [hprod, hsmall, hδ]
  have hwidthSmall : ∀ i < n,
      ((B (i + 1)).derivBound : ℝ) *
        (u (i + 2) - u (i + 1)) < 1 := by
    intro i hi
    obtain ⟨_, _, _, hD⟩ := hB (i + 1) (by omega)
      (hmem (i + 1) (by omega))
    rw [hwidth i hi]
    have hprod := mul_le_mul_of_nonneg_right hD hs.le
    have hden : 0 < 2 * (C + 1) := by positivity
    have hsmall : C * s < 1 / 2 := by
      have hmul := (lt_div_iff₀ hden).mp hsDeriv
      nlinarith only [hmul, hC, hs]
    linarith only [hprod, hsmall]
  have hoffMesh : ∀ i ≤ n + 1, u i < vStar := by
    intro i hi
    exact (hmem i hi).2.trans_lt hoff
  obtain ⟨M, hheight, hfirstX, hfirstY⟩ :=
    D.exists_finite_march_with_first_tile u B
      (by simpa only [hB₀] using T₀)
      hu₀ hu₁ n hstep
      (fun i hi => (hmem i hi).1)
      (fun i hi => (hmem i hi).2)
      hoffMesh hcenter hnear hwidthSize hwidthSmall
  exact ⟨n, u, B, M, hB₀, hu₀, hu₁, huLast, hstep,
    hmem, hheight, hfirstX, hfirstY⟩

end ChristodoulouBV.Uniqueness

end
