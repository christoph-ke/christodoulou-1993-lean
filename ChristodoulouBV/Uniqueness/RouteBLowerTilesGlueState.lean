module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesCoverGeometry
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.ClosedConvexJet
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic

/-!
# Gluing a finite march into a C¹ seven-state field

Each tile is a closed convex rectangle. Full first-jet agreement on adjacent
vertical joins gives the pairwise hypotheses of finite closed-convex gluing.
-/

public section

noncomputable section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The seven-state fields of a finite march glue to a relative `C¹` state
on the whole closed strip, agreeing with every tile including its boundary. -/
theorem LowerCoverMarch.exists_contDiffOn_rectangle_state_glue
    {a vStar L : ℝ} {D : LowerCoverBaseData a vStar L}
    {u : ℕ → ℝ} {B : ℕ → C1Solution.SafeRectangleBox} {n : ℕ}
    (M : LowerCoverMarch D u B n)
    (hstep : ∀ i ≤ n, u i < u (i + 1))
    (hmem : ∀ i ≤ n + 1, u i ∈ Icc 0 a) :
    ∃ Z : ℝ × ℝ → C1Solution.RectangleState,
      ContDiffOn ℝ 1 Z
        (Goursat.rectangle (u 0) (u (n + 1)) vStar
          (vStar + M.height)) ∧
      ∀ i : ℕ, (hi : i ≤ n) → EqOn Z
        (fun p => ((M.tile i hi).incoming p,
          (M.tile i hi).outgoing p))
        (Goursat.rectangle (u i) (u (i + 1)) vStar
          (vStar + M.height)) := by
  let K : ℕ → Set (ℝ × ℝ) := fun i =>
    Goursat.rectangle (u i) (u (i + 1)) vStar (vStar + M.height)
  let f : ℕ → ℝ × ℝ → C1Solution.RectangleState := fun i =>
    if hi : i ≤ n then
      fun p => ((M.tile i hi).incoming p, (M.tile i hi).outgoing p)
    else fun _ => 0
  let G : ℕ → ℝ × ℝ → (ℝ × ℝ) →L[ℝ]
      C1Solution.RectangleState := fun i => fderivWithin ℝ (f i) (K i)
  have hC1 : ∀ i ∈ Finset.range (n + 1), ContDiffOn ℝ 1 (f i) (K i) := by
    intro i hi
    have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    simpa only [f, K, dite_eq_left hin] using
      ((M.tile i hin).incoming_c1.prodMk (M.tile i hin).outgoing_c1)
  have hconv : ∀ i ∈ Finset.range (n + 1), Convex ℝ (K i) := by
    intro i hi
    change Convex ℝ (Icc (u i) (u (i + 1)) ×ˢ
      Icc vStar (vStar + M.height))
    exact (convex_Icc _ _).prod (convex_Icc _ _)
  have hclosed : ∀ i ∈ Finset.range (n + 1), IsClosed (K i) := by
    intro i hi
    change IsClosed (Icc (u i) (u (i + 1)) ×ˢ
      Icc vStar (vStar + M.height))
    exact isClosed_Icc.prod isClosed_Icc
  have hinterior : ∀ i ∈ Finset.range (n + 1),
      (interior (K i)).Nonempty := by
    intro i hi
    have hii : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    change (interior (Icc (u i) (u (i + 1)) ×ˢ
      Icc vStar (vStar + M.height))).Nonempty
    rw [interior_prod_eq, interior_Icc, interior_Icc]
    exact (nonempty_Ioo.mpr (hstep i hii)).prod
      (nonempty_Ioo.mpr (by linarith only [M.height_pos]))
  have hf : ∀ i ∈ Finset.range (n + 1), ContinuousOn (f i) (K i) :=
    fun i hi => (hC1 i hi).continuousOn
  have hG : ∀ i ∈ Finset.range (n + 1), ContinuousOn (G i) (K i) := by
    intro i hi
    exact (hC1 i hi).continuousOn_fderivWithin
      (uniqueDiffOn_convex (hconv i hi) (hinterior i hi)) (by norm_num)
  have hdiff : ∀ i ∈ Finset.range (n + 1),
      DifferentiableOn ℝ (f i) (interior (K i)) := by
    intro i hi
    exact ((hC1 i hi).differentiableOn (by norm_num)).mono interior_subset
  have hderiv : ∀ i ∈ Finset.range (n + 1),
      ∀ p ∈ interior (K i), fderiv ℝ (f i) p = G i p := by
    intro i hi p hp
    have hnhds : K i ∈ 𝓝 p :=
      Filter.mem_of_superset (IsOpen.mem_nhds isOpen_interior hp) interior_subset
    exact (fderivWithin_of_mem_nhds (f := f i) (s := K i) hnhds).symm
  have hadjValue : ∀ i < n, EqOn (f i) (f (i + 1))
      (K i ∩ K (i + 1)) := by
    intro i hi p hp
    have hli : i ≤ n := hi.le
    have hri : i + 1 ≤ n := Nat.succ_le_of_lt hi
    have hcoord : p.1 = u (i + 1) :=
      le_antisymm hp.1.1.2 hp.2.1.1
    have hpEq : p = (u (i + 1), p.2) := by
      ext
      · exact hcoord
      · rfl
    have hv : p.2 ∈ Icc vStar (vStar + M.height) := hp.1.2
    have hseam := M.seam i hi p.2 hv
    rw [hpEq]
    simpa only [f, dite_eq_left hli, dite_eq_left hri] using hseam
  have hadjJet : ∀ i < n, EqOn (G i) (G (i + 1))
      (K i ∩ K (i + 1)) := by
    intro i hi p hp
    have hli : i ≤ n := hi.le
    have hri : i + 1 ≤ n := Nat.succ_le_of_lt hi
    have hcoord : p.1 = u (i + 1) :=
      le_antisymm hp.1.1.2 hp.2.1.1
    have hpEq : p = (u (i + 1), p.2) := by
      ext
      · exact hcoord
      · rfl
    have hv : p.2 ∈ Icc vStar (vStar + M.height) := hp.1.2
    have hfirst := M.full_first_jets_eq_on_seam hstep hmem hi p.2 hv
    have hdiffL : DifferentiableWithinAt ℝ (M.tile i hli).incoming (K i) p :=
      ((M.tile i hli).incoming_c1.differentiableOn (by norm_num)) p hp.1
    have hdiffLY : DifferentiableWithinAt ℝ (M.tile i hli).outgoing (K i) p :=
      ((M.tile i hli).outgoing_c1.differentiableOn (by norm_num)) p hp.1
    have hdiffR : DifferentiableWithinAt ℝ (M.tile (i + 1) hri).incoming
        (K (i + 1)) p :=
      ((M.tile (i + 1) hri).incoming_c1.differentiableOn
        (by norm_num)) p hp.2
    have hdiffRY : DifferentiableWithinAt ℝ (M.tile (i + 1) hri).outgoing
        (K (i + 1)) p :=
      ((M.tile (i + 1) hri).outgoing_c1.differentiableOn
        (by norm_num)) p hp.2
    have hprodL := hdiffL.fderivWithin_prodMk hdiffLY
      ((C1Solution.uniqueDiffOn_rectangle (hstep i hli)
        (by linarith only [M.height_pos])) p hp.1)
    have hprodR := hdiffR.fderivWithin_prodMk hdiffRY
      ((C1Solution.uniqueDiffOn_rectangle (hstep (i + 1) hri)
        (by linarith only [M.height_pos])) p hp.2)
    change fderivWithin ℝ (f i) (K i) p =
      fderivWithin ℝ (f (i + 1)) (K (i + 1)) p
    simp only [f, dite_eq_left hli, dite_eq_left hri]
    rw [hprodL, hprodR]
    rw [hpEq]
    exact congrArg₂ ContinuousLinearMap.prod hfirst.1 hfirst.2
  have hvalue : ∀ i ∈ Finset.range (n + 1),
      ∀ j ∈ Finset.range (n + 1), EqOn (f i) (f j) (K i ∩ K j) := by
    intro i hi j hj
    exact finite_mesh_pairwise_eqOn_of_adjacent u n vStar M.height
      hstep f hadjValue (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
  have hjet : ∀ i ∈ Finset.range (n + 1),
      ∀ j ∈ Finset.range (n + 1), EqOn (G i) (G j) (K i ∩ K j) := by
    intro i hi j hj
    exact finite_mesh_pairwise_eqOn_of_adjacent u n vStar M.height
      hstep G hadjJet (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
  obtain ⟨Z, _, hZ, hmatch, _⟩ :=
    Convex.exists_contDiffOn_one_finset_glue
      (Finset.range (n + 1)) K hconv hclosed hinterior
      f G hf hG hdiff hderiv hvalue hjet
  refine ⟨Z, ?_, ?_⟩
  · rw [← finite_mesh_rectangles_cover u n vStar M.height hstep]
    exact hZ
  · intro i hi
    have hin : i ∈ Finset.range (n + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
    simpa only [f, K, dite_eq_left hi] using hmatch i hin

/-- The glued state takes the canonical base value at every point of the
closed terminal edge. -/
theorem LowerCoverMarch.exists_contDiffOn_rectangle_state_glue_with_terminal_trace
    {a vStar L : ℝ} {D : LowerCoverBaseData a vStar L}
    {u : ℕ → ℝ} {B : ℕ → C1Solution.SafeRectangleBox} {n : ℕ}
    (M : LowerCoverMarch D u B n)
    (hstep : ∀ i ≤ n, u i < u (i + 1))
    (hmem : ∀ i ≤ n + 1, u i ∈ Icc 0 a) :
    ∃ Z : ℝ × ℝ → C1Solution.RectangleState,
      ContDiffOn ℝ 1 Z
        (Goursat.rectangle (u 0) (u (n + 1)) vStar
          (vStar + M.height)) ∧
      (∀ i : ℕ, (hi : i ≤ n) → EqOn Z
        (fun p => ((M.tile i hi).incoming p,
          (M.tile i hi).outgoing p))
        (Goursat.rectangle (u i) (u (i + 1)) vStar
          (vStar + M.height))) ∧
      ∀ t ∈ Icc (u 0) (u (n + 1)), Z (t, vStar) = D.base t := by
  obtain ⟨Z, hZ, hmatch⟩ :=
    M.exists_contDiffOn_rectangle_state_glue hstep hmem
  refine ⟨Z, hZ, hmatch, ?_⟩
  intro t ht
  have hpUnion : (t, vStar) ∈
      (⋃ i ∈ Finset.range (n + 1),
        Goursat.rectangle (u i) (u (i + 1)) vStar
          (vStar + M.height)) := by
    rw [finite_mesh_rectangles_cover u n vStar M.height hstep]
    exact Goursat.pair_mem_rectangle ht
      ⟨le_rfl, by linarith only [M.height_pos]⟩
  simp only [Set.mem_iUnion, Finset.mem_range] at hpUnion
  obtain ⟨i, hi, hp⟩ := hpUnion
  have hin : i ≤ n := Nat.le_of_lt_succ hi
  exact (hmatch i hin hp).trans
    ((M.tile i hin).terminal_trace t hp.1)

/-- A state matching every safe tile is safe on the complete finite strip. -/
theorem LowerCoverMarch.state_glue_safe_of_tile_match
    {a vStar L : ℝ} {D : LowerCoverBaseData a vStar L}
    {u : ℕ → ℝ} {B : ℕ → C1Solution.SafeRectangleBox} {n : ℕ}
    (M : LowerCoverMarch D u B n)
    (hstep : ∀ i ≤ n, u i < u (i + 1))
    (Z : ℝ × ℝ → C1Solution.RectangleState)
    (hmatch : ∀ i : ℕ, (hi : i ≤ n) → EqOn Z
      (fun p => ((M.tile i hi).incoming p,
        (M.tile i hi).outgoing p))
      (Goursat.rectangle (u i) (u (i + 1)) vStar
        (vStar + M.height))) :
    ∀ p ∈ Goursat.rectangle (u 0) (u (n + 1)) vStar
      (vStar + M.height), C1Solution.IsSafeRectangleState (Z p) := by
  intro p hp
  have hpUnion : p ∈
      (⋃ i ∈ Finset.range (n + 1),
        Goursat.rectangle (u i) (u (i + 1)) vStar
          (vStar + M.height)) := by
    rw [finite_mesh_rectangles_cover u n vStar M.height hstep]
    exact hp
  simp only [Set.mem_iUnion, Finset.mem_range] at hpUnion
  obtain ⟨i, hi, hpi⟩ := hpUnion
  have hin : i ≤ n := Nat.le_of_lt_succ hi
  rw [hmatch i hin hpi]
  exact (B i).safe ((M.tile i hin).safe p hpi)

end ChristodoulouBV.Uniqueness

end
