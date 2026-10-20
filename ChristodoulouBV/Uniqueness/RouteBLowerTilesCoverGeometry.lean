module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesFiniteMarch
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# Geometry of a finite lower-cover mesh

The closed tile rectangles cover the intended strip exactly. Distinct
nonadjacent mesh intervals have disjoint interiors and no common points.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Closed intervals between consecutive increasing mesh points cover the
whole interval from the first to the last point. -/
theorem finite_mesh_intervals_cover
    (u : ℕ → ℝ) (n : ℕ)
    (hstep : ∀ i ≤ n, u i < u (i + 1)) :
    (⋃ i ∈ Finset.range (n + 1), Icc (u i) (u (i + 1))) =
      Icc (u 0) (u (n + 1)) := by
  induction n with
  | zero =>
      ext x
      simp
  | succ n ih =>
      have hstep' : ∀ i ≤ n, u i < u (i + 1) := by
        intro i hi
        exact hstep i (by omega)
      have hfirst : u 0 ≤ u (n + 1) := by
        have haux : ∀ k ≤ n + 1, u 0 ≤ u k := by
          intro k
          induction k with
          | zero => intro _; exact le_rfl
          | succ k ihk =>
              intro hk
              exact (ihk (by omega)).trans (hstep' k (by omega)).le
        exact haux (n + 1) le_rfl
      have hlast : u (n + 1) ≤ u (n + 2) :=
        (hstep (n + 1) (by omega)).le
      have hsplit :
          (⋃ i ∈ Finset.range (n + 2), Icc (u i) (u (i + 1))) =
            (⋃ i ∈ Finset.range (n + 1), Icc (u i) (u (i + 1))) ∪
              Icc (u (n + 1)) (u (n + 2)) := by
        ext x
        simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_union]
        constructor
        · rintro ⟨i, hi, hx⟩
          by_cases hin : i < n + 1
          · exact Or.inl ⟨i, hin, hx⟩
          · have hieq : i = n + 1 := by omega
            subst i
            exact Or.inr hx
        · rintro (⟨i, hi, hx⟩ | hx)
          · exact ⟨i, by omega, hx⟩
          · exact ⟨n + 1, by omega, hx⟩
      rw [hsplit, ih hstep', Icc_union_Icc_eq_Icc hfirst hlast]

/-- The finite tile rectangles cover precisely one closed strip. -/
theorem finite_mesh_rectangles_cover
    (u : ℕ → ℝ) (n : ℕ) (vStar H : ℝ)
    (hstep : ∀ i ≤ n, u i < u (i + 1)) :
    (⋃ i ∈ Finset.range (n + 1),
      Goursat.rectangle (u i) (u (i + 1)) vStar (vStar + H)) =
        Goursat.rectangle (u 0) (u (n + 1)) vStar (vStar + H) := by
  ext p
  simp only [Set.mem_iUnion, Finset.mem_range, Goursat.rectangle,
    Set.mem_prod, Set.mem_Icc]
  have hcover := finite_mesh_intervals_cover u n hstep
  have hcover' : (∃ i < n + 1, p.1 ∈ Icc (u i) (u (i + 1))) ↔
      p.1 ∈ Icc (u 0) (u (n + 1)) := by
    simpa only [Set.mem_iUnion, Finset.mem_range, exists_prop] using
      (congrArg (fun s : Set ℝ => p.1 ∈ s) hcover).to_iff
  constructor
  · rintro ⟨i, hi, hpi, hpv⟩
    exact ⟨(hcover').mp ⟨i, hi, hpi⟩, hpv⟩
  · rintro ⟨hpi, hpv⟩
    obtain ⟨i, hi, hxi⟩ := (hcover').mpr hpi
    exact ⟨i, hi, hxi, hpv⟩

/-- Strictly ordered mesh indices have strictly ordered coordinates as long
as both indices lie in the finite mesh. -/
theorem finite_mesh_strictMono_on
    (u : ℕ → ℝ) (n : ℕ)
    (hstep : ∀ i ≤ n, u i < u (i + 1))
    {i j : ℕ} (hij : i < j) (hj : j ≤ n + 1) : u i < u j := by
  have haux : ∀ k ≤ n + 1, ∀ i < k, u i < u k := by
    intro k
    induction k with
    | zero =>
        intro _ i hi
        omega
    | succ k ih =>
        intro hk i hi
        by_cases hik : i = k
        · subst i
          exact hstep k (by omega)
        · have hik' : i < k := by omega
          exact (ih (by omega) i hik').trans (hstep k (by omega))
  exact haux j hj i hij

/-- Two nonadjacent tile rectangles cannot intersect. -/
theorem finite_mesh_rectangles_disjoint_of_gap
    (u : ℕ → ℝ) (n : ℕ) (vStar H : ℝ)
    (hstep : ∀ k ≤ n, u k < u (k + 1))
    {i j : ℕ} (_hi : i < n + 1) (hj : j < n + 1)
    (hgap : i + 1 < j) :
    Disjoint
      (Goursat.rectangle (u i) (u (i + 1)) vStar (vStar + H))
      (Goursat.rectangle (u j) (u (j + 1)) vStar (vStar + H)) := by
  apply Set.disjoint_left.mpr
  intro p hp₁ hp₂
  have hpi : p.1 ∈ Icc (u i) (u (i + 1)) := hp₁.1
  have hpj : p.1 ∈ Icc (u j) (u (j + 1)) := hp₂.1
  have hstrict : u (i + 1) < u j :=
    finite_mesh_strictMono_on u n hstep hgap (by omega)
  exact (not_lt_of_ge hpi.2) (hstrict.trans_le hpj.1)

/-- Adjacent agreement on a finite strip implies pairwise agreement on all
rectangle intersections. Nonadjacent rectangles are disjoint. -/
theorem finite_mesh_pairwise_eqOn_of_adjacent
    {F : Type*} (u : ℕ → ℝ) (n : ℕ) (vStar H : ℝ)
    (hstep : ∀ k ≤ n, u k < u (k + 1))
    (f : ℕ → ℝ × ℝ → F)
    (hadj : ∀ i < n,
      EqOn (f i) (f (i + 1))
        (Goursat.rectangle (u i) (u (i + 1)) vStar (vStar + H) ∩
          Goursat.rectangle (u (i + 1)) (u (i + 2)) vStar (vStar + H)))
    {i j : ℕ} (hi : i < n + 1) (hj : j < n + 1) :
    EqOn (f i) (f j)
      (Goursat.rectangle (u i) (u (i + 1)) vStar (vStar + H) ∩
        Goursat.rectangle (u j) (u (j + 1)) vStar (vStar + H)) := by
  by_cases hij : i = j
  · subst j
    intro p hp
    rfl
  by_cases hnext : i + 1 = j
  · subst j
    exact hadj i (by omega)
  by_cases hprev : j + 1 = i
  · subst i
    intro p hp
    exact (hadj j (by omega) ⟨hp.2, hp.1⟩).symm
  have hgap : i + 1 < j ∨ j + 1 < i := by omega
  intro p hp
  rcases hgap with hgap | hgap
  · exact False.elim ((Set.disjoint_left.mp
      (finite_mesh_rectangles_disjoint_of_gap u n vStar H hstep
        hi hj hgap)) hp.1 hp.2)
  · exact False.elim ((Set.disjoint_left.mp
      (finite_mesh_rectangles_disjoint_of_gap u n vStar H hstep
        hj hi hgap)) hp.2 hp.1)

end ChristodoulouBV.Uniqueness

end
