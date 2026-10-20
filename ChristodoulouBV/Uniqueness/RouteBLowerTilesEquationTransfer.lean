module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesAssemble
public import ChristodoulouBV.Uniqueness.RouteBGluingClassicalJet
import ChristodoulouBV.Uniqueness.RouteBGluingJetTransfer
import Mathlib.Tactic

/-!
# Classical jet equations across a finite lower-tile cover

The full-jet finite glue has the same scalar-expression derivative as each
tile at every point of that tile, including its closed edges. This reduces
the twelve classical equations of the assembled lower cover to the local
rectangle equations.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Any pointwise classical relative-jet equation on every lower tile passes
to the assembled C¹ state on the entire closed strip. -/
theorem LowerCoverMarch.local_jet_equation_on_assembled_state
    {a vStar L b : ℝ} {D : LowerCoverBaseData a vStar L}
    {u : ℕ → ℝ} {B : ℕ → C1Solution.SafeRectangleBox} {n : ℕ}
    (M : LowerCoverMarch D u B n)
    (hstep : ∀ i ≤ n, u i < u (i + 1))
    (Z : ℝ × ℝ → C1Solution.RectangleState)
    (hmatch : ∀ i : ℕ, (hi : i ≤ n) → EqOn Z
      (fun p => ((M.tile i hi).incoming p, (M.tile i hi).outgoing p))
      (Goursat.rectangle (u i) (u (i + 1)) vStar
        (vStar + M.height)))
    (E rhs : (RouteBField → ℝ) → ℝ) (direction : ℝ × ℝ)
    (hEC1 : ContDiffOn ℝ 1
      (routeBScalarExpression E (rectangleStateFields Z))
      (Goursat.rectangle (u 0) (u (n + 1)) vStar
        (vStar + M.height)))
    (hTile : ∀ i : ℕ, (hi : i ≤ n) →
      RouteBLocalJetEquation b
        (Goursat.rectangle (u i) (u (i + 1)) vStar
          (vStar + M.height))
        (rectangleStateFields fun p =>
          ((M.tile i hi).incoming p, (M.tile i hi).outgoing p))
        E rhs direction) :
    RouteBLocalJetEquation b
      (Goursat.rectangle (u 0) (u (n + 1)) vStar
        (vStar + M.height))
      (rectangleStateFields Z) E rhs direction := by
  let K := Goursat.rectangle (u 0) (u (n + 1)) vStar
    (vStar + M.height)
  let Ki := fun i : ℕ => Goursat.rectangle (u i) (u (i + 1))
    vStar (vStar + M.height)
  have hcover := finite_mesh_rectangles_cover u n vStar M.height hstep
  intro p hp hpDev
  have hpUnion : p ∈ ⋃ i ∈ Finset.range (n + 1), Ki i := by
    rw [hcover]
    exact hp
  simp only [Set.mem_iUnion, Finset.mem_range] at hpUnion
  obtain ⟨i, hii, hpi⟩ := hpUnion
  have hi : i ≤ n := Nat.le_of_lt_succ hii
  let Zi : ℝ × ℝ → C1Solution.RectangleState := fun p =>
    ((M.tile i hi).incoming p, (M.tile i hi).outgoing p)
  have hfields : RouteBFieldsEqOn (rectangleStateFields Z)
      (rectangleStateFields Zi) (Ki i) := by
    intro c q hq
    have hz := hmatch i hi hq
    cases c <;>
      simp [routeBField, rectangleStateFields,
        routeBFieldsOfComponents, Zi, hz]
  have hEq : EqOn
      (routeBScalarExpression E (rectangleStateFields Z))
      (routeBScalarExpression E (rectangleStateFields Zi))
      (Ki i) := by
    intro q hq
    change E (fun c => routeBField (rectangleStateFields Z) c q) =
      E (fun c => routeBField (rectangleStateFields Zi) c q)
    congr 1
    funext c
    exact hfields c hq
  have hSub : Ki i ⊆ K := by
    intro q hq
    change q ∈ Goursat.rectangle (u 0) (u (n + 1))
      vStar (vStar + M.height)
    rw [← hcover]
    simp only [Set.mem_iUnion, Finset.mem_range]
    exact ⟨i, hii, hq⟩
  have hUnique : UniqueDiffOn ℝ (Ki i) :=
    C1Solution.uniqueDiffOn_rectangle (hstep i hi)
      (by linarith only [M.height_pos])
  have hderiv := fderivWithin_eq_of_eqOn_subset hEC1 hSub hUnique
    hEq hpi
  have hlocal := hTile i hi p hpi hpDev
  change (fderivWithin ℝ
    (routeBScalarExpression E (rectangleStateFields Z)) K p)
    direction = rhs (fun c => routeBField (rectangleStateFields Z) c p)
  rw [hderiv, hlocal]
  congr 1
  funext c
  exact (hfields c hpi).symm

end ChristodoulouBV.Uniqueness

end
