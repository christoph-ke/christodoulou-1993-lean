module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointNuJet
public import ChristodoulouBV.C1Solution.AxisPicardBoxNonempty
import Mathlib.Tactic

/-!
# The invariant axis Picard box

At the numerical lifetime, the three relative first jets of the Picard
output satisfy the value, coordinate derivative, trace, axis, and explicit
segment conditions of the complete closed box.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- A Picard output from a boxed input satisfies every physical box
constraint. -/
theorem Box.picardJets_isInBox {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (D : EdgeData a b M g hEdge) (x : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    IsInBox a b M g hEdge (x.picardJets D hab hM hsmall) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p
    have hval := x.picard_value_bounds D hab hM hsmall p.2
    have hfields := x.picardJets_values D hab hM hsmall p
    rw [hfields.1, hfields.2.1, hfields.2.2]
    refine ⟨hval.1, hval.2.1, hval.2.2.1, hval.2.2.2, ?_⟩
    intro i
    exact ⟨x.picardJets_lam_coordinate_bound D hab hM hsmall p i,
      x.picardJets_nu_coordinate_bound D hab hM hsmall p i,
      x.picardJets_h_coordinate_bound D hab hM hsmall p i⟩
  · intro v
    have h := (x.picardJets_values D hab hM hsmall (edgePoint v)).1
    rw [h]
    exact x.1.toTriple.picard_lam_edge a v.1 g hEdge
  · intro v
    have h := (x.picardJets_values D hab hM hsmall (edgePoint v)).2.2
    rw [h]
    exact x.1.toTriple.picard_h_edge a v.1 g hEdge
  · intro u
    have h := x.picardJets_values D hab hM hsmall (diagonalPoint u)
    rw [h.1, h.2.1]
    exact x.1.toTriple.picard_nu_diag a u.1 g hEdge

/-- The output jets also retain the public segment identities. -/
theorem Box.picardJets_isAdmissible {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (D : EdgeData a b M g hEdge) (x : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    IsAdmissible a b M g hEdge (x.picardJets D hab hM hsmall) := by
  refine ⟨x.picardJets_isInBox D hab hM hsmall, ?_, ?_, ?_⟩
  · exact ScalarJet.ofContDiffOn_explicit hab
      (x.1.toTriple.picard a g hEdge).lam
      (x.picard_lam_c1 D hab hM hsmall)
  · exact ScalarJet.ofContDiffOn_explicit hab
      (x.1.toTriple.picard a g hEdge).nu
      (x.picard_nu_c1 D hab hM hsmall)
  · exact ScalarJet.ofContDiffOn_explicit hab
      (x.1.toTriple.picard a g hEdge).h
      (x.picard_h_c1 D hab hM hsmall)

/-- The axis Picard update is a self-map of the complete closed box at the
explicit lifetime. -/
@[expose] noncomputable def Box.picardMap {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    Box a b M g hEdge → Box a b M g hEdge :=
  fun x => ⟨x.picardJets D hab hM hsmall,
    x.picardJets_isAdmissible D hab hM hsmall⟩

/-- The invariant map has the Picard update as its value triple on the
closed triangle. -/
theorem Box.picardMap_values {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (D : EdgeData a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (x : Box a b M g hEdge) (p : closedCoordTriangle a b) :
    ((Box.picardMap D hab hM hsmall x).1.1.1.1 p =
        (x.1.toTriple.picard a g hEdge).lam p.1) ∧
      ((Box.picardMap D hab hM hsmall x).1.2.1.1.1 p =
        (x.1.toTriple.picard a g hEdge).nu p.1) ∧
      ((Box.picardMap D hab hM hsmall x).1.2.2.1.1 p =
        (x.1.toTriple.picard a g hEdge).h p.1) :=
  x.picardJets_values D hab hM hsmall p

end ChristodoulouBV.AxisPicard

end
