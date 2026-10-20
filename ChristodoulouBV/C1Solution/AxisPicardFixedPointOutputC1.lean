module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointHorizontalPrimitive
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.AttenuatedVolterraJet
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Relative first jets of the axis Picard output

All three Picard output fields are continuously differentiable relative to
the closed axis triangle. This gives a total update on the complete triple
jet space before its physical box bounds are verified.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.AxisPicard

/-- The outgoing Picard field is relatively `C¹` on the closed triangle. -/
theorem Box.picard_lam_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (D : EdgeData a b M g hEdge) (x : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    ContDiffOn ℝ 1 (x.1.toTriple.picard a g hEdge).lam
      (closedCoordTriangle a b) := by
  have hedge : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => g p.2)
      (closedCoordTriangle a b) :=
    (D.g_c1.comp contDiff_snd).contDiffOn
  have hint := contDiffOn_horizontal_integral hab
    (x.picard_coefficients_c1 hab hM hsmall).1
  simpa only [Triple.picard, Pi.add_apply] using hedge.add hint

/-- The scalar Picard field is relatively `C¹` on the closed triangle. -/
theorem Box.picard_h_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (D : EdgeData a b M g hEdge) (x : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    ContDiffOn ℝ 1 (x.1.toTriple.picard a g hEdge).h
      (closedCoordTriangle a b) := by
  have hedge : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => hEdge p.2)
      (closedCoordTriangle a b) :=
    (D.h_c1.comp contDiff_snd).contDiffOn
  have hint := contDiffOn_horizontal_integral hab
    (x.picard_coefficients_c1 hab hM hsmall).2
  simpa only [Triple.picard, Pi.add_apply] using hedge.add hint

/-- The incoming Picard field is relatively `C¹` on the closed triangle. -/
theorem Box.picard_nu_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (D : EdgeData a b M g hEdge) (x : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    ContDiffOn ℝ 1 (x.1.toTriple.picard a g hEdge).nu
      (closedCoordTriangle a b) := by
  let K := closedCoordTriangle a b
  let lamNew := (x.1.toTriple.picard a g hEdge).lam
  have hdiagMap : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => (p.1, p.1)) K := by
    fun_prop
  have hdiagMem : MapsTo (fun p : ℝ × ℝ => (p.1, p.1)) K K := by
    intro p hp
    exact ⟨hp.1, le_refl _, hp.2.1.trans hp.2.2⟩
  have hdiag : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => lamNew (p.1, p.1)) K :=
    (x.picard_lam_c1 D hab hM hsmall).comp hdiagMap hdiagMem
  have hkernel := (x.picard_coefficients_c1 hab hM hsmall).1
  have hradius : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => ∫ s in p.1..p.2,
        x.1.toTriple.gravitational (p.1, s)) K := by
    exact intervalIntegral.contDiffOn_attenuatedVolterraPotential hab hkernel
  have hsum := hdiag.neg.add hradius
  simpa only [lamNew, Triple.picard, Pi.add_apply] using hsum

/-- The three Picard output fields have relative continuous first jets. -/
@[expose] noncomputable def Box.picardJets {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    TripleJet a b :=
  (ScalarJet.ofContDiffOn hab (x.1.toTriple.picard a g hEdge).lam
      (x.picard_lam_c1 D hab hM hsmall),
    ScalarJet.ofContDiffOn hab (x.1.toTriple.picard a g hEdge).nu
      (x.picard_nu_c1 D hab hM hsmall),
    ScalarJet.ofContDiffOn hab (x.1.toTriple.picard a g hEdge).h
      (x.picard_h_c1 D hab hM hsmall))

/-- The value of each output jet is the corresponding Picard field. -/
theorem Box.picardJets_values {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (D : EdgeData a b M g hEdge) (x : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (p : closedCoordTriangle a b) :
    (x.picardJets D hab hM hsmall).1.1.1 p =
        (x.1.toTriple.picard a g hEdge).lam p.1 ∧
      (x.picardJets D hab hM hsmall).2.1.1.1 p =
        (x.1.toTriple.picard a g hEdge).nu p.1 ∧
      (x.picardJets D hab hM hsmall).2.2.1.1 p =
        (x.1.toTriple.picard a g hEdge).h p.1 := by
  simp [Box.picardJets]

end ChristodoulouBV.AxisPicard

end
