module

public import ChristodoulouBV.C1Solution.UniquenessU
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Unconditional uniqueness on a width-one triangle

Compactness supplies every bound in the vertical coefficient ledger.
The zero-data moving-slice lemma then forces equality of the outgoing
expansion and quotient on the whole closed triangle.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

/-- Two frozen C¹ solutions with equal initial radius and scalar data have
equal canonical outgoing fields on every compact triangle of width at most
one contained in their common development. -/
theorem canonical_outgoing_eq_on_width_one
    {b₁ b₂ T : ℝ} (hT : 0 < T) (hTwidth : T ≤ 1)
    (hT₁ : T < b₁) (hT₂ : T < b₂)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hr : ∀ v ∈ Ioo 0 T, S₁.r 0 v = S₂.r 0 v)
    (hphi : ∀ v ∈ Ioo 0 T, S₁.phi 0 v = S₂.phi 0 v) :
    EqOn (fun p : ℝ × ℝ => S₁.lam p.1 p.2)
      (fun p => S₂.lam p.1 p.2) (closedCoordTriangle 0 T) ∧
    EqOn (outgoingQuotient S₁) (outgoingQuotient S₂)
      (closedCoordTriangle 0 T) := by
  let K := closedCoordTriangle 0 T
  obtain ⟨M, hM, hbounds⟩ :=
    exists_common_outgoing_bound hT hT₁ hT₂ H₁ H₂
  obtain ⟨c, ε, hc, hε, hlower⟩ :=
    exists_common_regular_lower_bounds hT hT₁ hT₂ H₁ H₂
  have hweight₁ : ∀ p ∈ K,
      c ≤ S₁.lam p.1 p.2 ∧ S₁.lam p.1 p.2 ≤ M := by
    intro p hp
    exact ⟨(hlower p hp).1,
      (le_abs_self _).trans (hbounds p hp).1⟩
  have hweight₂ : ∀ p ∈ K,
      c ≤ S₂.lam p.1 p.2 ∧ S₂.lam p.1 p.2 ≤ M := by
    intro p hp
    exact ⟨(hlower p hp).2.1,
      (le_abs_self _).trans (hbounds p hp).2.1⟩
  have hhvertical₁ : ∀ p ∈ K,
      |(fderivWithin ℝ (outgoingQuotient S₁) K p) (0, 1)| ≤ M := by
    intro p hp
    exact (hbounds p hp).2.2.2.2.2.2.2.2.1
  have hhvertical₂ : ∀ p ∈ K,
      |(fderivWithin ℝ (outgoingQuotient S₂) K p) (0, 1)| ≤ M := by
    intro p hp
    exact (hbounds p hp).2.2.2.2.2.2.2.2.2
  have hnu₁ : ∀ p ∈ K, |S₁.nu p.1 p.2| ≤ M := by
    intro p hp
    exact (hbounds p hp).2.2.1
  have hnu₂ : ∀ p ∈ K, |S₂.nu p.1 p.2| ≤ M := by
    intro p hp
    exact (hbounds p hp).2.2.2.1
  have hlamvertical₁ : ∀ p ∈ K,
      |(fderivWithin ℝ (fun q : ℝ × ℝ => S₁.lam q.1 q.2) K p)
        (0, 1)| ≤ M := by
    intro p hp
    exact (hbounds p hp).2.2.2.2.2.2.1
  have hlamvertical₂ : ∀ p ∈ K,
      |(fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2) K p)
        (0, 1)| ≤ M := by
    intro p hp
    exact (hbounds p hp).2.2.2.2.2.2.2.1
  have hgap₁ : ∀ p ∈ K,
      ε ≤ 1 - canonicalMassRatio b₁ S₁ p := by
    intro p hp
    exact (hlower p hp).2.2.2.2.1
  have hgap₂ : ∀ p ∈ K,
      ε ≤ 1 - canonicalMassRatio b₂ S₂ p := by
    intro p hp
    exact (hlower p hp).2.2.2.2.2
  let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
    hc hM.le hM.le H₁ H₂ hweight₁ hweight₂
    hhvertical₁ hhvertical₂
  let ℓ := canonicalVerticalLedger B M M M M ε
  let A₂ := 2 * Real.exp ℓ.Kd * ℓ.A1
  have hA1 : 0 ≤ ℓ.A1 :=
    (CanonicalVerticalLedger.nonneg B hc hM.le hM.le hM.le hM.le hε).2.2.2.2
  have hA₂ : 0 ≤ A₂ := by
    dsimp [A₂]
    positivity
  have hU : ∀ u ∈ Icc 0 T,
      outgoingDifference T hT.le S₁ S₂ u ≤
        A₂ * ∫ s in (0 : ℝ)..u,
          outgoingDifference T hT.le S₁ S₂ s := by
    intro u hu
    exact canonical_outgoing_integral_bound
      hT hTwidth hT₁ hT₂ hc hM.le hM.le hM.le hM.le hε
      H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
      hnu₁ hnu₂ hlamvertical₁ hlamvertical₂ hgap₁ hgap₂
      hr hphi hu
  have hf0 : ∀ p ∈ K,
      0 ≤ outgoingDifferenceSummand T S₁ S₂ p := by
    intro p hp
    unfold outgoingDifferenceSummand
    positivity
  have hzero := eq_zero_of_movingSliceSup_integral_bound hT.le hA₂
    (outgoing_difference_summand_continuousOn hT hT₁ hT₂ H₁ H₂)
    hf0 hU
  constructor
  · intro p hp
    have hz := hzero hp
    change outgoingDifferenceSummand T S₁ S₂ p = 0 at hz
    unfold outgoingDifferenceSummand at hz
    have hrest : 0 ≤
        |outgoingQuotient S₁ p - outgoingQuotient S₂ p| +
        |(fderivWithin ℝ (fun q : ℝ × ℝ => S₁.lam q.1 q.2) K p) (0, 1) -
          (fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2) K p) (0, 1)| +
        |(fderivWithin ℝ (outgoingQuotient S₁) K p) (0, 1) -
          (fderivWithin ℝ (outgoingQuotient S₂) K p) (0, 1)| := by positivity
    have hEq : |S₁.lam p.1 p.2 - S₂.lam p.1 p.2| = 0 := by
      linarith only [hz, hrest, abs_nonneg (S₁.lam p.1 p.2 - S₂.lam p.1 p.2)]
    exact sub_eq_zero.mp (abs_eq_zero.mp hEq)
  · intro p hp
    have hz := hzero hp
    change outgoingDifferenceSummand T S₁ S₂ p = 0 at hz
    unfold outgoingDifferenceSummand at hz
    have hnonneg : 0 ≤
        |S₁.lam p.1 p.2 - S₂.lam p.1 p.2| +
        |(fderivWithin ℝ (fun q : ℝ × ℝ => S₁.lam q.1 q.2) K p) (0, 1) -
          (fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2) K p) (0, 1)| +
        |(fderivWithin ℝ (outgoingQuotient S₁) K p) (0, 1) -
          (fderivWithin ℝ (outgoingQuotient S₂) K p) (0, 1)| := by positivity
    have hEq : |outgoingQuotient S₁ p - outgoingQuotient S₂ p| = 0 := by
      linarith only [hz, hnonneg,
        abs_nonneg (outgoingQuotient S₁ p - outgoingQuotient S₂ p)]
    exact sub_eq_zero.mp (abs_eq_zero.mp hEq)

end ChristodoulouBV.C1Solution

end
