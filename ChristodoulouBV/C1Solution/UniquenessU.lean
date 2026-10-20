module

public import ChristodoulouBV.C1Solution.UniquenessHorizontalFour
public import ChristodoulouBV.C1Solution.UniquenessIncomingBound
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# The width-one uniqueness inequality

The four canonical source differences are integrated on incoming rays.
The outgoing-ray estimate for the incoming expansion closes the moving
supremum inequality `(U)` with the explicit audited coefficient.
-/

public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.C1Solution

/-- On a width-one compact triangle, the outgoing moving difference obeys
the zero-data Volterra inequality with coefficient `2 exp(Kd) A1`. -/
theorem canonical_outgoing_integral_bound
    {b₁ b₂ T c C Bv V L ε : ℝ}
    (hT : 0 < T) (hTwidth : T ≤ 1)
    (hT₁ : T < b₁) (hT₂ : T < b₂)
    (hc : 0 < c) (hC : 0 ≤ C) (hBv : 0 ≤ Bv)
    (hV : 0 ≤ V) (hL : 0 ≤ L) (hε : 0 < ε)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hweight₁ : ∀ p ∈ closedCoordTriangle 0 T,
      c ≤ S₁.lam p.1 p.2 ∧ S₁.lam p.1 p.2 ≤ C)
    (hweight₂ : ∀ p ∈ closedCoordTriangle 0 T,
      c ≤ S₂.lam p.1 p.2 ∧ S₂.lam p.1 p.2 ≤ C)
    (hhvertical₁ : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (outgoingQuotient S₁)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Bv)
    (hhvertical₂ : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (outgoingQuotient S₂)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Bv)
    (hnu₁ : ∀ p ∈ closedCoordTriangle 0 T,
      |S₁.nu p.1 p.2| ≤ V)
    (hnu₂ : ∀ p ∈ closedCoordTriangle 0 T,
      |S₂.nu p.1 p.2| ≤ V)
    (hlamvertical₁ : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (fun q : ℝ × ℝ => S₁.lam q.1 q.2)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ L)
    (hlamvertical₂ : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ L)
    (hgap₁ : ∀ p ∈ closedCoordTriangle 0 T,
      ε ≤ 1 - canonicalMassRatio b₁ S₁ p)
    (hgap₂ : ∀ p ∈ closedCoordTriangle 0 T,
      ε ≤ 1 - canonicalMassRatio b₂ S₂ p)
    (hr : ∀ v ∈ Ioo 0 T, S₁.r 0 v = S₂.r 0 v)
    (hphi : ∀ v ∈ Ioo 0 T, S₁.phi 0 v = S₂.phi 0 v)
    {u : ℝ} (hu : u ∈ Icc 0 T) :
    let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
      hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
    let ℓ := canonicalVerticalLedger B C Bv V L ε
    outgoingDifference T hT.le S₁ S₂ u ≤
      (2 * Real.exp ℓ.Kd * ℓ.A1) *
        ∫ s in (0 : ℝ)..u, outgoingDifference T hT.le S₁ S₂ s := by
  dsimp only
  let K := closedCoordTriangle 0 T
  let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
    hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
  let ℓ := canonicalVerticalLedger B C Bv V L ε
  let D := outgoingDifference T hT.le S₁ S₂
  let N := incomingDifference T hT.le S₁ S₂
  let A₂ := 2 * Real.exp ℓ.Kd * ℓ.A1
  let G₁ := canonicalMixedCoefficient b₁ S₁
  let G₂ := canonicalMixedCoefficient b₂ S₂
  let Q₁ := canonicalQuotientSource b₁ S₁
  let Q₂ := canonicalQuotientSource b₂ S₂
  let g := horizontalFourSourceSummand T G₁ G₂ Q₁ Q₂
  have hA1 : 0 ≤ ℓ.A1 :=
    (CanonicalVerticalLedger.nonneg B hc hC hBv hV hL hε).2.2.2.2
  have hDc : Continuous D :=
    continuous_movingSliceSupReal hT.le
      (outgoing_difference_summand_continuousOn hT hT₁ hT₂ H₁ H₂)
  have hgc : ContinuousOn g K :=
    horizontalFourSourceSummand_continuousOn hT
      (canonicalMixedCoefficient_contDiffOn hT hT₁ H₁)
      (canonicalMixedCoefficient_contDiffOn hT hT₂ H₂)
      (canonicalQuotientSource_contDiffOn hT hT₁ H₁)
      (canonicalQuotientSource_contDiffOn hT hT₂ H₂)
  have hsource (s v : ℝ) (hs : 0 ≤ s) (hsv : s ≤ v) (hv : v ≤ T) :
      g (s, v) ≤ A₂ * D s := by
    have hp : (s, v) ∈ K := ⟨hs, hsv, hv⟩
    have hfour := canonical_four_coefficient_difference_bound
      hT hTwidth hT₁ hT₂ hc hC hBv hV hL hε H₁ H₂
      hweight₁ hweight₂ hhvertical₁ hhvertical₂ hnu₁ hnu₂
      hlamvertical₁ hlamvertical₂ hgap₁ hgap₂ hp
    have hfour' : g (s, v) ≤ ℓ.A1 * (D s + N s) := by
      convert hfour using 1; rfl
    have hN := canonical_incoming_difference_le_outgoing_difference
      hT hTwidth hT₁ hT₂ hc hC hBv hV hL hε H₁ H₂
      hweight₁ hweight₂ hhvertical₁ hhvertical₂ hnu₁ hnu₂
      hgap₁ hgap₂ ⟨hs, hsv.trans hv⟩
    have hN' : N s ≤ (2 * Real.exp ℓ.Kd - 1) * D s := by
      convert hN using 1
    calc
      g (s, v) ≤ ℓ.A1 * (D s + N s) := hfour'
      _ ≤ ℓ.A1 * ((2 * Real.exp ℓ.Kd) * D s) := by
        apply mul_le_mul_of_nonneg_left _ hA1
        nlinarith only [hN']
      _ = A₂ * D s := by dsimp [A₂]; ring
  have hpoint (v : ℝ) (hv : v ∈ Icc u T) :
      outgoingDifferenceSummand T S₁ S₂ (u, v) ≤
        A₂ * ∫ s in (0 : ℝ)..u, D s := by
    have hinit := initial_lam_outgoingQuotient_jets_eq_of_data
      hT hT₁ hT₂ H₁ H₂ hr hphi
      (show v ∈ Icc 0 T from ⟨hu.1.trans hv.1, hv.2⟩)
    have hlam₁ := (five_fields_contDiffOn hT hT₁ H₁).1
    have hlam₂ := (five_fields_contDiffOn hT hT₂ H₂).1
    have hh₁ := alpha_div_lam_contDiffOn hT hT₁ H₁
    have hh₂ := alpha_div_lam_contDiffOn hT hT₂ H₂
    have hG₁ := canonicalMixedCoefficient_contDiffOn hT hT₁ H₁
    have hG₂ := canonicalMixedCoefficient_contDiffOn hT hT₂ H₂
    have hQ₁ := canonicalQuotientSource_contDiffOn hT hT₁ H₁
    have hQ₂ := canonicalQuotientSource_contDiffOn hT hT₂ H₂
    have hlamu₁ (p : ℝ × ℝ) (hp : p ∈ K) :
        (fderivWithin ℝ (fun q : ℝ × ℝ => S₁.lam q.1 q.2) K p) (1, 0) =
          G₁ p := (four_mixed_coordinate_jets hT hT₁ H₁ hp).1
    have hlamu₂ (p : ℝ × ℝ) (hp : p ∈ K) :
        (fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2) K p) (1, 0) =
          G₂ p := (four_mixed_coordinate_jets hT hT₂ H₂ hp).1
    have hhu₁ (p : ℝ × ℝ) (hp : p ∈ K) :
        (fderivWithin ℝ (outgoingQuotient S₁) K p) (1, 0) = Q₁ p :=
      outgoingQuotient_horizontal_jet hT hT₁ H₁ hp
    have hhu₂ (p : ℝ × ℝ) (hp : p ∈ K) :
        (fderivWithin ℝ (outgoingQuotient S₂) K p) (1, 0) = Q₂ p :=
      outgoingQuotient_horizontal_jet hT hT₂ H₂ hp
    have hfour := horizontal_four_difference_le_integral hT
      hlam₁ hlam₂ hh₁ hh₂ hG₁ hG₂ hQ₁ hQ₂
      hlamu₁ hlamu₂ hhu₁ hhu₂ hu.1 hv.1 hv.2
      hinit.1 hinit.2.1 hinit.2.2.1 hinit.2.2.2
    have hfour' : outgoingDifferenceSummand T S₁ S₂ (u, v) ≤
        ∫ s in (0 : ℝ)..u, g (s, v) := by
      convert hfour using 1; rfl
    have hpath : ContinuousOn (fun s : ℝ => (s, v)) (Icc 0 u) :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hmap : MapsTo (fun s : ℝ => (s, v)) (Icc 0 u) K := by
      intro s hs
      exact ⟨hs.1, hs.2.trans hv.1, hv.2⟩
    have hgInt : IntervalIntegrable (fun s => g (s, v)) volume 0 u :=
      (hgc.comp hpath hmap).intervalIntegrable_of_Icc hu.1
    have hDInt : IntervalIntegrable (fun s => A₂ * D s) volume 0 u :=
      (continuousOn_const.mul hDc.continuousOn).intervalIntegrable_of_Icc hu.1
    have hmono : (∫ s in (0 : ℝ)..u, g (s, v)) ≤
        ∫ s in (0 : ℝ)..u, A₂ * D s := by
      apply intervalIntegral.integral_mono_on hu.1 hgInt hDInt
      intro s hs
      exact hsource s v hs.1 (hs.2.trans hv.1) hv.2
    calc
      _ ≤ ∫ s in (0 : ℝ)..u, g (s, v) := hfour'
      _ ≤ ∫ s in (0 : ℝ)..u, A₂ * D s := hmono
      _ = A₂ * ∫ s in (0 : ℝ)..u, D s := by
        rw [intervalIntegral.integral_const_mul]
  have hsup := movingSliceSup_le_of_slice_bound hT.le hu hpoint
  change movingSliceSupReal T hT.le
    (outgoingDifferenceSummand T S₁ S₂) u ≤
      A₂ * ∫ s in (0 : ℝ)..u, D s
  rw [movingSliceSupReal, Set.projIcc_of_mem hT.le hu]
  exact hsup

end ChristodoulouBV.C1Solution

end
