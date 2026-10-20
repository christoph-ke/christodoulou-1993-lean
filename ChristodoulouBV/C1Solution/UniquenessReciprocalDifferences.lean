module

public import ChristodoulouBV.C1Solution.UniquenessRemovableDifferences
public import ChristodoulouBV.C1Solution.UniquenessVerticalReciprocal
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Canonical reciprocal mass-gap bounds

The fixed-ray mass-ratio estimates supply the reciprocal factor used by the
mixed coefficient.
-/

public section

namespace ChristodoulouBV.C1Solution

/-- The reciprocal of the canonical mass gap and its outgoing jet
expression satisfy all six vertical-only value and difference estimates. -/
theorem canonical_inverse_mass_gap_vertical_bounds
    {b₁ b₂ T c C Bv ε : ℝ}
    (hT : 0 < T) (hTwidth : T ≤ 1)
    (hT₁ : T < b₁) (hT₂ : T < b₂)
    (hc : 0 < c) (hC : 0 ≤ C) (hBv : 0 ≤ Bv) (hε : 0 < ε)
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
    (hgap₁ : ∀ p ∈ closedCoordTriangle 0 T,
      ε ≤ 1 - canonicalMassRatio b₁ S₁ p)
    (hgap₂ : ∀ p ∈ closedCoordTriangle 0 T,
      ε ≤ 1 - canonicalMassRatio b₂ S₂ p)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 T) :
    let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
      hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
    let μ₁ := canonicalMassRatio b₁ S₁
    let μ₂ := canonicalMassRatio b₂ S₂
    let μv₁ := (fderivWithin ℝ μ₁ (closedCoordTriangle 0 T) p) (0, 1)
    let μv₂ := (fderivWithin ℝ μ₂ (closedCoordTriangle 0 T) p) (0, 1)
    let Mv := B.Jv / c + B.J₀ * B.Rv / c ^ 2
    let Md := B.JΔ / c + B.J₀ / c ^ 2
    let Mdv := B.JΔv / c + B.Jv / c ^ 2 +
      B.JΔ * B.Rv / c ^ 2 + B.J₀ * B.RΔv / c ^ 2 +
      2 * B.J₀ * B.Rv / c ^ 3
    |(1 - μ₁ p)⁻¹| ≤ ε⁻¹ ∧
    |(1 - μ₂ p)⁻¹| ≤ ε⁻¹ ∧
    |μv₁ / (1 - μ₁ p) ^ 2| ≤ (Mv / ε ^ 2) * (p.2 - p.1) ∧
    |μv₂ / (1 - μ₂ p) ^ 2| ≤ (Mv / ε ^ 2) * (p.2 - p.1) ∧
    |(1 - μ₁ p)⁻¹ - (1 - μ₂ p)⁻¹| ≤
      (Md / ε ^ 2) * (p.2 - p.1) ^ 2 *
        outgoingDifference T hT.le S₁ S₂ p.1 ∧
    |μv₁ / (1 - μ₁ p) ^ 2 - μv₂ / (1 - μ₂ p) ^ 2| ≤
      (Mdv / ε ^ 2 + 2 * Mv * Md / ε ^ 3) *
        (p.2 - p.1) * outgoingDifference T hT.le S₁ S₂ p.1 := by
  dsimp only
  let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
    hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
  have hid (q : ℝ × ℝ) (hq : q ∈ closedCoordTriangle 0 T) :=
    canonical_vertical_pair_box_mass_quotients
      hT hTwidth hT₁ hT₂ hc hC hBv H₁ H₂
      hweight₁ hweight₂ hhvertical₁ hhvertical₂ hq
  have heq₁ : Set.EqOn
      (intervalIntegral.cubicLinearQuotient B.first.J B.first.r)
      (canonicalMassRatio b₁ S₁) (closedCoordTriangle 0 T) := by
    intro q hq
    exact (hid q hq).1.1
  have heq₂ : Set.EqOn
      (intervalIntegral.cubicLinearQuotient B.second.J B.second.r)
      (canonicalMassRatio b₂ S₂) (closedCoordTriangle 0 T) := by
    intro q hq
    exact (hid q hq).2.1
  have hgapbox₁ : ∀ q ∈ closedCoordTriangle 0 T,
      ε ≤ 1 - intervalIntegral.cubicLinearQuotient B.first.J B.first.r q := by
    intro q hq
    rw [(hid q hq).1.1]
    exact hgap₁ q hq
  have hgapbox₂ : ∀ q ∈ closedCoordTriangle 0 T,
      ε ≤ 1 - intervalIntegral.cubicLinearQuotient B.second.J B.second.r q := by
    intro q hq
    rw [(hid q hq).2.1]
    exact hgap₂ q hq
  have h := B.inverse_complement_vertical_bounds hT
    (by simpa only [sub_zero] using hTwidth) hc hε
    hgapbox₁ hgapbox₂ p hp
  dsimp only at h
  rw [(hid p hp).1.1, (hid p hp).2.1,
    fderivWithin_congr' heq₁ hp,
    fderivWithin_congr' heq₂ hp] at h
  exact h

end ChristodoulouBV.C1Solution

end
