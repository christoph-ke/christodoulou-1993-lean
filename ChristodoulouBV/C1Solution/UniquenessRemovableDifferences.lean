module

public import ChristodoulouBV.C1Solution.UniquenessVerticalQuotientBox
public import ChristodoulouBV.C1Solution.UniquenessBoxIdentities
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Canonical removable quotient differences

The vertical pair box yields the mass ratio and squared-radius quotient
differences needed by the mixed coefficient ledger.
-/

public section

namespace ChristodoulouBV.C1Solution

/-- The two quotients of the vertical pair box agree with the canonical
mass ratio and squared-radius mass quotient on the closed triangle. -/
theorem canonical_vertical_pair_box_mass_quotients
    {b₁ b₂ T c C Bv : ℝ}
    (hT : 0 < T) (hTwidth : T ≤ 1)
    (hT₁ : T < b₁) (hT₂ : T < b₂)
    (hc : 0 < c) (hC : 0 ≤ C) (hBv : 0 ≤ Bv)
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
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 T) :
    let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
      hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
    (intervalIntegral.cubicLinearQuotient B.first.J B.first.r p =
      canonicalMassRatio b₁ S₁ p ∧
     intervalIntegral.cubicSquaredQuotient B.first.J B.first.r p =
      canonicalMassOverRadiusSq b₁ S₁ p) ∧
    (intervalIntegral.cubicLinearQuotient B.second.J B.second.r p =
      canonicalMassRatio b₂ S₂ p ∧
     intervalIntegral.cubicSquaredQuotient B.second.J B.second.r p =
      canonicalMassOverRadiusSq b₂ S₂ p) := by
  dsimp only
  constructor
  · simpa only [canonicalVerticalPairBox] using
      (canonical_box_mass_quotients hT hT₁ H₁
        (fun q hq => (hweight₁ q hq).1) hp)
  · simpa only [canonicalVerticalPairBox] using
      (canonical_box_mass_quotients hT hT₂ H₂
        (fun q hq => (hweight₂ q hq).1) hp)

/-- The canonical squared-radius mass quotient has the vertical-only
two-solution value bound at each point of a width-one triangle. -/
theorem canonical_mass_over_radius_sq_sub_le_difference
    {b₁ b₂ T c C Bv : ℝ}
    (hT : 0 < T) (hTwidth : T ≤ 1)
    (hT₁ : T < b₁) (hT₂ : T < b₂)
    (hc : 0 < c) (hC : 0 ≤ C) (hBv : 0 ≤ Bv)
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
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 T) :
    let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
      hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
    |canonicalMassOverRadiusSq b₁ S₁ p -
      canonicalMassOverRadiusSq b₂ S₂ p| ≤
        (B.JΔ / c ^ 2 + 2 * B.J₀ / c ^ 3) *
          (p.2 - p.1) * outgoingDifference T hT.le S₁ S₂ p.1 := by
  dsimp only
  let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
    hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
  have hid := canonical_vertical_pair_box_mass_quotients
    hT hTwidth hT₁ hT₂ hc hC hBv H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hp
  have h := B.squaredQuotient_value_sub_bound hc p hp
  dsimp only at hid
  rw [hid.1.2, hid.2.2] at h
  exact h

/-- The vertical pair box also gives the canonical mass-ratio value
difference with its quadratic axis factor. -/
theorem canonical_mass_ratio_sub_le_of_vertical_box
    {b₁ b₂ T c C Bv : ℝ}
    (hT : 0 < T) (hTwidth : T ≤ 1)
    (hT₁ : T < b₁) (hT₂ : T < b₂)
    (hc : 0 < c) (hC : 0 ≤ C) (hBv : 0 ≤ Bv)
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
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 T) :
    let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
      hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
    |canonicalMassRatio b₁ S₁ p - canonicalMassRatio b₂ S₂ p| ≤
      (B.JΔ / c + B.J₀ / c ^ 2) * (p.2 - p.1) ^ 2 *
        outgoingDifference T hT.le S₁ S₂ p.1 := by
  dsimp only
  let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
    hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
  have hid := canonical_vertical_pair_box_mass_quotients
    hT hTwidth hT₁ hT₂ hc hC hBv H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hp
  have h := B.linearQuotient_value_sub_bound hc p hp
  dsimp only at hid
  rw [hid.1.1, hid.2.1] at h
  exact h

/-- The outgoing jet of the canonical mass ratio has the vertical-only
two-solution bound, with no incoming jet difference. -/
theorem canonical_mass_ratio_vertical_jet_sub_le_difference
    {b₁ b₂ T c C Bv : ℝ}
    (hT : 0 < T) (hTwidth : T ≤ 1)
    (hT₁ : T < b₁) (hT₂ : T < b₂)
    (hc : 0 < c) (hC : 0 ≤ C) (hBv : 0 ≤ Bv)
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
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 T) :
    let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
      hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
    |(fderivWithin ℝ (canonicalMassRatio b₁ S₁)
        (closedCoordTriangle 0 T) p) (0, 1) -
      (fderivWithin ℝ (canonicalMassRatio b₂ S₂)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤
        (B.JΔv / c + B.Jv / c ^ 2 +
          B.JΔ * B.Rv / c ^ 2 + B.J₀ * B.RΔv / c ^ 2 +
          2 * B.J₀ * B.Rv / c ^ 3) * (p.2 - p.1) *
          outgoingDifference T hT.le S₁ S₂ p.1 := by
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
  have h := B.linearQuotient_vertical_sub_bound hT hc p hp
  rw [fderivWithin_congr' heq₁ hp,
    fderivWithin_congr' heq₂ hp] at h
  exact h

/-- The outgoing jet of the canonical squared-radius mass quotient has
the vertical-only two-solution bound. -/
theorem canonical_mass_over_radius_sq_vertical_jet_sub_le_difference
    {b₁ b₂ T c C Bv : ℝ}
    (hT : 0 < T) (hTwidth : T ≤ 1)
    (hT₁ : T < b₁) (hT₂ : T < b₂)
    (hc : 0 < c) (hC : 0 ≤ C) (hBv : 0 ≤ Bv)
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
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 T) :
    let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
      hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
    |(fderivWithin ℝ (canonicalMassOverRadiusSq b₁ S₁)
        (closedCoordTriangle 0 T) p) (0, 1) -
      (fderivWithin ℝ (canonicalMassOverRadiusSq b₂ S₂)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤
        (B.JΔv / c ^ 2 + 2 * B.Jv / c ^ 3 +
          2 * B.JΔ * B.Rv / c ^ 3 +
          2 * B.J₀ * B.RΔv / c ^ 3 +
          6 * B.J₀ * B.Rv / c ^ 4) *
          outgoingDifference T hT.le S₁ S₂ p.1 := by
  dsimp only
  let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
    hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
  have hid (q : ℝ × ℝ) (hq : q ∈ closedCoordTriangle 0 T) :=
    canonical_vertical_pair_box_mass_quotients
      hT hTwidth hT₁ hT₂ hc hC hBv H₁ H₂
      hweight₁ hweight₂ hhvertical₁ hhvertical₂ hq
  have heq₁ : Set.EqOn
      (intervalIntegral.cubicSquaredQuotient B.first.J B.first.r)
      (canonicalMassOverRadiusSq b₁ S₁) (closedCoordTriangle 0 T) := by
    intro q hq
    exact (hid q hq).1.2
  have heq₂ : Set.EqOn
      (intervalIntegral.cubicSquaredQuotient B.second.J B.second.r)
      (canonicalMassOverRadiusSq b₂ S₂) (closedCoordTriangle 0 T) := by
    intro q hq
    exact (hid q hq).2.2
  have h := B.squaredQuotient_vertical_sub_bound hT hc p hp
  rw [fderivWithin_congr' heq₁ hp,
    fderivWithin_congr' heq₂ hp] at h
  exact h

/-- Both canonical mass quotients have the common outgoing jet bounds
supplied by the vertical-only box. -/
theorem canonical_mass_quotients_vertical_jet_bounds
    {b₁ b₂ T c C Bv : ℝ}
    (hT : 0 < T) (hTwidth : T ≤ 1)
    (hT₁ : T < b₁) (hT₂ : T < b₂)
    (hc : 0 < c) (hC : 0 ≤ C) (hBv : 0 ≤ Bv)
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
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 T) :
    let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
      hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
    (|(fderivWithin ℝ (canonicalMassRatio b₁ S₁)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤
        (B.Jv / c + B.J₀ * B.Rv / c ^ 2) * (p.2 - p.1) ∧
     |(fderivWithin ℝ (canonicalMassRatio b₂ S₂)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤
        (B.Jv / c + B.J₀ * B.Rv / c ^ 2) * (p.2 - p.1)) ∧
    (|(fderivWithin ℝ (canonicalMassOverRadiusSq b₁ S₁)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤
        B.Jv / c ^ 2 + 2 * B.J₀ * B.Rv / c ^ 3 ∧
     |(fderivWithin ℝ (canonicalMassOverRadiusSq b₂ S₂)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤
        B.Jv / c ^ 2 + 2 * B.J₀ * B.Rv / c ^ 3) := by
  dsimp only
  let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
    hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
  have hid (q : ℝ × ℝ) (hq : q ∈ closedCoordTriangle 0 T) :=
    canonical_vertical_pair_box_mass_quotients
      hT hTwidth hT₁ hT₂ hc hC hBv H₁ H₂
      hweight₁ hweight₂ hhvertical₁ hhvertical₂ hq
  have heqμ₁ : Set.EqOn
      (intervalIntegral.cubicLinearQuotient B.first.J B.first.r)
      (canonicalMassRatio b₁ S₁) (closedCoordTriangle 0 T) := by
    intro q hq
    exact (hid q hq).1.1
  have heqμ₂ : Set.EqOn
      (intervalIntegral.cubicLinearQuotient B.second.J B.second.r)
      (canonicalMassRatio b₂ S₂) (closedCoordTriangle 0 T) := by
    intro q hq
    exact (hid q hq).2.1
  have heqA₁ : Set.EqOn
      (intervalIntegral.cubicSquaredQuotient B.first.J B.first.r)
      (canonicalMassOverRadiusSq b₁ S₁) (closedCoordTriangle 0 T) := by
    intro q hq
    exact (hid q hq).1.2
  have heqA₂ : Set.EqOn
      (intervalIntegral.cubicSquaredQuotient B.second.J B.second.r)
      (canonicalMassOverRadiusSq b₂ S₂) (closedCoordTriangle 0 T) := by
    intro q hq
    exact (hid q hq).2.2
  have h := B.quotient_vertical_bounds hT hc p hp
  rw [fderivWithin_congr' heqμ₁ hp,
    fderivWithin_congr' heqμ₂ hp,
    fderivWithin_congr' heqA₁ hp,
    fderivWithin_congr' heqA₂ hp] at h
  exact h

end ChristodoulouBV.C1Solution

end
