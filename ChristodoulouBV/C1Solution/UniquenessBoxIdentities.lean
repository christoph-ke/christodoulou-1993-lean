module

public import ChristodoulouBV.C1Solution.UniquenessBoxMass
public import ChristodoulouBV.C1Solution.UniquenessFinal
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsProducts
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Identifying canonical and box coefficients

The rational coefficients of the single-input cubic box agree with the
canonical mixed coefficient and quotient source of the frozen solution on
each smaller closed triangle.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

/-- The box's cubic-over-linear and cubic-over-square quotients equal the
canonical mass ratio and normalized mass coefficient. -/
theorem canonical_box_mass_quotients {b B c : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hcl : ∀ p ∈ closedCoordTriangle 0 B, c ≤ S.lam p.1 p.2)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    let box := canonicalCubicRationalTriangleBox hB hBb H hcl
    intervalIntegral.cubicLinearQuotient box.J box.r p =
      canonicalMassRatio b S p ∧
    intervalIntegral.cubicSquaredQuotient box.J box.r p =
      canonicalMassOverRadiusSq b S p := by
  dsimp only
  rcases p with ⟨u, v⟩
  by_cases huv : u < v
  · constructor
    · simp only [canonicalCubicRationalTriangleBox,
        intervalIntegral.cubicLinearQuotient, huv, ↓reduceIte,
        canonicalMassNumerator, canonicalMassRatio]
    · simp only [canonicalCubicRationalTriangleBox,
        intervalIntegral.cubicSquaredQuotient, huv, ↓reduceIte,
        canonicalMassNumerator, canonicalMassOverRadiusSq]
  · have heq : u = v := le_antisymm hp.2.1 (le_of_not_gt huv)
    subst v
    constructor
    · simp [intervalIntegral.cubicLinearQuotient,
        canonicalMassRatio_axis]
    · simp [intervalIntegral.cubicSquaredQuotient,
        canonicalMassOverRadiusSq_axis]

/-- The box coefficient is the canonical mixed coefficient on the closed
triangle, including the removable axis. -/
theorem canonical_box_mixed_coefficient {b B c : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hcl : ∀ p ∈ closedCoordTriangle 0 B, c ≤ S.lam p.1 p.2)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    let box := canonicalCubicRationalTriangleBox hB hBb H hcl
    intervalIntegral.rationalCubicCoefficient
      box.J box.r box.w box.z p = canonicalMixedCoefficient b S p := by
  dsimp only
  have hquot := canonical_box_mass_quotients hB hBb H hcl hp
  simp only [intervalIntegral.rationalCubicCoefficient,
    canonicalCubicRationalTriangleBox] at hquot ⊢
  rw [hquot.1, hquot.2]
  rw [canonicalMixedCoefficient]
  ring

/-- The rational box source is the canonical incoming source for the
outgoing quotient. -/
theorem canonical_box_quotient_source {b B c : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hcl : ∀ p ∈ closedCoordTriangle 0 B, c ≤ S.lam p.1 p.2)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    let box := canonicalCubicRationalTriangleBox hB hBb H hcl
    intervalIntegral.rationalCubicSource
      box.J box.r box.w box.z box.H p =
        canonicalQuotientSource b S p := by
  dsimp only
  rw [intervalIntegral.rationalCubicSource,
    canonical_box_mixed_coefficient hB hBb H hcl hp]
  change canonicalMixedCoefficient b S p *
    (-canonicalSourceFactor S p / S.lam p.1 p.2) =
      canonicalQuotientSource b S p
  rw [canonicalQuotientSource, canonicalSourceFactor]
  ring

end ChristodoulouBV.C1Solution

end
