module

public import ChristodoulouBV.C1Solution.UniquenessVerticalQuotients
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsReciprocal
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Vertical-only reciprocal complement bounds

The reciprocal of `1 - μ` and its outgoing quotient-rule expression inherit
the fixed-ray bounds of the canonical mass ratio.
-/

public section

namespace intervalIntegral

/-- The two reciprocal complements and their outgoing jet expressions obey
the value and difference bounds from the arbitrary-bound ledger. -/
theorem CubicRationalVerticalPairBox.inverse_complement_vertical_bounds
    {a b c ε : ℝ} (B : CubicRationalVerticalPairBox a b c)
    (hab : a < b) (hwidth : b - a ≤ 1) (hc : 0 < c) (hε : 0 < ε)
    (hgap₁ : ∀ p ∈ closedCoordTriangle a b,
      ε ≤ 1 - cubicLinearQuotient B.first.J B.first.r p)
    (hgap₂ : ∀ p ∈ closedCoordTriangle a b,
      ε ≤ 1 - cubicLinearQuotient B.second.J B.second.r p) :
    ∀ p ∈ closedCoordTriangle a b,
      let μ₁ := cubicLinearQuotient B.first.J B.first.r
      let μ₂ := cubicLinearQuotient B.second.J B.second.r
      let μv₁ := (fderivWithin ℝ μ₁ (closedCoordTriangle a b) p) (0, 1)
      let μv₂ := (fderivWithin ℝ μ₂ (closedCoordTriangle a b) p) (0, 1)
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
        (Md / ε ^ 2) * (p.2 - p.1) ^ 2 * B.D p.1 ∧
      |μv₁ / (1 - μ₁ p) ^ 2 - μv₂ / (1 - μ₂ p) ^ 2| ≤
        (Mdv / ε ^ 2 + 2 * Mv * Md / ε ^ 3) *
          (p.2 - p.1) * B.D p.1 := by
  intro p hp
  dsimp only
  let d := p.2 - p.1
  let μ₁ := cubicLinearQuotient B.first.J B.first.r
  let μ₂ := cubicLinearQuotient B.second.J B.second.r
  let μv₁ := (fderivWithin ℝ μ₁ (closedCoordTriangle a b) p) (0, 1)
  let μv₂ := (fderivWithin ℝ μ₂ (closedCoordTriangle a b) p) (0, 1)
  let Mv := B.Jv / c + B.J₀ * B.Rv / c ^ 2
  let Md := B.JΔ / c + B.J₀ / c ^ 2
  let Mdv := B.JΔv / c + B.Jv / c ^ 2 +
    B.JΔ * B.Rv / c ^ 2 + B.J₀ * B.RΔv / c ^ 2 +
    2 * B.J₀ * B.Rv / c ^ 3
  have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
  have hd : 0 ≤ d := sub_nonneg.mpr hcoord.2.1
  have hdle : d ≤ 1 := by dsimp [d]; linarith only [hcoord.1, hcoord.2.2, hwidth]
  have hD : 0 ≤ B.D p.1 :=
    B.D_nonneg p.1 ⟨hcoord.1, hcoord.2.1.trans hcoord.2.2⟩
  rcases B.bounds_nonneg with ⟨hJ₀, hJv, hJΔ, hJΔv, hRv, hRΔv⟩
  have hMv : 0 ≤ Mv := by dsimp [Mv]; positivity
  have hMd : 0 ≤ Md := by dsimp [Md]; positivity
  have hμv := B.quotient_vertical_bounds hab hc p hp
  have hμd := B.linearQuotient_value_sub_bound hc p hp
  have hμdv := B.linearQuotient_vertical_sub_bound hab hc p hp
  exact ⟨inv_one_sub_le hε (hgap₁ p hp),
    inv_one_sub_le hε (hgap₂ p hp),
    abs_inverseOneSubJet_le_of_gap_bounds hε hd hMv
      (hgap₁ p hp) hμv.1.1,
    abs_inverseOneSubJet_le_of_gap_bounds hε hd hMv
      (hgap₂ p hp) hμv.1.2,
    abs_inv_one_sub_sub_le_of_quadratic_gap_bounds hε
      (hgap₁ p hp) (hgap₂ p hp) hμd,
    abs_inverseOneSubJet_sub_le_of_gap_bounds hε hd hdle
      hD hMv hMd (hgap₁ p hp) (hgap₂ p hp)
      hμd hμv.1.2 hμdv⟩

end intervalIntegral

end
