module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointMeanError
import all ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBoxVolterraPair
import Mathlib.Tactic

/-!
# Complementary denominator margin for the Picard pair box

The explicit lifetime keeps both removable mass ratios below one quarter,
so the common rational coefficient box has denominator margin three quarters.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- The cubic numerator coefficient of the two-input Volterra box is bounded
by the mass-ratio entry of the numerical lifetime ledger. -/
theorem Box.pair_mass_coefficient_le_ledger {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x y : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M) (hsize : b - a ≤ 1) :
    (x.toCubicRationalPairBox y hab hM hsize).J₀ / (1 / 4 : ℝ) ≤
      (numericalLedger M).mu₀ := by
  dsimp [Box.toCubicRationalPairBox, Box.toAttenuatedVolterraPairData,
    intervalIntegral.AttenuatedVolterraPairData.toCubicRationalPairBox,
    intervalIntegral.AttenuatedVolterraPairData.valueCoefficient,
    numericalLedger, intervalIntegral.weightedDiagonalQuadraticValueCoefficient]
  exact le_max_right (0 : ℝ) _

/-- At the explicit lifetime, both complementary denominators of the
common cubic pair box are at least three quarters throughout the triangle. -/
theorem Box.pair_complement_bounds {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x y : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    let hsize : b - a ≤ 1 :=
      (numerical_lifetime_bounds hM (sub_pos.mpr hab) hsmall).1
    let B := x.toCubicRationalPairBox y hab hM hsize
    (3 / 4 : ℝ) ≤ 1 -
      intervalIntegral.cubicLinearQuotient B.first.J B.first.r p ∧
    (3 / 4 : ℝ) ≤ 1 -
      intervalIntegral.cubicLinearQuotient B.second.J B.second.r p := by
  dsimp only
  let T := b - a
  have hT : 0 < T := sub_pos.mpr hab
  have hwidth : T ≤ 1 :=
    (numerical_lifetime_bounds hM hT hsmall).1
  let B := x.toCubicRationalPairBox y hab hM hwidth
  have hμ := (numerical_lifetime_bounds hM hT hsmall).2.1
  have hcoef : B.J₀ / (1 / 4 : ℝ) ≤ (numericalLedger M).mu₀ :=
    x.pair_mass_coefficient_le_ledger y hab hM hwidth
  have hcoef0 : 0 ≤ (numericalLedger M).mu₀ :=
    (numericalLedger M).nonneg.1
  have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
  have hgap : 0 ≤ p.2 - p.1 := sub_nonneg.mpr hcoord.2.1
  have hgapT : p.2 - p.1 ≤ T := by dsimp [T]; linarith only [hcoord.1, hcoord.2.2]
  have hsq : (p.2 - p.1) ^ 2 ≤ T ^ 2 := by nlinarith only [hgap, hgapT, hT.le]
  have hbound : (B.J₀ / (1 / 4 : ℝ)) * (p.2 - p.1) ^ 2 ≤ 1 / 100 := by
    calc
      _ ≤ (numericalLedger M).mu₀ * (p.2 - p.1) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      _ ≤ (numericalLedger M).mu₀ * T ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hcoef0
      _ ≤ 1 / 100 := hμ
  have hvalues := B.linearQuotient_value_bounds (by norm_num) p hp
  constructor
  · linarith only [hvalues.2.1, hbound]
  · linarith only [hvalues.2.2, hbound]

end ChristodoulouBV.AxisPicard

end
