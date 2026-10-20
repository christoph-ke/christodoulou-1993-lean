module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointLedger
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Value bounds for the axis Picard update

The linear and quadratic source bounds integrate to the first row of the
Picard output estimates on the closed triangle.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.AxisPicard

/-- A linearly vanishing kernel has a quadratic-width horizontal primitive
bound on the closed axis triangle. -/
theorem abs_horizontal_integral_le_square {a b K u v : ℝ}
    {k : ℝ × ℝ → ℝ} (hK : 0 ≤ K)
    (hk : ∀ p ∈ closedCoordTriangle a b,
      |k p| ≤ K * (p.2 - p.1))
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    |∫ s in a..u, k (s, v)| ≤ K * (b - a) ^ 2 := by
  have hT : 0 ≤ b - a := by linarith only [hau, huv, hvb]
  have hspan : u - a ≤ b - a := by linarith only [huv, hvb]
  have hbound : ∀ s ∈ Ι a u, ‖k (s, v)‖ ≤ K * (b - a) := by
    intro s hs
    have hsI : s ∈ Icc a u := by
      rw [uIoc_of_le hau] at hs
      exact ⟨hs.1.le, hs.2⟩
    have hsk : (s, v) ∈ closedCoordTriangle a b := by
      change a ≤ s ∧ s ≤ v ∧ v ≤ b
      exact ⟨hsI.1, hsI.2.trans huv, hvb⟩
    have hgap : v - s ≤ b - a := by linarith only [hsI.1, hvb]
    simpa only [Real.norm_eq_abs] using
      (hk (s, v) hsk).trans (mul_le_mul_of_nonneg_left hgap hK)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := u) (C := K * (b - a)) (f := fun s => k (s, v)) hbound
  have hmul : K * (b - a) * (u - a) ≤ K * (b - a) ^ 2 := by
    calc
      _ ≤ K * (b - a) * (b - a) :=
        mul_le_mul_of_nonneg_left hspan (mul_nonneg hK hT)
      _ = _ := by ring
  have hnorm : |∫ s in a..u, k (s, v)| ≤ K * (b - a) * (u - a) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hau)] using h
  exact hnorm.trans hmul

/-- A quadratically vanishing source has a cubic-width horizontal primitive
bound on the closed axis triangle. -/
theorem abs_horizontal_integral_le_cube {a b Q u v : ℝ}
    {q : ℝ × ℝ → ℝ} (hQ : 0 ≤ Q)
    (hq : ∀ p ∈ closedCoordTriangle a b,
      |q p| ≤ Q * (p.2 - p.1) ^ 2)
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    |∫ s in a..u, q (s, v)| ≤ Q * (b - a) ^ 3 := by
  have hT : 0 ≤ b - a := by linarith only [hau, huv, hvb]
  have hspan : u - a ≤ b - a := by linarith only [huv, hvb]
  have hbound : ∀ s ∈ Ι a u, ‖q (s, v)‖ ≤ Q * (b - a) ^ 2 := by
    intro s hs
    have hsI : s ∈ Icc a u := by
      rw [uIoc_of_le hau] at hs
      exact ⟨hs.1.le, hs.2⟩
    have hsq : (s, v) ∈ closedCoordTriangle a b := by
      change a ≤ s ∧ s ≤ v ∧ v ≤ b
      exact ⟨hsI.1, hsI.2.trans huv, hvb⟩
    have hgap : v - s ≤ b - a := by linarith only [hsI.1, hvb]
    have hgap₀ : 0 ≤ v - s := sub_nonneg.mpr (hsI.2.trans huv)
    simpa only [Real.norm_eq_abs] using
      (hq (s, v) hsq).trans
        (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hgap₀ hT).2 hgap) hQ)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := u) (C := Q * (b - a) ^ 2) (f := fun s => q (s, v)) hbound
  have hmul : Q * (b - a) ^ 2 * (u - a) ≤ Q * (b - a) ^ 3 := by
    calc
      _ ≤ Q * (b - a) ^ 2 * (b - a) :=
        mul_le_mul_of_nonneg_left hspan (mul_nonneg hQ (sq_nonneg _))
      _ = _ := by ring
  have hnorm : |∫ s in a..u, q (s, v)| ≤ Q * (b - a) ^ 2 * (u - a) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hau)] using h
  exact hnorm.trans hmul

/-- A linearly vanishing kernel has a quadratic-width vertical primitive
bound on the closed axis triangle. -/
theorem abs_vertical_integral_le_square {a b K u v : ℝ}
    {k : ℝ × ℝ → ℝ} (hK : 0 ≤ K)
    (hk : ∀ p ∈ closedCoordTriangle a b,
      |k p| ≤ K * (p.2 - p.1))
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    |∫ s in u..v, k (u, s)| ≤ K * (b - a) ^ 2 := by
  have hT : 0 ≤ b - a := by linarith only [hau, huv, hvb]
  have hspan : v - u ≤ b - a := by linarith only [hau, hvb]
  have hbound : ∀ s ∈ Ι u v, ‖k (u, s)‖ ≤ K * (b - a) := by
    intro s hs
    have hsI : s ∈ Icc u v := by
      rw [uIoc_of_le huv] at hs
      exact ⟨hs.1.le, hs.2⟩
    have hsk : (u, s) ∈ closedCoordTriangle a b := by
      change a ≤ u ∧ u ≤ s ∧ s ≤ b
      exact ⟨hau, hsI.1, hsI.2.trans hvb⟩
    have hgap : s - u ≤ b - a := by linarith only [hau, hsI.2, hvb]
    simpa only [Real.norm_eq_abs] using
      (hk (u, s) hsk).trans (mul_le_mul_of_nonneg_left hgap hK)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := u) (b := v) (C := K * (b - a)) (f := fun s => k (u, s)) hbound
  have hmul : K * (b - a) * (v - u) ≤ K * (b - a) ^ 2 := by
    calc
      _ ≤ K * (b - a) * (b - a) :=
        mul_le_mul_of_nonneg_left hspan (mul_nonneg hK hT)
      _ = _ := by ring
  have hnorm : |∫ s in u..v, k (u, s)| ≤ K * (b - a) * (v - u) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr huv)] using h
  exact hnorm.trans hmul

/-- The outgoing Picard field differs from its edge trace by at most the
quadratic-width gravitational bound. -/
theorem Box.picard_lam_value_bound {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |(x.1.toTriple.picard a g hEdge).lam p - g p.2| ≤
      (numericalLedger M).K₀ * (b - a) ^ 2 := by
  have hK : 0 ≤ (numericalLedger M).K₀ :=
    (numericalLedger M).nonneg.2.1
  have hk : ∀ q ∈ closedCoordTriangle a b,
      |x.1.toTriple.gravitational q| ≤
        (numericalLedger M).K₀ * (q.2 - q.1) := by
    intro q hq
    exact (x.gravitational_value_bounds_ledger x hab hM hsmall hq).1
  have hbound := abs_horizontal_integral_le_square hK hk hp.1 hp.2.1 hp.2.2
  simpa only [Triple.picard, add_sub_cancel_left] using hbound

/-- The scalar Picard field differs from its edge trace by at most the
cubic-width source bound. -/
theorem Box.picard_h_value_bound {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |(x.1.toTriple.picard a g hEdge).h p - hEdge p.2| ≤
      (numericalLedger M).Q₀ * (b - a) ^ 3 := by
  have hQ : 0 ≤ (numericalLedger M).Q₀ :=
    (numericalLedger M).nonneg.2.2.2.1
  have hq : ∀ q ∈ closedCoordTriangle a b,
      |x.1.toTriple.scalarSource q| ≤
        (numericalLedger M).Q₀ * (q.2 - q.1) ^ 2 := by
    intro q hq
    exact (x.scalarSource_value_bounds_ledger x hab hM hsmall hq).1
  have hbound := abs_horizontal_integral_le_cube hQ hq hp.1 hp.2.1 hp.2.2
  simpa only [Triple.picard, add_sub_cancel_left] using hbound

/-- The incoming Picard field differs from the negative diagonal edge trace
by at most twice the quadratic-width gravitational bound. -/
theorem Box.picard_nu_value_bound {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |(x.1.toTriple.picard a g hEdge).nu p + g p.1| ≤
      2 * (numericalLedger M).K₀ * (b - a) ^ 2 := by
  have huI : (p.1, p.1) ∈ closedCoordTriangle a b := by
    change a ≤ p.1 ∧ p.1 ≤ p.1 ∧ p.1 ≤ b
    exact ⟨hp.1, le_refl _, hp.2.1.trans hp.2.2⟩
  have hdiag := x.picard_lam_value_bound hab hM hsmall huI
  have hK : 0 ≤ (numericalLedger M).K₀ :=
    (numericalLedger M).nonneg.2.1
  have hk : ∀ q ∈ closedCoordTriangle a b,
      |x.1.toTriple.gravitational q| ≤
        (numericalLedger M).K₀ * (q.2 - q.1) := by
    intro q hq
    exact (x.gravitational_value_bounds_ledger x hab hM hsmall hq).1
  have hv := abs_vertical_integral_le_square hK hk hp.1 hp.2.1 hp.2.2
  have heq : (x.1.toTriple.picard a g hEdge).nu p + g p.1 =
      -((x.1.toTriple.picard a g hEdge).lam (p.1, p.1) - g p.1) +
        ∫ s in p.1..p.2, x.1.toTriple.gravitational (p.1, s) := by
    simp only [Triple.picard]
    ring
  rw [heq]
  calc
    _ ≤ |-((x.1.toTriple.picard a g hEdge).lam (p.1, p.1) - g p.1)| +
        |∫ s in p.1..p.2, x.1.toTriple.gravitational (p.1, s)| :=
      abs_add_le _ _
    _ ≤ 2 * (numericalLedger M).K₀ * (b - a) ^ 2 := by
      rw [abs_neg]
      linarith only [hdiag, hv]

/-- The three Picard output values satisfy the value part of the closed box
under the explicit lifetime. -/
theorem Box.picard_value_bounds {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (D : EdgeData a b M g hEdge) (x : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (1 / 4 : ℝ) ≤ (x.1.toTriple.picard a g hEdge).lam p ∧
      (x.1.toTriple.picard a g hEdge).lam p ≤ 3 / 4 ∧
      |(x.1.toTriple.picard a g hEdge).nu p| ≤ 3 / 4 ∧
      |(x.1.toTriple.picard a g hEdge).h p| ≤ 2 * M := by
  let B := numericalLedger M
  let T := b - a
  have hT : 0 < T := sub_pos.mpr hab
  have hsmall₀ := B.lifetime_bounds hM hT hsmall
  have hK := hsmall₀.2.2.2.1
  have hQ := hsmall₀.2.2.2.2.2.1
  have hpv : p.2 ∈ Icc a b := ⟨hp.1.trans hp.2.1, hp.2.2⟩
  have hpu : p.1 ∈ Icc a b := ⟨hp.1, hp.2.1.trans hp.2.2⟩
  have hLam := x.picard_lam_value_bound hab hM hsmall hp
  have hNu := x.picard_nu_value_bound hab hM hsmall hp
  have hH := x.picard_h_value_bound hab hM hsmall hp
  have hglo := D.g_lower p.2 hpv
  have hghi := D.g_upper p.2 hpv
  have hguLo := D.g_lower p.1 hpu
  have hguHi := D.g_upper p.1 hpu
  have hhEdge := D.h_bound p.2 hpv
  have hHtriangle : |(x.1.toTriple.picard a g hEdge).h p| ≤
      |(x.1.toTriple.picard a g hEdge).h p - hEdge p.2| +
        |hEdge p.2| := by
    simpa only [sub_add_cancel] using
      (abs_add_le ((x.1.toTriple.picard a g hEdge).h p - hEdge p.2)
        (hEdge p.2))
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := (abs_le.mp hLam).1
    linarith only [h, hglo, hK]
  · have h := (abs_le.mp hLam).2
    linarith only [h, hghi, hK]
  · apply abs_le.mpr
    constructor
    · have h := (abs_le.mp hNu).1
      linarith only [h, hguHi, hK]
    · have h := (abs_le.mp hNu).2
      linarith only [h, hguLo, hK]
  · linarith only [hHtriangle, hH, hhEdge, hQ, hM]

/-- The incoming Picard output has the explicit strict-sign margin required
by the removable coefficients. -/
theorem Box.picard_nu_le_neg_quarter {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (x.1.toTriple.picard a g hEdge).nu p ≤ -(1 / 4 : ℝ) := by
  have hpu : p.1 ∈ Icc a b := ⟨hp.1, hp.2.1.trans hp.2.2⟩
  have hNu := x.picard_nu_value_bound hab hM hsmall hp
  exact output_nu_le_neg_quarter hM (sub_pos.mpr hab) hsmall
    (D.g_lower p.1 hpu) (abs_le.mp hNu).2

end ChristodoulouBV.AxisPicard

end
