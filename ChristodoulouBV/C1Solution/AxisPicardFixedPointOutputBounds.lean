module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointPrimitiveJet
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Endpoint bounds for the axis Picard update

These estimates turn the established coefficient bounds into bounds for the
horizontal and vertical derivatives supplied by the fundamental theorem of
calculus. They also bound the transverse integral in the output first jet.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.AxisPicard

/-- Integrating a uniformly bounded triangle kernel horizontally costs at
most the width of the triangle. -/
theorem abs_horizontal_integral_le_const {a b A u v : ℝ}
    {k : ℝ × ℝ → ℝ} (hA : 0 ≤ A)
    (hk : ∀ p ∈ closedCoordTriangle a b, |k p| ≤ A)
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    |∫ s in a..u, k (s, v)| ≤ A * (b - a) := by
  have hbound : ∀ s ∈ Ι a u, ‖k (s, v)‖ ≤ A := by
    intro s hs
    have hsI : s ∈ Icc a u := by
      rw [uIoc_of_le hau] at hs
      exact ⟨hs.1.le, hs.2⟩
    simpa only [Real.norm_eq_abs] using
      hk (s, v) ⟨hsI.1, hsI.2.trans huv, hvb⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := u) (C := A) (f := fun s => k (s, v)) hbound
  have hspan : u - a ≤ b - a := by linarith only [huv, hvb]
  have hnorm : |∫ s in a..u, k (s, v)| ≤ A * (u - a) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hau)] using h
  exact hnorm.trans (mul_le_mul_of_nonneg_left hspan hA)

/-- A linearly vanishing triangle kernel has a quadratic-width transverse
integral bound. -/
theorem abs_horizontal_integral_le_linear {a b A u v : ℝ}
    {k : ℝ × ℝ → ℝ} (hA : 0 ≤ A)
    (hk : ∀ p ∈ closedCoordTriangle a b,
      |k p| ≤ A * (p.2 - p.1))
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    |∫ s in a..u, k (s, v)| ≤ A * (b - a) ^ 2 :=
  abs_horizontal_integral_le_square hA hk hau huv hvb

/-- The outgoing horizontal endpoint derivative has the linear-width
gravitational bound. -/
theorem Box.picard_lam_horizontal_deriv_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |x.1.toTriple.gravitational p| ≤ (numericalLedger M).K₀ * (b - a) := by
  have h := (x.gravitational_value_bounds_ledger x hab hM hsmall hp).1
  have hgap : p.2 - p.1 ≤ b - a := by linarith only [hp.1, hp.2.2]
  exact h.trans (mul_le_mul_of_nonneg_left hgap
    (numericalLedger M).nonneg.2.1)

/-- The scalar horizontal endpoint derivative has the quadratic-width
source bound. -/
theorem Box.picard_h_horizontal_deriv_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |x.1.toTriple.scalarSource p| ≤
      (numericalLedger M).Q₀ * (b - a) ^ 2 := by
  have h := (x.scalarSource_value_bounds_ledger x hab hM hsmall hp).1
  have hgap : p.2 - p.1 ≤ b - a := by linarith only [hp.1, hp.2.2]
  have hgap₀ : 0 ≤ p.2 - p.1 := sub_nonneg.mpr hp.2.1
  have hT₀ : 0 ≤ b - a := by linarith only [hab]
  exact h.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ hgap₀ hT₀).2 hgap) (numericalLedger M).nonneg.2.2.2.1)

/-- The transverse integral in the outgoing first jet has the linear-width
bound from the coefficient first-jet ledger. -/
theorem Box.picard_lam_transverse_integral_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |∫ s in a..p.1,
      (fderivWithin ℝ x.1.toTriple.gravitational
        (closedCoordTriangle a b) (s, p.2)) (0, 1)| ≤
      (numericalLedger M).K₁ * (b - a) := by
  apply abs_horizontal_integral_le_const
    (k := fun q => (fderivWithin ℝ x.1.toTriple.gravitational
      (closedCoordTriangle a b) q) (0, 1))
    (numericalLedger M).nonneg.2.2.1 ?_ hp.1 hp.2.1 hp.2.2
  intro q hq
  exact (x.gravitational_jet_bounds_ledger x hab hM hsmall hq
    (by simp : (0, 1) ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)))).1

/-- The transverse integral in the scalar first jet has a quadratic-width
bound. -/
theorem Box.picard_h_transverse_integral_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |∫ s in a..p.1,
      (fderivWithin ℝ x.1.toTriple.scalarSource
        (closedCoordTriangle a b) (s, p.2)) (0, 1)| ≤
      (numericalLedger M).Q₁ * (b - a) ^ 2 := by
  apply abs_horizontal_integral_le_square
    (k := fun q => (fderivWithin ℝ x.1.toTriple.scalarSource
      (closedCoordTriangle a b) q) (0, 1))
    (numericalLedger M).nonneg.2.2.2.2.1 ?_ hp.1 hp.2.1 hp.2.2
  intro q hq
  exact (x.scalarSource_jet_bound_ledger x hab hM hsmall hq
    (by simp : (0, 1) ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)))).1

end ChristodoulouBV.AxisPicard

end
