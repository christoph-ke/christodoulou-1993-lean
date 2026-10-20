module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointPairPrimitive
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Two-input Picard output estimates

The common coefficient box controls differences of the three updated value
fields and the outgoing and scalar first jets.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.AxisPicard

/-- A uniform difference bound for two continuous triangle kernels passes
to their horizontal primitives with one width factor. -/
theorem abs_horizontal_integral_sub_le_const {a b A u v : ℝ}
    {k₁ k₂ : ℝ × ℝ → ℝ}
    (hk₁ : ContinuousOn k₁ (closedCoordTriangle a b))
    (hk₂ : ContinuousOn k₂ (closedCoordTriangle a b))
    (hA : 0 ≤ A)
    (hbound : ∀ p ∈ closedCoordTriangle a b, |k₁ p - k₂ p| ≤ A)
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    |(∫ s in a..u, k₁ (s, v)) - (∫ s in a..u, k₂ (s, v))| ≤
      A * (b - a) := by
  have hint (k : ℝ × ℝ → ℝ)
      (hk : ContinuousOn k (closedCoordTriangle a b)) :
      IntervalIntegrable (fun s => k (s, v)) volume a u := by
    apply ContinuousOn.intervalIntegrable_of_Icc hau
    exact hk.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs.1, hs.2.trans huv, hvb⟩)
  rw [← intervalIntegral.integral_sub (hint k₁ hk₁) (hint k₂ hk₂)]
  exact abs_horizontal_integral_le_const hA hbound hau huv hvb

/-- A uniform difference bound for two continuous triangle kernels passes
to their vertical primitives with one width factor. -/
theorem abs_vertical_integral_sub_le_const {a b A u v : ℝ}
    {k₁ k₂ : ℝ × ℝ → ℝ}
    (hk₁ : ContinuousOn k₁ (closedCoordTriangle a b))
    (hk₂ : ContinuousOn k₂ (closedCoordTriangle a b))
    (hA : 0 ≤ A)
    (hbound : ∀ p ∈ closedCoordTriangle a b, |k₁ p - k₂ p| ≤ A)
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    |(∫ s in u..v, k₁ (u, s)) - (∫ s in u..v, k₂ (u, s))| ≤
      A * (b - a) := by
  have hint (k : ℝ × ℝ → ℝ)
      (hk : ContinuousOn k (closedCoordTriangle a b)) :
      IntervalIntegrable (fun s => k (u, s)) volume u v := by
    apply ContinuousOn.intervalIntegrable_of_Icc huv
    exact hk.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hau, hs.1, hs.2.trans hvb⟩)
  rw [← intervalIntegral.integral_sub (hint k₁ hk₁) (hint k₂ hk₂)]
  exact abs_vertical_integral_le_const hA hbound hau huv hvb

/-- The outgoing Picard values differ by at most the gravitational
two-input coefficient times the squared width. -/
theorem Box.picard_lam_value_sub_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x y : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |(x.1.toTriple.picard a g hEdge).lam p -
      (y.1.toTriple.picard a g hEdge).lam p| ≤
      (numericalLedger M).KΔ₀ * (b - a) ^ 2 *
        x.1.coordinateDistance y.1 := by
  let B := numericalLedger M
  let D := x.1.coordinateDistance y.1
  have hk₁ := (x.picard_coefficients_c1 hab hM hsmall).1.continuousOn
  have hk₂ := (y.picard_coefficients_c1 hab hM hsmall).1.continuousOn
  have hD : 0 ≤ D := (dist_nonneg).trans
    (x.1.dist_le_coordinateDistance hab.le y.1)
  have hT : 0 ≤ b - a := sub_nonneg.mpr hab.le
  have hKΔ₀ : 0 ≤ B.KΔ₀ := B.nonneg.2.2.2.2.2.1
  have hbound : ∀ q ∈ closedCoordTriangle a b,
      |x.1.toTriple.gravitational q - y.1.toTriple.gravitational q| ≤
        B.KΔ₀ * (b - a) * D := by
    intro q hq
    have hgap : q.2 - q.1 ≤ b - a := by linarith only [hq.1, hq.2.2]
    exact (x.gravitational_value_bounds_ledger y hab hM hsmall hq).2.2.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgap hKΔ₀) hD)
  have h := abs_horizontal_integral_sub_le_const hk₁ hk₂
    (mul_nonneg (mul_nonneg hKΔ₀ hT) hD) hbound
    hp.1 hp.2.1 hp.2.2
  simp only [Triple.picard, add_sub_add_left_eq_sub] at *
  convert h using 1
  ring

/-- The scalar Picard values differ by at most the scalar two-input
coefficient times the cubed width. -/
theorem Box.picard_h_value_sub_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x y : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |(x.1.toTriple.picard a g hEdge).h p -
      (y.1.toTriple.picard a g hEdge).h p| ≤
      (numericalLedger M).QΔ₀ * (b - a) ^ 3 *
        x.1.coordinateDistance y.1 := by
  let B := numericalLedger M
  let D := x.1.coordinateDistance y.1
  have hk₁ := (x.picard_coefficients_c1 hab hM hsmall).2.continuousOn
  have hk₂ := (y.picard_coefficients_c1 hab hM hsmall).2.continuousOn
  have hD : 0 ≤ D := (dist_nonneg).trans
    (x.1.dist_le_coordinateDistance hab.le y.1)
  have hT : 0 ≤ b - a := sub_nonneg.mpr hab.le
  have hQΔ₀ : 0 ≤ B.QΔ₀ := B.nonneg.2.2.2.2.2.2.2.1
  have hbound : ∀ q ∈ closedCoordTriangle a b,
      |x.1.toTriple.scalarSource q - y.1.toTriple.scalarSource q| ≤
        B.QΔ₀ * (b - a) ^ 2 * D := by
    intro q hq
    have hgap : q.2 - q.1 ≤ b - a := by linarith only [hq.1, hq.2.2]
    have hgap₀ : 0 ≤ q.2 - q.1 := sub_nonneg.mpr hq.2.1
    exact (x.scalarSource_value_bounds_ledger y hab hM hsmall hq).2.2.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hgap₀ hT).2 hgap) hQΔ₀) hD)
  have h := abs_horizontal_integral_sub_le_const hk₁ hk₂
    (mul_nonneg (mul_nonneg hQΔ₀ (sq_nonneg _)) hD) hbound
    hp.1 hp.2.1 hp.2.2
  simp only [Triple.picard, add_sub_add_left_eq_sub] at *
  convert h using 1
  ring

/-- The incoming Picard values differ by at most twice the gravitational
two-input value coefficient times the squared width. -/
theorem Box.picard_nu_value_sub_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x y : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |(x.1.toTriple.picard a g hEdge).nu p -
      (y.1.toTriple.picard a g hEdge).nu p| ≤
      2 * (numericalLedger M).KΔ₀ * (b - a) ^ 2 *
        x.1.coordinateDistance y.1 := by
  let B := numericalLedger M
  let D := x.1.coordinateDistance y.1
  have hD : 0 ≤ D := (dist_nonneg).trans
    (x.1.dist_le_coordinateDistance hab.le y.1)
  have hT : 0 ≤ b - a := sub_nonneg.mpr hab.le
  have hK : 0 ≤ B.KΔ₀ := B.nonneg.2.2.2.2.2.1
  have hdiag : (p.1, p.1) ∈ closedCoordTriangle a b :=
    ⟨hp.1, le_refl _, hp.2.1.trans hp.2.2⟩
  have hlam := x.picard_lam_value_sub_bound y hab hM hsmall hdiag
  have hk₁ := (x.picard_coefficients_c1 hab hM hsmall).1.continuousOn
  have hk₂ := (y.picard_coefficients_c1 hab hM hsmall).1.continuousOn
  have hbound : ∀ q ∈ closedCoordTriangle a b,
      |x.1.toTriple.gravitational q - y.1.toTriple.gravitational q| ≤
        B.KΔ₀ * (b - a) * D := by
    intro q hq
    have hgap : q.2 - q.1 ≤ b - a := by linarith only [hq.1, hq.2.2]
    exact (x.gravitational_value_bounds_ledger y hab hM hsmall hq).2.2.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgap hK) hD)
  have hint := abs_vertical_integral_sub_le_const hk₁ hk₂
    (mul_nonneg (mul_nonneg hK hT) hD) hbound hp.1 hp.2.1 hp.2.2
  have htriangle := abs_add_le
    (-((x.1.toTriple.picard a g hEdge).lam (p.1, p.1) -
      (y.1.toTriple.picard a g hEdge).lam (p.1, p.1)))
    ((∫ s in p.1..p.2, x.1.toTriple.gravitational (p.1, s)) -
      (∫ s in p.1..p.2, y.1.toTriple.gravitational (p.1, s)))
  simp only [abs_neg] at htriangle
  change |(-((x.1.toTriple.picard a g hEdge).lam (p.1, p.1)) +
      ∫ s in p.1..p.2, x.1.toTriple.gravitational (p.1, s)) -
    (-((y.1.toTriple.picard a g hEdge).lam (p.1, p.1)) +
      ∫ s in p.1..p.2, y.1.toTriple.gravitational (p.1, s))| ≤ _
  calc
    _ = |(-((x.1.toTriple.picard a g hEdge).lam (p.1, p.1) -
        (y.1.toTriple.picard a g hEdge).lam (p.1, p.1))) +
        ((∫ s in p.1..p.2, x.1.toTriple.gravitational (p.1, s)) -
          (∫ s in p.1..p.2, y.1.toTriple.gravitational (p.1, s)))| := by congr 1; ring
    _ ≤ B.KΔ₀ * (b - a) ^ 2 * D +
        (B.KΔ₀ * (b - a) * D) * (b - a) := by
      exact htriangle.trans (add_le_add hlam hint)
    _ = 2 * B.KΔ₀ * (b - a) ^ 2 * D := by ring

end ChristodoulouBV.AxisPicard

end
