module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointHorizontalDifference
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Two-input Picard primitive derivative bounds

The numerical full-pair coefficient box controls the differences of the
gravitational and scalar horizontal primitive first jets.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- Differences of gravitational horizontal primitive coordinate jets are
bounded linearly in the width and the input coordinate distance. -/
theorem Box.picard_lam_primitive_coordinate_sub_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x y : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (i : Fin 2) :
    |horizontalIntegralJet a x.1.toTriple.gravitational
        (fderivWithin ℝ x.1.toTriple.gravitational
          (closedCoordTriangle a b)) p (coordinateDirection i) -
      horizontalIntegralJet a y.1.toTriple.gravitational
        (fderivWithin ℝ y.1.toTriple.gravitational
          (closedCoordTriangle a b)) p (coordinateDirection i)| ≤
      ((numericalLedger M).KΔ₀ + (numericalLedger M).KΔ₁) *
        (b - a) * x.1.coordinateDistance y.1 := by
  let B := numericalLedger M
  let D := x.1.coordinateDistance y.1
  let k₁ := x.1.toTriple.gravitational
  let k₂ := y.1.toTriple.gravitational
  let G₁ := fderivWithin ℝ k₁ (closedCoordTriangle a b)
  let G₂ := fderivWithin ℝ k₂ (closedCoordTriangle a b)
  have hT : 0 ≤ b - a := sub_nonneg.mpr hab.le
  have hD : 0 ≤ D := (dist_nonneg).trans
    (x.1.dist_le_coordinateDistance hab.le y.1)
  have hKΔ₀ : 0 ≤ B.KΔ₀ := B.nonneg.2.2.2.2.2.1
  have hKΔ₁ : 0 ≤ B.KΔ₁ := B.nonneg.2.2.2.2.2.2.1
  have hk₁ := (x.picard_coefficients_c1 hab hM hsmall).1
  have hk₂ := (y.picard_coefficients_c1 hab hM hsmall).1
  have hunique : UniqueDiffOn ℝ (closedCoordTriangle a b) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hG₁ : ContinuousOn G₁ (closedCoordTriangle a b) :=
    hk₁.continuousOn_fderivWithin hunique (by norm_num)
  have hG₂ : ContinuousOn G₂ (closedCoordTriangle a b) :=
    hk₂.continuousOn_fderivWithin hunique (by norm_num)
  have hmean : |horizontalMean a k₁ p - horizontalMean a k₂ p| ≤
      B.KΔ₀ * (b - a) * D := by
    apply abs_horizontalMean_sub_le_const hk₁.continuousOn hk₂.continuousOn
      (mul_nonneg (mul_nonneg hKΔ₀ hT) hD) ?_ hp
    intro q hq
    have hgap : q.2 - q.1 ≤ b - a := by linarith only [hq.1, hq.2.2]
    have h := (x.gravitational_value_bounds_ledger y hab hM hsmall hq).2.2
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgap hKΔ₀) hD)
  have hjet : ∀ j : Fin 2,
      |horizontalMeanJet a G₁ p (coordinateDirection j) -
        horizontalMeanJet a G₂ p (coordinateDirection j)| ≤ B.KΔ₁ * D := by
    intro j
    apply abs_horizontalMeanJet_sub_coordinate_le hG₁ hG₂
      (mul_nonneg hKΔ₁ hD) ?_ hp j
    intro q hq
    exact ⟨(x.gravitational_jet_bounds_ledger y hab hM hsmall hq
      (by simp : (1, 0) ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)))).2.2,
      (x.gravitational_jet_bounds_ledger y hab hM hsmall hq
      (by simp : (0, 1) ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)))).2.2⟩
  have h := abs_horizontalIntegralJet_sub_coordinate_le
    (mul_nonneg (mul_nonneg hKΔ₀ hT) hD)
    (mul_nonneg hKΔ₁ hD)
    hp hmean hjet i
  convert h using 1
  ring

/-- Differences of scalar-source horizontal primitive coordinate jets are
bounded quadratically in the width and linearly in the input distance. -/
theorem Box.picard_h_primitive_coordinate_sub_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x y : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (i : Fin 2) :
    |horizontalIntegralJet a x.1.toTriple.scalarSource
        (fderivWithin ℝ x.1.toTriple.scalarSource
          (closedCoordTriangle a b)) p (coordinateDirection i) -
      horizontalIntegralJet a y.1.toTriple.scalarSource
        (fderivWithin ℝ y.1.toTriple.scalarSource
          (closedCoordTriangle a b)) p (coordinateDirection i)| ≤
      ((numericalLedger M).QΔ₀ + (numericalLedger M).QΔ₁) *
        (b - a) ^ 2 * x.1.coordinateDistance y.1 := by
  let B := numericalLedger M
  let D := x.1.coordinateDistance y.1
  let k₁ := x.1.toTriple.scalarSource
  let k₂ := y.1.toTriple.scalarSource
  let G₁ := fderivWithin ℝ k₁ (closedCoordTriangle a b)
  let G₂ := fderivWithin ℝ k₂ (closedCoordTriangle a b)
  have hT : 0 ≤ b - a := sub_nonneg.mpr hab.le
  have hD : 0 ≤ D := (dist_nonneg).trans
    (x.1.dist_le_coordinateDistance hab.le y.1)
  have hQΔ₀ : 0 ≤ B.QΔ₀ := B.nonneg.2.2.2.2.2.2.2.1
  have hQΔ₁ : 0 ≤ B.QΔ₁ := B.nonneg.2.2.2.2.2.2.2.2
  have hk₁ := (x.picard_coefficients_c1 hab hM hsmall).2
  have hk₂ := (y.picard_coefficients_c1 hab hM hsmall).2
  have hunique : UniqueDiffOn ℝ (closedCoordTriangle a b) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hG₁ : ContinuousOn G₁ (closedCoordTriangle a b) :=
    hk₁.continuousOn_fderivWithin hunique (by norm_num)
  have hG₂ : ContinuousOn G₂ (closedCoordTriangle a b) :=
    hk₂.continuousOn_fderivWithin hunique (by norm_num)
  have hmean : |horizontalMean a k₁ p - horizontalMean a k₂ p| ≤
      B.QΔ₀ * (b - a) ^ 2 * D := by
    apply abs_horizontalMean_sub_le_const hk₁.continuousOn hk₂.continuousOn
      (mul_nonneg (mul_nonneg hQΔ₀ (sq_nonneg _)) hD) ?_ hp
    intro q hq
    have hgap : q.2 - q.1 ≤ b - a := by linarith only [hq.1, hq.2.2]
    have hgap₀ : 0 ≤ q.2 - q.1 := sub_nonneg.mpr hq.2.1
    have h := (x.scalarSource_value_bounds_ledger y hab hM hsmall hq).2.2
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hgap₀ hT).2 hgap)
        hQΔ₀) hD)
  have hjet : ∀ j : Fin 2,
      |horizontalMeanJet a G₁ p (coordinateDirection j) -
        horizontalMeanJet a G₂ p (coordinateDirection j)| ≤
          B.QΔ₁ * (b - a) * D := by
    intro j
    apply abs_horizontalMeanJet_sub_coordinate_le hG₁ hG₂
      (mul_nonneg (mul_nonneg hQΔ₁ hT) hD) ?_ hp j
    intro q hq
    have hgap : q.2 - q.1 ≤ b - a := by linarith only [hq.1, hq.2.2]
    have hu := x.scalarSource_jet_sub_bound_ledger y hab hM hsmall hq
      (by simp : (1, 0) ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)))
    have hv := x.scalarSource_jet_sub_bound_ledger y hab hM hsmall hq
      (by simp : (0, 1) ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)))
    exact ⟨hu.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgap hQΔ₁) hD),
      hv.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgap hQΔ₁) hD)⟩
  have h := abs_horizontalIntegralJet_sub_coordinate_le
    (mul_nonneg (mul_nonneg hQΔ₀ (sq_nonneg _)) hD)
    (mul_nonneg (mul_nonneg hQΔ₁ hT) hD)
    hp hmean hjet i
  convert h using 1
  ring

end ChristodoulouBV.AxisPicard

end
