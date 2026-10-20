module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointOutputC1
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Bounds for the normalized horizontal Picard jets

The fixed-interval representation of the horizontal primitive bounds its
value and both coordinate components of its derivative without requiring a
separate boundary differentiation argument.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.AxisPicard

/-- A uniform kernel bound passes to its normalized horizontal mean. -/
theorem abs_horizontalMean_le_const {a b A : ℝ}
    {k : ℝ × ℝ → ℝ} (_hA : 0 ≤ A)
    (hk : ∀ q ∈ closedCoordTriangle a b, |k q| ≤ A)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |horizontalMean a k p| ≤ A := by
  have hbound : ∀ t ∈ Ι (0 : ℝ) 1,
      ‖k (horizontalSegment a p t)‖ ≤ A := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact Ioc_subset_Icc_self ht
    simpa only [Real.norm_eq_abs] using
      hk _ (horizontalSegment_mem_closedCoordTriangle hp htI)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := A)
    (f := fun t => k (horizontalSegment a p t)) hbound
  simpa only [horizontalMean, Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h

/-- A linear axis-gap bound gives a width bound for the normalized
horizontal mean. -/
theorem abs_horizontalMean_le_linear {a b A : ℝ}
    {k : ℝ × ℝ → ℝ} (hA : 0 ≤ A)
    (hk : ∀ q ∈ closedCoordTriangle a b,
      |k q| ≤ A * (q.2 - q.1))
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |horizontalMean a k p| ≤ A * (b - a) := by
  have hab : a ≤ b := hp.1.trans (hp.2.1.trans hp.2.2)
  apply abs_horizontalMean_le_const (mul_nonneg hA (sub_nonneg.mpr hab)) ?_ hp
  intro q hq
  have hgap : q.2 - q.1 ≤ b - a := by linarith only [hq.1, hq.2.2]
  exact (hk q hq).trans (mul_le_mul_of_nonneg_left hgap hA)

/-- A quadratic axis-gap bound gives a squared-width bound for the
normalized horizontal mean. -/
theorem abs_horizontalMean_le_square {a b A : ℝ}
    {k : ℝ × ℝ → ℝ} (hA : 0 ≤ A)
    (hk : ∀ q ∈ closedCoordTriangle a b,
      |k q| ≤ A * (q.2 - q.1) ^ 2)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |horizontalMean a k p| ≤ A * (b - a) ^ 2 := by
  have hT : 0 ≤ b - a :=
    sub_nonneg.mpr (hp.1.trans (hp.2.1.trans hp.2.2))
  apply abs_horizontalMean_le_const (mul_nonneg hA (sq_nonneg _)) ?_ hp
  intro q hq
  have hgap : q.2 - q.1 ≤ b - a := by linarith only [hq.1, hq.2.2]
  have hgap₀ : 0 ≤ q.2 - q.1 := sub_nonneg.mpr hq.2.1
  exact (hk q hq).trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ hgap₀ hT).2 hgap) hA)

/-- Evaluation commutes with the interval integral defining the horizontal
mean jet. -/
theorem horizontalMeanJet_apply {a b : ℝ}
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hG : ContinuousOn G (closedCoordTriangle a b))
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (e : ℝ × ℝ) :
    horizontalMeanJet a G p e =
      ∫ t in (0 : ℝ)..1,
        G (horizontalSegment a p t) (horizontalSegmentFDeriv t e) := by
  have hseg : Continuous (fun t : ℝ => horizontalSegment a p t) := by
    unfold horizontalSegment
    fun_prop
  have hGseg : ContinuousOn (fun t => G (horizontalSegment a p t))
      (Icc (0 : ℝ) 1) :=
    hG.comp hseg.continuousOn
      (fun t ht => horizontalSegment_mem_closedCoordTriangle hp ht)
  have hint : IntervalIntegrable
      (fun t : ℝ => (G (horizontalSegment a p t)).comp
        (horizontalSegmentFDeriv t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact hGseg.clm_comp continuous_horizontalSegmentFDeriv.continuousOn
  rw [horizontalMeanJet, ContinuousLinearMap.intervalIntegral_apply hint]
  rfl

/-- A uniform bound for the transformed integrand bounds any coordinate
component of the normalized horizontal mean jet. -/
theorem abs_horizontalMeanJet_apply_le_const {a b A : ℝ}
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hG : ContinuousOn G (closedCoordTriangle a b))
    (_hA : 0 ≤ A)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (e : ℝ × ℝ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      |G (horizontalSegment a p t) (horizontalSegmentFDeriv t e)| ≤ A) :
    |horizontalMeanJet a G p e| ≤ A := by
  rw [horizontalMeanJet_apply hG hp e]
  have hnorm : ∀ t ∈ Ι (0 : ℝ) 1,
      ‖G (horizontalSegment a p t) (horizontalSegmentFDeriv t e)‖ ≤ A := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact Ioc_subset_Icc_self ht
    simpa only [Real.norm_eq_abs] using hbound t htI
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := A)
    (f := fun t => G (horizontalSegment a p t)
      (horizontalSegmentFDeriv t e)) hnorm
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h

/-- Uniform bounds for both kernel coordinate derivatives pass unchanged
to the coordinate components of the normalized horizontal mean jet. -/
theorem abs_horizontalMeanJet_coordinate_le {a b A : ℝ}
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hG : ContinuousOn G (closedCoordTriangle a b)) (hA : 0 ≤ A)
    (hbound : ∀ q ∈ closedCoordTriangle a b,
      |G q (1, 0)| ≤ A ∧ |G q (0, 1)| ≤ A)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (i : Fin 2) :
    |horizontalMeanJet a G p (coordinateDirection i)| ≤ A := by
  fin_cases i
  · apply abs_horizontalMeanJet_apply_le_const hG hA hp (1, 0)
    intro t ht
    have hq := (hbound _ (horizontalSegment_mem_closedCoordTriangle hp ht)).1
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    rw [horizontalSegmentFDeriv_apply]
    simp only [mul_one]
    have heq : (t, (0 : ℝ)) = t • ((1 : ℝ), (0 : ℝ)) := by
      ext <;> simp
    rw [heq, map_smul, smul_eq_mul]
    rw [abs_mul, abs_of_nonneg ht0]
    calc
      t * |G (horizontalSegment a p t) (1, 0)| ≤ t * A :=
        mul_le_mul_of_nonneg_left hq ht0
      _ ≤ A := by nlinarith only [ht1, hA]
  · apply abs_horizontalMeanJet_apply_le_const hG hA hp (0, 1)
    intro t ht
    simpa only [horizontalSegmentFDeriv_apply, mul_zero, coordinateDirection,
      Fin.isValue, ↓reduceIte] using
      (hbound _ (horizontalSegment_mem_closedCoordTriangle hp ht)).2

end ChristodoulouBV.AxisPicard

end
