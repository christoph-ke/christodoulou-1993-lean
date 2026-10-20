module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointInvariant
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Differences of horizontal Picard primitives

The normalized fixed-interval representation transfers two-input value and
coordinate derivative bounds to differences of horizontal primitive jets.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.AxisPicard

/-- The difference of two normalized horizontal means is the normalized
mean of the difference. -/
theorem horizontalMean_sub_eq {a b : ℝ} {k₁ k₂ : ℝ × ℝ → ℝ}
    (hk₁ : ContinuousOn k₁ (closedCoordTriangle a b))
    (hk₂ : ContinuousOn k₂ (closedCoordTriangle a b))
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    horizontalMean a k₁ p - horizontalMean a k₂ p =
      horizontalMean a (k₁ - k₂) p := by
  have hint (k : ℝ × ℝ → ℝ)
      (hk : ContinuousOn k (closedCoordTriangle a b)) :
      IntervalIntegrable (fun t => k (horizontalSegment a p t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    have hseg : Continuous (fun t : ℝ => horizontalSegment a p t) := by
      unfold horizontalSegment
      fun_prop
    exact hk.comp hseg.continuousOn
      (fun t ht => horizontalSegment_mem_closedCoordTriangle hp ht)
  simp only [horizontalMean]
  rw [← intervalIntegral.integral_sub (hint k₁ hk₁) (hint k₂ hk₂)]
  rfl

/-- The coordinate component of the difference of two normalized
horizontal mean jets is the component of the mean jet of the difference. -/
theorem horizontalMeanJet_sub_apply_eq {a b : ℝ}
    {G₁ G₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hG₁ : ContinuousOn G₁ (closedCoordTriangle a b))
    (hG₂ : ContinuousOn G₂ (closedCoordTriangle a b))
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (e : ℝ × ℝ) :
    horizontalMeanJet a G₁ p e - horizontalMeanJet a G₂ p e =
      horizontalMeanJet a (G₁ - G₂) p e := by
  have hint (G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ)
      (hG : ContinuousOn G (closedCoordTriangle a b)) :
      IntervalIntegrable (fun t =>
        G (horizontalSegment a p t) (horizontalSegmentFDeriv t e))
        volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    have hseg : Continuous (fun t : ℝ => horizontalSegment a p t) := by
      unfold horizontalSegment
      fun_prop
    have hGseg : ContinuousOn (fun t => G (horizontalSegment a p t))
        (Icc (0 : ℝ) 1) :=
      hG.comp hseg.continuousOn
        (fun t ht => horizontalSegment_mem_closedCoordTriangle hp ht)
    exact hGseg.clm_apply
      (continuous_horizontalSegmentFDeriv.comp continuous_id |>.clm_apply
        continuous_const).continuousOn
  rw [horizontalMeanJet_apply hG₁ hp e,
    horizontalMeanJet_apply hG₂ hp e,
    horizontalMeanJet_apply (hG₁.sub hG₂) hp e]
  rw [← intervalIntegral.integral_sub (hint G₁ hG₁) (hint G₂ hG₂)]
  rfl

/-- Pointwise value-difference bounds pass to normalized horizontal means. -/
theorem abs_horizontalMean_sub_le_const {a b A : ℝ}
    {k₁ k₂ : ℝ × ℝ → ℝ}
    (hk₁ : ContinuousOn k₁ (closedCoordTriangle a b))
    (hk₂ : ContinuousOn k₂ (closedCoordTriangle a b))
    (hA : 0 ≤ A)
    (hbound : ∀ q ∈ closedCoordTriangle a b, |k₁ q - k₂ q| ≤ A)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |horizontalMean a k₁ p - horizontalMean a k₂ p| ≤ A := by
  rw [horizontalMean_sub_eq hk₁ hk₂ hp]
  apply abs_horizontalMean_le_const hA ?_ hp
  intro q hq
  exact hbound q hq

/-- Pointwise coordinate derivative-difference bounds pass to normalized
horizontal mean jets. -/
theorem abs_horizontalMeanJet_sub_coordinate_le {a b A : ℝ}
    {G₁ G₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hG₁ : ContinuousOn G₁ (closedCoordTriangle a b))
    (hG₂ : ContinuousOn G₂ (closedCoordTriangle a b))
    (hA : 0 ≤ A)
    (hbound : ∀ q ∈ closedCoordTriangle a b,
      |G₁ q (1, 0) - G₂ q (1, 0)| ≤ A ∧
      |G₁ q (0, 1) - G₂ q (0, 1)| ≤ A)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (i : Fin 2) :
    |horizontalMeanJet a G₁ p (coordinateDirection i) -
      horizontalMeanJet a G₂ p (coordinateDirection i)| ≤ A := by
  rw [horizontalMeanJet_sub_apply_eq hG₁ hG₂ hp]
  apply abs_horizontalMeanJet_coordinate_le (hG₁.sub hG₂) hA ?_ hp i
  intro q hq
  simpa only [Pi.sub_apply, sub_apply] using hbound q hq

/-- Differences of horizontal primitive jets are controlled by the
normalized mean and mean-jet differences. -/
theorem abs_horizontalIntegralJet_sub_coordinate_le {a b A B : ℝ}
    {k₁ k₂ : ℝ × ℝ → ℝ}
    {G₁ G₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hmean : |horizontalMean a k₁ p - horizontalMean a k₂ p| ≤ A)
    (hjet : ∀ i : Fin 2,
      |horizontalMeanJet a G₁ p (coordinateDirection i) -
        horizontalMeanJet a G₂ p (coordinateDirection i)| ≤ B)
    (i : Fin 2) :
    |horizontalIntegralJet a k₁ G₁ p (coordinateDirection i) -
      horizontalIntegralJet a k₂ G₂ p (coordinateDirection i)| ≤
      A + B * (b - a) := by
  have hspan0 : 0 ≤ p.1 - a := sub_nonneg.mpr hp.1
  have hspan : p.1 - a ≤ b - a := by linarith only [hp.2.1, hp.2.2]
  have he : |(coordinateDirection i).1| ≤ (1 : ℝ) := by
    fin_cases i <;> norm_num [coordinateDirection]
  have hprod : |p.1 - a| *
      |horizontalMeanJet a G₁ p (coordinateDirection i) -
        horizontalMeanJet a G₂ p (coordinateDirection i)| ≤ B * (b - a) := by
    rw [abs_of_nonneg hspan0]
    calc
      _ ≤ (p.1 - a) * B := mul_le_mul_of_nonneg_left (hjet i) hspan0
      _ ≤ B * (b - a) := by nlinarith only [hspan, hB]
  have hmeanprod : |horizontalMean a k₁ p - horizontalMean a k₂ p| *
      |(coordinateDirection i).1| ≤ A := by
    calc
      _ ≤ A * |(coordinateDirection i).1| :=
        mul_le_mul_of_nonneg_right hmean (abs_nonneg _)
      _ ≤ A := by nlinarith only [he, hA]
  simp only [horizontalIntegralJet, add_apply, smul_apply, smul_eq_mul]
  have hfst : (ContinuousLinearMap.fst ℝ ℝ ℝ)
      (coordinateDirection i) = (coordinateDirection i).1 := rfl
  rw [hfst]
  have heq : ((p.1 - a) * horizontalMeanJet a G₁ p (coordinateDirection i) +
      horizontalMean a k₁ p * (coordinateDirection i).1) -
      ((p.1 - a) * horizontalMeanJet a G₂ p (coordinateDirection i) +
        horizontalMean a k₂ p * (coordinateDirection i).1) =
      (p.1 - a) * (horizontalMeanJet a G₁ p (coordinateDirection i) -
        horizontalMeanJet a G₂ p (coordinateDirection i)) +
        (horizontalMean a k₁ p - horizontalMean a k₂ p) *
          (coordinateDirection i).1 := by ring
  rw [heq]
  have htri := abs_add_le
    ((p.1 - a) * (horizontalMeanJet a G₁ p (coordinateDirection i) -
      horizontalMeanJet a G₂ p (coordinateDirection i)))
    ((horizontalMean a k₁ p - horizontalMean a k₂ p) *
      (coordinateDirection i).1)
  rw [abs_mul, abs_mul] at htri
  linarith only [htri, hprod, hmeanprod]

end ChristodoulouBV.AxisPicard

end
