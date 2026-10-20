module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMeanHorizontalDifference
import Mathlib.Tactic

/-!
# Algebraic bounds for normalized endpoint numerators

The results here isolate the real-variable estimates in the horizontal
derivative of a positive weighted average.
-/

public section

open Set MeasureTheory
open scoped Interval

namespace intervalIntegral

/-- The numerator formed by a left endpoint contribution and a normalized
integral of two products. -/
@[expose] noncomputable def weightedEndpointNumerator
    (a e d : ℝ) (X Z W Y : ℝ → ℝ) : ℝ :=
  a * e / d + ∫ t in (0 : ℝ)..1, X t * Z t + W t * Y t

/-- The endpoint numerator has the sharp coarse unit-interval bound used
when each factor is controlled separately. -/
theorem abs_weightedEndpointNumerator_le
    {a e d B C L : ℝ} {X Z W Y : ℝ → ℝ}
    (hd : 0 < d) (hdle : d ≤ 1) (hB : 0 ≤ B) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (ha : |a| ≤ C) (he : |e| ≤ B * d)
    (hX : ∀ t ∈ Icc (0 : ℝ) 1, |X t| ≤ L)
    (hZ : ∀ t ∈ Icc (0 : ℝ) 1, |Z t| ≤ B * d)
    (hW : ∀ t ∈ Icc (0 : ℝ) 1, |W t| ≤ C)
    (hY : ∀ t ∈ Icc (0 : ℝ) 1, |Y t| ≤ L) :
    |weightedEndpointNumerator a e d X Z W Y| ≤ C * B + L * B + C * L := by
  have hend : |a * e / d| ≤ C * B := by
    rw [abs_div, abs_mul, abs_of_pos hd]
    have hnum := mul_le_mul ha he (abs_nonneg _) hC
    have hnum' : |a| * |e| ≤ C * B * d := by
      calc
        _ ≤ C * (B * d) := hnum
        _ = C * B * d := by ring
    exact (div_le_iff₀ hd).2 (by nlinarith [hnum'])
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      |X t * Z t + W t * Y t| ≤ L * B * d + C * L := by
    intro t ht
    have hfirst : |X t * Z t| ≤ L * (B * d) := by
      rw [abs_mul]
      exact mul_le_mul (hX t ht) (hZ t ht) (abs_nonneg _) hL
    have hsecond : |W t * Y t| ≤ C * L := by
      rw [abs_mul]
      exact mul_le_mul (hW t ht) (hY t ht) (abs_nonneg _) hC
    calc
      _ ≤ |X t * Z t| + |W t * Y t| := abs_add_le _ _
      _ ≤ L * (B * d) + C * L := add_le_add hfirst hsecond
      _ = L * B * d + C * L := by ring
  have hI : |∫ t in (0 : ℝ)..1, X t * Z t + W t * Y t| ≤
      L * B * d + C * L := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := L * B * d + C * L)
      (f := fun t => X t * Z t + W t * Y t) (fun t ht => by
        have ht' : t ∈ Icc (0 : ℝ) 1 := by
          rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
          exact ⟨ht.1.le, ht.2⟩
        simpa only [Real.norm_eq_abs] using hpoint t ht')
    simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h
  change |a * e / d + ∫ t in (0 : ℝ)..1, X t * Z t + W t * Y t| ≤ _
  calc
    _ ≤ |a * e / d| + |∫ t in (0 : ℝ)..1, X t * Z t + W t * Y t| :=
      abs_add_le _ _
    _ ≤ C * B + (L * B * d + C * L) := add_le_add hend hI
    _ ≤ C * B + L * B + C * L := by
      nlinarith [mul_le_mul_of_nonneg_left hdle (mul_nonneg hL hB)]

/-- Two endpoint numerators obey the exact three-part difference coefficient:
endpoint, derivative of the weight, and derivative of the averaged function. -/
theorem abs_weightedEndpointNumerator_sub_le
    {a₁ a₂ e₁ e₂ d B C L M D : ℝ}
    {X₁ X₂ Z₁ Z₂ W₁ W₂ Y₁ Y₂ : ℝ → ℝ}
    (hd : 0 < d) (hdle : d ≤ 1)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hM : 0 ≤ M) (hD : 0 ≤ D)
    (ha₂ : |a₂| ≤ C) (haDiff : |a₁ - a₂| ≤ D)
    (he₁ : |e₁| ≤ B * d)
    (heDiff : |e₁ - e₂| ≤ M * d * D)
    (hX₂ : ∀ t ∈ Icc (0 : ℝ) 1, |X₂ t| ≤ L)
    (hXDiff : ∀ t ∈ Icc (0 : ℝ) 1, |X₁ t - X₂ t| ≤ D)
    (hZ₁ : ∀ t ∈ Icc (0 : ℝ) 1, |Z₁ t| ≤ B * d)
    (hZDiff : ∀ t ∈ Icc (0 : ℝ) 1,
      |Z₁ t - Z₂ t| ≤ (1 + M) * d * D)
    (hW₂ : ∀ t ∈ Icc (0 : ℝ) 1, |W₂ t| ≤ C)
    (hWDiff : ∀ t ∈ Icc (0 : ℝ) 1, |W₁ t - W₂ t| ≤ D)
    (hY₁ : ∀ t ∈ Icc (0 : ℝ) 1, |Y₁ t| ≤ L)
    (hYDiff : ∀ t ∈ Icc (0 : ℝ) 1, |Y₁ t - Y₂ t| ≤ D)
    (hI₁ : IntervalIntegrable
      (fun t => X₁ t * Z₁ t + W₁ t * Y₁ t) volume 0 1)
    (hI₂ : IntervalIntegrable
      (fun t => X₂ t * Z₂ t + W₂ t * Y₂ t) volume 0 1) :
    |weightedEndpointNumerator a₁ e₁ d X₁ Z₁ W₁ Y₁ -
      weightedEndpointNumerator a₂ e₂ d X₂ Z₂ W₂ Y₂| ≤
      (B + C * M + B + L * (1 + M) + L + C) * D := by
  have hend : |a₁ * e₁ / d - a₂ * e₂ / d| ≤ (B + C * M) * D := by
    have hident : a₁ * e₁ / d - a₂ * e₂ / d =
        ((a₁ - a₂) * e₁ + a₂ * (e₁ - e₂)) / d := by ring
    rw [hident, abs_div, abs_of_pos hd]
    have hfirst : |(a₁ - a₂) * e₁| ≤ D * (B * d) := by
      rw [abs_mul]
      exact mul_le_mul haDiff he₁ (abs_nonneg _) hD
    have hsecond : |a₂ * (e₁ - e₂)| ≤ C * (M * d * D) := by
      rw [abs_mul]
      exact mul_le_mul ha₂ heDiff (abs_nonneg _) hC
    have hnum : |(a₁ - a₂) * e₁ + a₂ * (e₁ - e₂)| ≤
        (B + C * M) * D * d := by
      calc
        _ ≤ |(a₁ - a₂) * e₁| + |a₂ * (e₁ - e₂)| := abs_add_le _ _
        _ ≤ D * (B * d) + C * (M * d * D) := add_le_add hfirst hsecond
        _ = (B + C * M) * D * d := by ring
    exact (div_le_iff₀ hd).2 (by nlinarith [hnum])
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      |(X₁ t * Z₁ t + W₁ t * Y₁ t) -
        (X₂ t * Z₂ t + W₂ t * Y₂ t)| ≤
      (B + L * (1 + M)) * d * D + (L + C) * D := by
    intro t ht
    have hfirst : |X₁ t * Z₁ t - X₂ t * Z₂ t| ≤
        (B + L * (1 + M)) * d * D := by
      have hid : X₁ t * Z₁ t - X₂ t * Z₂ t =
          (X₁ t - X₂ t) * Z₁ t + X₂ t * (Z₁ t - Z₂ t) := by ring
      rw [hid]
      calc
        _ ≤ |(X₁ t - X₂ t) * Z₁ t| + |X₂ t * (Z₁ t - Z₂ t)| :=
          abs_add_le _ _
        _ ≤ D * (B * d) + L * ((1 + M) * d * D) := by
          rw [abs_mul, abs_mul]
          exact add_le_add
            (mul_le_mul (hXDiff t ht) (hZ₁ t ht) (abs_nonneg _) hD)
            (mul_le_mul (hX₂ t ht) (hZDiff t ht) (abs_nonneg _) hL)
        _ = (B + L * (1 + M)) * d * D := by ring
    have hsecond : |W₁ t * Y₁ t - W₂ t * Y₂ t| ≤ (L + C) * D := by
      have hid : W₁ t * Y₁ t - W₂ t * Y₂ t =
          (W₁ t - W₂ t) * Y₁ t + W₂ t * (Y₁ t - Y₂ t) := by ring
      rw [hid]
      calc
        _ ≤ |(W₁ t - W₂ t) * Y₁ t| + |W₂ t * (Y₁ t - Y₂ t)| :=
          abs_add_le _ _
        _ ≤ D * L + C * D := by
          rw [abs_mul, abs_mul]
          exact add_le_add
            (mul_le_mul (hWDiff t ht) (hY₁ t ht) (abs_nonneg _) hD)
            (mul_le_mul (hW₂ t ht) (hYDiff t ht) (abs_nonneg _) hC)
        _ = (L + C) * D := by ring
    have hid : (X₁ t * Z₁ t + W₁ t * Y₁ t) -
        (X₂ t * Z₂ t + W₂ t * Y₂ t) =
        (X₁ t * Z₁ t - X₂ t * Z₂ t) +
          (W₁ t * Y₁ t - W₂ t * Y₂ t) := by ring
    rw [hid]
    exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)
  have hI : |(∫ t in (0 : ℝ)..1, X₁ t * Z₁ t + W₁ t * Y₁ t) -
      (∫ t in (0 : ℝ)..1, X₂ t * Z₂ t + W₂ t * Y₂ t)| ≤
      (B + L * (1 + M)) * d * D + (L + C) * D := by
    rw [← intervalIntegral.integral_sub hI₁ hI₂]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1)
      (C := (B + L * (1 + M)) * d * D + (L + C) * D)
      (f := fun t => (X₁ t * Z₁ t + W₁ t * Y₁ t) -
        (X₂ t * Z₂ t + W₂ t * Y₂ t)) (fun t ht => by
          have ht' : t ∈ Icc (0 : ℝ) 1 := by
            rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
            exact ⟨ht.1.le, ht.2⟩
          simpa only [Real.norm_eq_abs] using hpoint t ht')
    simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h
  change |(a₁ * e₁ / d + ∫ t in (0 : ℝ)..1, X₁ t * Z₁ t + W₁ t * Y₁ t) -
    (a₂ * e₂ / d + ∫ t in (0 : ℝ)..1, X₂ t * Z₂ t + W₂ t * Y₂ t)| ≤ _
  have hid : (a₁ * e₁ / d + ∫ t in (0 : ℝ)..1, X₁ t * Z₁ t + W₁ t * Y₁ t) -
      (a₂ * e₂ / d + ∫ t in (0 : ℝ)..1, X₂ t * Z₂ t + W₂ t * Y₂ t) =
      (a₁ * e₁ / d - a₂ * e₂ / d) +
        ((∫ t in (0 : ℝ)..1, X₁ t * Z₁ t + W₁ t * Y₁ t) -
          (∫ t in (0 : ℝ)..1, X₂ t * Z₂ t + W₂ t * Y₂ t)) := by ring
  rw [hid]
  calc
    _ ≤ |a₁ * e₁ / d - a₂ * e₂ / d| +
        |(∫ t in (0 : ℝ)..1, X₁ t * Z₁ t + W₁ t * Y₁ t) -
          (∫ t in (0 : ℝ)..1, X₂ t * Z₂ t + W₂ t * Y₂ t)| := abs_add_le _ _
    _ ≤ (B + C * M) * D +
        ((B + L * (1 + M)) * d * D + (L + C) * D) := add_le_add hend hI
    _ ≤ (B + C * M + B + L * (1 + M) + L + C) * D := by
      have hcoef : 0 ≤ B + L * (1 + M) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hdle (mul_nonneg hcoef hD)]

end intervalIntegral

end
