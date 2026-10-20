module

public import ChristodoulouBV.ForMathlib.AbsolutelyContinuous.Calculus

/-!
# Interval primitives on a compact interval

These lemmas unpack a subinterval increment identity into absolute continuity and
almost-everywhere calculus rules.
-/

public section

open Set MeasureTheory

namespace AbsolutelyContinuousOnInterval

/-- An interval-integrable density giving every ordered increment on `[a,b]` makes its
primitive absolutely continuous. -/
theorem of_integral_eq_sub_of_le {F g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ∀ x y, a ≤ x → x ≤ y → y ≤ b → IntervalIntegrable g volume x y)
    (hF : ∀ x y, a ≤ x → x ≤ y → y ≤ b →
      F y - F x = ∫ t in x..y, g t) :
    AbsolutelyContinuousOnInterval F a b := by
  apply of_integral_eq_sub (hg a b le_rfl hab le_rfl)
  intro t ht
  rw [uIcc_of_le hab] at ht
  exact hF a t le_rfl ht.1 ht.2

/-- The derivative of an interval primitive agrees almost everywhere with its density. -/
theorem ae_deriv_eq_of_integral_eq_sub_of_le {F g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hg : ∀ x y, a ≤ x → x ≤ y → y ≤ b → IntervalIntegrable g volume x y)
    (hF : ∀ x y, a ≤ x → x ≤ y → y ≤ b →
      F y - F x = ∫ t in x..y, g t) :
    ∀ᵐ t ∂volume, t ∈ Icc a b → deriv F t = g t := by
  have h := ae_deriv_eq_of_integral_eq_sub (hg a b le_rfl hab le_rfl)
    (fun t ht => by
      rw [uIcc_of_le hab] at ht
      exact hF a t le_rfl ht.1 ht.2)
  simpa only [uIcc_of_le hab] using h

/-- Two densities of the same interval primitive agree almost everywhere. -/
theorem ae_eq_of_same_integral_increments {F g h : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hg : ∀ x y, a ≤ x → x ≤ y → y ≤ b → IntervalIntegrable g volume x y)
    (hh : ∀ x y, a ≤ x → x ≤ y → y ≤ b → IntervalIntegrable h volume x y)
    (hFg : ∀ x y, a ≤ x → x ≤ y → y ≤ b →
      F y - F x = ∫ t in x..y, g t)
    (hFh : ∀ x y, a ≤ x → x ≤ y → y ≤ b →
      F y - F x = ∫ t in x..y, h t) :
    ∀ᵐ t ∂volume, t ∈ Icc a b → g t = h t := by
  have H := ae_eq_of_integral_eq_sub (hg a b le_rfl hab le_rfl)
    (hh a b le_rfl hab le_rfl)
    (fun t ht => by rw [uIcc_of_le hab] at ht; exact hFg a t le_rfl ht.1 ht.2)
    (fun t ht => by rw [uIcc_of_le hab] at ht; exact hFh a t le_rfl ht.1 ht.2)
  simpa only [uIcc_of_le hab] using H

/-- Product rule almost everywhere for functions specified by subinterval increments. -/
theorem ae_deriv_mul_of_integral_eq_sub_of_le {F G f g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ∀ x y, a ≤ x → x ≤ y → y ≤ b → IntervalIntegrable f volume x y)
    (hg : ∀ x y, a ≤ x → x ≤ y → y ≤ b → IntervalIntegrable g volume x y)
    (hF : ∀ x y, a ≤ x → x ≤ y → y ≤ b →
      F y - F x = ∫ t in x..y, f t)
    (hG : ∀ x y, a ≤ x → x ≤ y → y ≤ b →
      G y - G x = ∫ t in x..y, g t) :
    AbsolutelyContinuousOnInterval (fun t => F t * G t) a b ∧
      ∀ᵐ t ∂volume, t ∈ Icc a b →
        deriv (fun x => F x * G x) t = f t * G t + F t * g t := by
  have hFac := of_integral_eq_sub_of_le hab hf hF
  have hGac := of_integral_eq_sub_of_le hab hg hG
  refine ⟨by simpa only [Pi.mul_apply] using hFac.fun_mul hGac, ?_⟩
  filter_upwards [hFac.ae_deriv_mul hGac,
    ae_deriv_eq_of_integral_eq_sub_of_le hab hf hF,
    ae_deriv_eq_of_integral_eq_sub_of_le hab hg hG] with t hmul hdf hdg ht
  rw [uIcc_of_le hab] at hmul
  rw [hmul ht, hdf ht, hdg ht]

/-- Quotient rule almost everywhere for interval primitives with a denominator bounded
away from zero. -/
theorem ae_deriv_div_of_integral_eq_sub_of_le {F G f g : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 < c) (hGc : ∀ t ∈ Icc a b, c ≤ |G t|)
    (hf : ∀ x y, a ≤ x → x ≤ y → y ≤ b → IntervalIntegrable f volume x y)
    (hg : ∀ x y, a ≤ x → x ≤ y → y ≤ b → IntervalIntegrable g volume x y)
    (hF : ∀ x y, a ≤ x → x ≤ y → y ≤ b →
      F y - F x = ∫ t in x..y, f t)
    (hG : ∀ x y, a ≤ x → x ≤ y → y ≤ b →
      G y - G x = ∫ t in x..y, g t) :
    AbsolutelyContinuousOnInterval (fun t => F t / G t) a b ∧
      ∀ᵐ t ∂volume, t ∈ Icc a b →
        deriv (fun x => F x / G x) t =
          (f t * G t - F t * g t) / (G t) ^ 2 := by
  have hFac := of_integral_eq_sub_of_le hab hf hF
  have hGac := of_integral_eq_sub_of_le hab hg hG
  obtain ⟨hQ, hderiv⟩ := hFac.div_and_ae_deriv hGac hc (by
    simpa only [uIcc_of_le hab] using hGc)
  refine ⟨hQ, ?_⟩
  filter_upwards [hderiv,
    ae_deriv_eq_of_integral_eq_sub_of_le hab hf hF,
    ae_deriv_eq_of_integral_eq_sub_of_le hab hg hG] with t hdiv hdf hdg ht
  rw [uIcc_of_le hab] at hdiv
  rw [hdiv ht, hdf ht, hdg ht]

end AbsolutelyContinuousOnInterval

end
