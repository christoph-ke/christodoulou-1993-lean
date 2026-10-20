module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Integral Gronwall inequalities

Lebesgue integral versions of Gronwall's inequality for interval integrable real functions.
The derivative-based bound `gronwallBound` in `Mathlib.Analysis.ODE.Gronwall` has different
hypotheses; the results here require no continuity of the function being bounded.
-/

public section

open MeasureTheory Set intervalIntegral

namespace intervalIntegral

/-- Integral Gronwall inequality with an integrable coefficient and integrable product. -/
theorem le_mul_exp_integral_of_le_integral {a b A : ℝ} {k h : ℝ → ℝ}
    (hab : a ≤ b) (hk : IntervalIntegrable k volume a b)
    (hkh : IntervalIntegrable (fun s => k s * h s) volume a b)
    (hk0 : ∀ s ∈ Icc a b, 0 ≤ k s)
    (hh : ∀ t ∈ Icc a b, h t ≤ A + ∫ s in a..t, k s * h s) :
    ∀ t ∈ Icc a b, h t ≤ A * Real.exp (∫ s in a..t, k s) := by
  let K : ℝ → ℝ := fun t => ∫ s in a..t, k s
  let U : ℝ → ℝ := fun t => A + ∫ s in a..t, k s * h s
  have hKac : AbsolutelyContinuousOnInterval K a b :=
    hk.absolutelyContinuousOnInterval_intervalIntegral (by simp [hab])
  have hUac : AbsolutelyContinuousOnInterval U a b := by
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => A) a b :=
      (LipschitzWith.const A).lipschitzOnWith.absolutelyContinuousOnInterval
    exact hc.add (hkh.absolutelyContinuousOnInterval_intervalIntegral (by simp [hab]))
  have hKrange : MapsTo K (Icc a b) (Icc 0 (K b)) := by
    intro t ht
    constructor
    · exact intervalIntegral.integral_nonneg ht.1 (fun s hs => hk0 s ⟨hs.1, hs.2.trans ht.2⟩)
    · exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall
          (fun s hs => hk0 s ⟨hs.1.le, hs.2⟩))) hk
  have hEac : AbsolutelyContinuousOnInterval (fun t => Real.exp (-K t)) a b := by
    have hsmooth : ContDiffOn ℝ 1 (fun y : ℝ => Real.exp (-y)) (Icc 0 (K b)) := by
      fun_prop
    obtain ⟨C, hC⟩ := hsmooth.exists_lipschitzOnWith (by norm_num)
      (convex_Icc _ _) isCompact_Icc
    simpa only [Function.comp_def] using
      hC.comp_absolutelyContinuousOnInterval (by simpa [uIcc_of_le hab] using hKrange) hKac
  have hGac : AbsolutelyContinuousOnInterval
      (fun t => U t * Real.exp (-K t)) a b := by
    exact hUac.mul hEac
  have hGderiv : ∀ᵐ t : ℝ, t ∈ Icc a b →
      deriv (fun x => U x * Real.exp (-K x)) t ≤ 0 := by
    filter_upwards [hk.ae_hasDerivAt_integral, hkh.ae_hasDerivAt_integral]
      with t htK htU ht
    have hKd : HasDerivAt K (k t) t := htK (by simpa [uIcc_of_le hab] using ht) a
      (by simp [hab])
    have hUd : HasDerivAt U (k t * h t) t := by
      exact (htU (by simpa [uIcc_of_le hab] using ht) a (by simp [hab])).const_add A
    have hEd : HasDerivAt (fun x => Real.exp (-K x))
        (Real.exp (-K t) * (-k t)) t := hKd.neg.exp
    have hGd := hUd.mul hEd
    change deriv (U * fun x => Real.exp (-K x)) t ≤ 0
    rw [hGd.deriv]
    have hh' : h t ≤ U t := hh t ht
    have hprod : k t * h t ≤ k t * U t := mul_le_mul_of_nonneg_left hh' (hk0 t ht)
    nlinarith [Real.exp_pos (-K t)]
  intro t ht
  have hGle : U t * Real.exp (-K t) ≤ A := by
    have hderiv_nonpos : ∫ x in a..t, deriv (fun x => U x * Real.exp (-K x)) x ≤ 0 := by
      have hsub : AbsolutelyContinuousOnInterval
          (fun x => U x * Real.exp (-K x)) a t := hGac.mono (by
        rw [uIcc_of_le ht.1, uIcc_of_le hab]
        exact Icc_subset_Icc_right ht.2)
      have hi := intervalIntegral.integral_mono_ae_restrict ht.1
        hsub.intervalIntegrable_deriv (intervalIntegrable_const (c := (0 : ℝ)))
        ((ae_restrict_iff' measurableSet_Icc).2 (hGderiv.mono fun x hx hxt =>
          hx ⟨hxt.1, hxt.2.trans ht.2⟩))
      simpa only [intervalIntegral.integral_zero] using hi
    have hFTC := (hGac.mono (c := a) (d := t) (by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc_right ht.2)).integral_deriv_eq_sub
    have hUa : U a = A := by simp [U]
    have hKa : K a = 0 := by simp [K]
    rw [hUa, hKa] at hFTC
    simp only [neg_zero, Real.exp_zero, mul_one] at hFTC
    linarith
  have hbound : U t ≤ A * Real.exp (K t) := by
    have hpos := Real.exp_pos (K t)
    rw [Real.exp_neg] at hGle
    exact (mul_inv_le_iff₀ hpos).mp hGle
  exact (hh t ht).trans hbound

/-- Integral Gronwall inequality with a nondecreasing time dependent source bound. -/
theorem le_mul_exp_integral_of_le_integral_mono {a b : ℝ} {A k h : ℝ → ℝ}
    (hab : a ≤ b) (hA : MonotoneOn A (Icc a b))
    (hk : IntervalIntegrable k volume a b)
    (hkh : IntervalIntegrable (fun s => k s * h s) volume a b)
    (hk0 : ∀ s ∈ Icc a b, 0 ≤ k s)
    (hh : ∀ t ∈ Icc a b, h t ≤ A t + ∫ s in a..t, k s * h s) :
    ∀ t ∈ Icc a b, h t ≤ A t * Real.exp (∫ s in a..t, k s) := by
  intro t ht
  have hsub : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    exact Icc_subset_Icc_right ht.2
  exact le_mul_exp_integral_of_le_integral ht.1 (hk.mono_set hsub)
    (hkh.mono_set hsub) (fun s hs => hk0 s ⟨hs.1, hs.2.trans ht.2⟩)
    (fun s hs => (hh s ⟨hs.1, hs.2.trans ht.2⟩).trans
      (add_le_add_left (hA ⟨hs.1, hs.2.trans ht.2⟩ ht hs.2) _)) t
    ⟨ht.1, le_rfl⟩

/-- Backward integral Gronwall inequality, with integration from the current point to `b`. -/
theorem le_mul_exp_integral_of_le_integral_backward {a b A : ℝ} {k h : ℝ → ℝ}
    (hab : a ≤ b) (hk : IntervalIntegrable k volume a b)
    (hkh : IntervalIntegrable (fun s => k s * h s) volume a b)
    (hk0 : ∀ s ∈ Icc a b, 0 ≤ k s)
    (hh : ∀ t ∈ Icc a b, h t ≤ A + ∫ s in t..b, k s * h s) :
    ∀ t ∈ Icc a b, h t ≤ A * Real.exp (∫ s in t..b, k s) := by
  have hk' : IntervalIntegrable (fun s => k (-s)) volume (-b) (-a) :=
    (IntervalIntegrable.iff_comp_neg (a := b) (b := a)).mp hk.symm
  have hkh' : IntervalIntegrable (fun s => k (-s) * h (-s)) volume (-b) (-a) :=
    (IntervalIntegrable.iff_comp_neg (a := b) (b := a)).mp hkh.symm
  have H := le_mul_exp_integral_of_le_integral (a := -b) (b := -a)
    (A := A) (k := fun s => k (-s)) (h := fun s => h (-s))
    (neg_le_neg hab) hk' hkh'
    (fun s hs => hk0 (-s) (by constructor <;> linarith [hs.1, hs.2]))
    (fun s hs => by
      have hs' : -s ∈ Icc a b := by constructor <;> linarith [hs.1, hs.2]
      change h (-s) ≤ A + ∫ x in -b..s, (fun y => k y * h y) (-x)
      rw [intervalIntegral.integral_comp_neg (fun y => k y * h y)]
      simpa only [neg_neg] using hh (-s) hs')
  intro t ht
  have ht' : -t ∈ Icc (-b) (-a) := by constructor <;> linarith [ht.1, ht.2]
  simpa only [intervalIntegral.integral_comp_neg, neg_neg] using H (-t) ht'

/-- Integral Gronwall inequality when the integral term is multiplied by a nonnegative constant. -/
theorem le_mul_exp_integral_of_le_integral_const_mul {a b A B : ℝ} {k h : ℝ → ℝ}
    (hab : a ≤ b) (hB : 0 ≤ B) (hk : IntervalIntegrable k volume a b)
    (hkh : IntervalIntegrable (fun s => k s * h s) volume a b)
    (hk0 : ∀ s ∈ Icc a b, 0 ≤ k s)
    (hh : ∀ t ∈ Icc a b, h t ≤ A + B * ∫ s in a..t, k s * h s) :
    ∀ t ∈ Icc a b, h t ≤ A * Real.exp (B * ∫ s in a..t, k s) := by
  have hk' : IntervalIntegrable (fun s => B * k s) volume a b := hk.const_mul B
  have hkh' : IntervalIntegrable (fun s => (B * k s) * h s) volume a b := by
    simpa only [mul_assoc] using hkh.const_mul B
  have H := le_mul_exp_integral_of_le_integral (a := a) (b := b)
    (A := A) (k := fun s => B * k s) (h := h) hab hk' hkh'
    (fun s hs => mul_nonneg hB (hk0 s hs))
    (fun t ht => by
      simpa only [mul_assoc, intervalIntegral.integral_const_mul] using hh t ht)
  intro t ht
  simpa only [intervalIntegral.integral_const_mul] using H t ht

end intervalIntegral
