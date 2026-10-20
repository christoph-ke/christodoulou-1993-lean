module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Linear integral equations on a real interval

Variation of constants for scalar equations with interval-integrable coefficients.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace AbsolutelyContinuousOnInterval

/-- The exponential of a real absolutely continuous function is absolutely continuous
on the same interval. -/
theorem exp {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ Real.exp (f x)) a b := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  have hmap : MapsTo f (uIcc a b) (Icc (-C) C) := by
    intro x hx
    have := hC x hx
    simp only [Real.norm_eq_abs, abs_le] at this
    exact this
  obtain ⟨L, hL⟩ :=
    (Real.contDiff_exp (n := 1)).contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_Icc _ _) isCompact_Icc
  exact hL.comp_absolutelyContinuousOnInterval hmap hf

end AbsolutelyContinuousOnInterval

namespace intervalIntegral

/-- The fundamental theorem of calculus with an almost-everywhere specified derivative. -/
theorem integral_eq_sub_of_ae_hasDerivAt {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hderiv : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (f' x) x) :
    ∫ x in a..b, f' x = f b - f a := by
  rw [← hf.integral_deriv_eq_sub]
  apply integral_congr_ae
  filter_upwards [hderiv] with x hx hmem
  exact (hx (uIoc_subset_uIcc hmem)).deriv.symm

end intervalIntegral

namespace intervalIntegral

/-- Variation of constants for an absolutely continuous solution of a scalar linear ODE
with interval-integrable coefficients. -/
theorem eq_exp_mul_add_integral_of_ae_hasDerivAt
    {a b : ℝ} (hab : a ≤ b) {k g y : ℝ → ℝ}
    (hk : IntervalIntegrable k volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hy : AbsolutelyContinuousOnInterval y a b)
    (hy' : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt y (k x * y x + g x) x)
    {t : ℝ} (ht : t ∈ Icc a b) :
    y t = Real.exp (∫ s in a..t, k s) *
      (y a + ∫ s in a..t, Real.exp (-(∫ σ in a..s, k σ)) * g s) := by
  let K (x : ℝ) := ∫ s in a..x, k s
  let E (x : ℝ) := Real.exp (-K x)
  have hK : AbsolutelyContinuousOnInterval K a b :=
    hk.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hE : AbsolutelyContinuousOnInterval E a b := hK.neg.exp
  have hEg : IntervalIntegrable (fun x ↦ E x * g x) volume a b :=
    hg.continuousOn_mul hE.continuousOn
  have hEK : ∀ᵐ x, x ∈ uIcc a b →
      HasDerivAt E (-E x * k x) x := by
    filter_upwards [hk.ae_hasDerivAt_integral] with x hx hmem
    have hKx : HasDerivAt K (k x) x := hx hmem a (by simp)
    simpa only [E, Pi.neg_apply, neg_mul, mul_neg, Function.comp_def] using hKx.neg.exp
  have hprod : ∀ᵐ x, x ∈ uIcc a b →
      HasDerivAt (fun x ↦ E x * y x) (E x * g x) x := by
    filter_upwards [hEK, hy'] with x hEx hyx hmem
    convert (hEx hmem).mul (hyx hmem) using 1; ring
  have hprodAC := hE.mul hy
  have hint : ∫ s in a..t, E s * g s = E t * y t - E a * y a := by
    exact integral_eq_sub_of_ae_hasDerivAt (hprodAC.mono (by
      rw [uIcc_of_le hab, uIcc_of_le ht.1]
      exact Icc_subset_Icc_right ht.2)) (by
      filter_upwards [hprod] with x hx hmem
      exact hx (by
        rw [uIcc_of_le ht.1] at hmem
        rw [uIcc_of_le hab]
        exact ⟨hmem.1, hmem.2.trans ht.2⟩))
  have hKa : K a = 0 := by simp [K]
  have hEa : E a = 1 := by simp [E, hKa]
  have hEt : E t * Real.exp (K t) = 1 := by
    simp [E, ← Real.exp_add]
  rw [hEa, one_mul] at hint
  calc
    y t = Real.exp (K t) * (E t * y t) := by
      rw [← mul_assoc, mul_comm (Real.exp (K t)) (E t), hEt, one_mul]
    _ = Real.exp (K t) * (y a + ∫ s in a..t, E s * g s) := by rw [hint]; ring

end intervalIntegral

namespace intervalIntegral

/-- A scalar linear integral equation has the variation of constants representation. -/
theorem eq_exp_mul_add_integral_of_integral_eq
    {a b : ℝ} (hab : a ≤ b) {k g y : ℝ → ℝ}
    (hk : IntervalIntegrable k volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hky : IntervalIntegrable (fun s ↦ k s * y s) volume a b)
    (hy : ∀ t ∈ Icc a b,
      y t - y a = ∫ s in a..t, (k s * y s + g s))
    {t : ℝ} (ht : t ∈ Icc a b) :
    y t = Real.exp (∫ s in a..t, k s) *
      (y a + ∫ s in a..t, Real.exp (-(∫ σ in a..s, k σ)) * g s) := by
  let q (s : ℝ) := k s * y s + g s
  let F (x : ℝ) := y a + ∫ s in a..x, q s
  have hq : IntervalIntegrable q volume a b := hky.add hg
  have hF : AbsolutelyContinuousOnInterval F a b := by
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ y a) a b :=
      (LipschitzWith.const (y a)).lipschitzOnWith.absolutelyContinuousOnInterval
    exact hconst.add (hq.absolutelyContinuousOnInterval_intervalIntegral (by simp))
  have hFy : EqOn F y (uIcc a b) := by
    intro x hx
    have hmem : x ∈ Icc a b := by simpa [uIcc_of_le hab] using hx
    have := hy x hmem
    dsimp [F, q]
    linarith
  have hyAC : AbsolutelyContinuousOnInterval y a b := hF.congr hFy
  have hFderiv : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt F (q x) x := by
    filter_upwards [hq.ae_hasDerivAt_integral] with x hx hmem
    have hInt := hx hmem a (by simp)
    exact hInt.const_add (y a)
  have hae_a : ∀ᵐ x : ℝ, x ≠ a := by simp [ae_iff, measure_singleton]
  have hae_b : ∀ᵐ x : ℝ, x ≠ b := by simp [ae_iff, measure_singleton]
  have hyderiv : ∀ᵐ x, x ∈ uIcc a b →
      HasDerivAt y (k x * y x + g x) x := by
    filter_upwards [hFderiv, hae_a, hae_b] with x hx hxa hxb hmem
    have hIoo : x ∈ Ioo a b := by
      rw [uIcc_of_le hab] at hmem
      exact ⟨lt_of_le_of_ne hmem.1 (Ne.symm hxa), lt_of_le_of_ne hmem.2 hxb⟩
    have hloc : F =ᶠ[𝓝 x] y :=
      (hFy.mono (by
        rw [uIcc_of_le hab]
        exact Ioo_subset_Icc_self)).eventuallyEq_of_mem
          (Ioo_mem_nhds hIoo.1 hIoo.2)
    exact (hx hmem).congr_of_eventuallyEq hloc.symm
  exact eq_exp_mul_add_integral_of_ae_hasDerivAt hab hk hg hyAC hyderiv ht

/-- An interval-integral solution is automatically absolutely continuous. -/
theorem absolutelyContinuousOnInterval_of_integral_eq
    {a b : ℝ} (hab : a ≤ b) {k g y : ℝ → ℝ}
    (hky : IntervalIntegrable (fun s ↦ k s * y s) volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hy : ∀ t ∈ Icc a b,
      y t - y a = ∫ s in a..t, (k s * y s + g s)) :
    AbsolutelyContinuousOnInterval y a b := by
  have hq : IntervalIntegrable (fun s ↦ k s * y s + g s) volume a b :=
    hky.add hg
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ y a) a b :=
    (LipschitzWith.const (y a)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hF : AbsolutelyContinuousOnInterval
      (fun x ↦ y a + ∫ s in a..x, (k s * y s + g s)) a b :=
    hconst.add (hq.absolutelyContinuousOnInterval_intervalIntegral (by simp))
  apply hF.congr
  intro x hx
  have hmem : x ∈ Icc a b := by simpa [uIcc_of_le hab] using hx
  have := hy x hmem
  dsimp
  linarith

/-- The variation of constants formula defines an absolutely continuous solution of the
scalar linear integral equation. -/
theorem exists_integral_eq (a b c : ℝ) (hab : a ≤ b) {k g : ℝ → ℝ}
    (hk : IntervalIntegrable k volume a b)
    (hg : IntervalIntegrable g volume a b) :
    ∃ y : ℝ → ℝ,
      (∀ t ∈ Icc a b,
        y t = Real.exp (∫ s in a..t, k s) *
          (c + ∫ s in a..t, Real.exp (-(∫ σ in a..s, k σ)) * g s)) ∧
      AbsolutelyContinuousOnInterval y a b ∧ y a = c ∧
      ∀ t ∈ Icc a b,
        y t - y a = ∫ s in a..t, (k s * y s + g s) := by
  let K (x : ℝ) := ∫ s in a..x, k s
  let E (x : ℝ) := Real.exp (-K x)
  let P (x : ℝ) := Real.exp (K x)
  let H (x : ℝ) := ∫ s in a..x, E s * g s
  let y (x : ℝ) := P x * (c + H x)
  have hK : AbsolutelyContinuousOnInterval K a b :=
    hk.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hE : AbsolutelyContinuousOnInterval E a b := hK.neg.exp
  have hP : AbsolutelyContinuousOnInterval P a b := hK.exp
  have hEg : IntervalIntegrable (fun s ↦ E s * g s) volume a b :=
    hg.continuousOn_mul hE.continuousOn
  have hH : AbsolutelyContinuousOnInterval H a b :=
    hEg.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ c) a b :=
    (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval
  have hy : AbsolutelyContinuousOnInterval y a b := hP.mul (hconst.add hH)
  have hya : y a = c := by simp [y, P, H, K]
  have hderiv : ∀ᵐ x, x ∈ uIcc a b →
      HasDerivAt y (k x * y x + g x) x := by
    filter_upwards [hk.ae_hasDerivAt_integral,
      hEg.ae_hasDerivAt_integral] with x hKx hHx hmem
    have hK' : HasDerivAt K (k x) x := hKx hmem a (by simp)
    have hH' : HasDerivAt H (E x * g x) x := hHx hmem a (by simp)
    have hP' : HasDerivAt P (P x * k x) x := by
      simpa only [P, Function.comp_def] using hK'.exp
    have hprod := hP'.mul (hH'.const_add c)
    convert hprod using 1
    · have hPE : P x * E x = 1 := by simp [P, E, ← Real.exp_add]
      have hPEG : P x * (E x * g x) = g x := by
        rw [← mul_assoc, hPE, one_mul]
      dsimp [y]
      rw [hPEG]
      ring
  refine ⟨y, ?_, hy, hya, ?_⟩
  · intro t _
    rfl
  have hky : IntervalIntegrable (fun s ↦ k s * y s) volume a b :=
    hk.mul_continuousOn hy.continuousOn
  intro t ht
  have hsource := hky.add hg
  have hsub : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    exact Icc_subset_Icc_right ht.2
  symm
  apply integral_eq_sub_of_ae_hasDerivAt (hy.mono hsub)
  filter_upwards [hderiv] with x hx hmem
  exact hx (hsub hmem)

/-- Two solutions with the same initial value coincide on the interval. -/
theorem eq_on_of_integral_eq
    {a b : ℝ} (hab : a ≤ b) {k g y z : ℝ → ℝ}
    (hk : IntervalIntegrable k volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hky : IntervalIntegrable (fun s ↦ k s * y s) volume a b)
    (hkz : IntervalIntegrable (fun s ↦ k s * z s) volume a b)
    (hy : ∀ t ∈ Icc a b,
      y t - y a = ∫ s in a..t, (k s * y s + g s))
    (hz : ∀ t ∈ Icc a b,
      z t - z a = ∫ s in a..t, (k s * z s + g s))
    (ha : y a = z a) : EqOn y z (Icc a b) := by
  intro t ht
  rw [eq_exp_mul_add_integral_of_integral_eq hab hk hg hky hy ht,
    eq_exp_mul_add_integral_of_integral_eq hab hk hg hkz hz ht, ha]

/-- Duhamel's form of the variation of constants formula. -/
theorem eq_mul_exp_add_integral_exp
    {a b : ℝ} (hab : a ≤ b) {k g y : ℝ → ℝ}
    (hk : IntervalIntegrable k volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hky : IntervalIntegrable (fun s ↦ k s * y s) volume a b)
    (hy : ∀ t ∈ Icc a b,
      y t - y a = ∫ s in a..t, (k s * y s + g s))
    {t : ℝ} (ht : t ∈ Icc a b) :
    y t = y a * Real.exp (∫ s in a..t, k s) +
      ∫ s in a..t, Real.exp (∫ σ in s..t, k σ) * g s := by
  let K (x : ℝ) := ∫ s in a..x, k s
  have hk_at : IntervalIntegrable k volume a t := hk.mono_set (by
    rw [uIcc_of_le hab, uIcc_of_le ht.1]
    exact Icc_subset_Icc_right ht.2)
  have hkernel (s : ℝ) (hs : s ∈ Icc a t) :
      Real.exp (∫ σ in s..t, k σ) = Real.exp (K t) * Real.exp (-K s) := by
    have hk_as : IntervalIntegrable k volume a s := hk_at.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hs.1]
      exact Icc_subset_Icc_right hs.2)
    have hsub := integral_interval_sub_left hk_at hk_as
    rw [← hsub, Real.exp_sub, Real.exp_neg, div_eq_mul_inv]
  have hrepr := eq_exp_mul_add_integral_of_integral_eq hab hk hg hky hy ht
  calc
    y t = Real.exp (K t) *
        (y a + ∫ s in a..t, Real.exp (-K s) * g s) := hrepr
    _ = y a * Real.exp (K t) +
        Real.exp (K t) * ∫ s in a..t, Real.exp (-K s) * g s := by ring
    _ = y a * Real.exp (K t) +
        ∫ s in a..t, Real.exp (K t) * (Real.exp (-K s) * g s) := by
          rw [integral_const_mul]
    _ = _ := by
      congr 1
      apply integral_congr
      intro s hs
      dsimp only
      rw [hkernel s (by simpa [uIcc_of_le ht.1] using hs)]
      ring

/-- A solution with nonnegative initial value and nonnegative forcing stays nonnegative. -/
theorem nonneg_of_integral_eq
    {a b : ℝ} (hab : a ≤ b) {k g y : ℝ → ℝ}
    (hk : IntervalIntegrable k volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hky : IntervalIntegrable (fun s ↦ k s * y s) volume a b)
    (hy : ∀ t ∈ Icc a b,
      y t - y a = ∫ s in a..t, (k s * y s + g s))
    (hya : 0 ≤ y a) (hg_nonneg : ∀ s ∈ Icc a b, 0 ≤ g s)
    {t : ℝ} (ht : t ∈ Icc a b) : 0 ≤ y t := by
  rw [eq_exp_mul_add_integral_of_integral_eq hab hk hg hky hy ht]
  apply mul_nonneg (Real.exp_nonneg _)
  apply add_nonneg hya
  apply integral_nonneg ht.1
  intro s hs
  exact mul_nonneg (Real.exp_nonneg _) (hg_nonneg s ⟨hs.1, hs.2.trans ht.2⟩)

/-- The standard exponential bound for a scalar linear integral equation. -/
theorem abs_le_exp_integral_abs_mul
    {a b : ℝ} (hab : a ≤ b) {k g y : ℝ → ℝ}
    (hk : IntervalIntegrable k volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hky : IntervalIntegrable (fun s ↦ k s * y s) volume a b)
    (hy : ∀ t ∈ Icc a b,
      y t - y a = ∫ s in a..t, (k s * y s + g s))
    {t : ℝ} (ht : t ∈ Icc a b) :
    |y t| ≤ Real.exp (∫ s in a..t, |k s|) *
      (|y a| + ∫ s in a..t, |g s|) := by
  let K (x : ℝ) := ∫ s in a..x, k s
  let E (x : ℝ) := Real.exp (-K x)
  let P (x : ℝ) := Real.exp (K x)
  let A : ℝ := ∫ s in a..t, |k s|
  have hk_at : IntervalIntegrable k volume a t := hk.mono_set (by
    rw [uIcc_of_le hab, uIcc_of_le ht.1]
    exact Icc_subset_Icc_right ht.2)
  have hkabs_at : IntervalIntegrable (fun s ↦ |k s|) volume a t := hk_at.abs
  have hgabs_at : IntervalIntegrable (fun s ↦ |g s|) volume a t :=
    (hg.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le ht.1]
      exact Icc_subset_Icc_right ht.2)).abs
  have hK_le : K t ≤ A :=
    integral_mono_on ht.1 hk_at hkabs_at (fun s _ ↦ le_abs_self _)
  have hP_le : P t ≤ Real.exp A := Real.exp_le_exp.mpr hK_le
  have hPE_le (s : ℝ) (hs : s ∈ Icc a t) : P t * E s ≤ Real.exp A := by
    have hk_as : IntervalIntegrable k volume a s := hk_at.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hs.1]
      exact Icc_subset_Icc_right hs.2)
    have hk_st : IntervalIntegrable k volume s t := hk_at.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hs.2]
      exact Icc_subset_Icc_left hs.1)
    have hkabs_st : IntervalIntegrable (fun u ↦ |k u|) volume s t := hk_st.abs
    have hsmall : (∫ u in s..t, k u) ≤ ∫ u in s..t, |k u| :=
      integral_mono_on hs.2 hk_st hkabs_st (fun u _ ↦ le_abs_self _)
    have hlarge : (∫ u in s..t, |k u|) ≤ A :=
      integral_mono_interval hs.1 hs.2 le_rfl
        (Filter.Eventually.of_forall (fun u ↦ abs_nonneg (k u))) hkabs_at
    have hdiff := integral_interval_sub_left hk_at hk_as
    have hExp : P t * E s = Real.exp (∫ u in s..t, k u) := by
      rw [← hdiff, Real.exp_sub]
      simp [P, E, K, Real.exp_neg, div_eq_mul_inv]
    rw [hExp]
    exact Real.exp_le_exp.mpr (hsmall.trans hlarge)
  have hE : AbsolutelyContinuousOnInterval E a b :=
    (hk.absolutelyContinuousOnInterval_intervalIntegral (by simp)).neg.exp
  have hEg : IntervalIntegrable (fun s ↦ E s * g s) volume a b :=
    hg.continuousOn_mul hE.continuousOn
  have hB : IntervalIntegrable (fun s ↦ P t * (E s * g s)) volume a t :=
    (hEg.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le ht.1]
      exact Icc_subset_Icc_right ht.2)).const_mul (P t)
  have hC : IntervalIntegrable (fun s ↦ Real.exp A * |g s|) volume a t :=
    hgabs_at.const_mul (Real.exp A)
  have hIntBound :
      |∫ s in a..t, P t * (E s * g s)| ≤
        Real.exp A * ∫ s in a..t, |g s| := by
    calc
      |∫ s in a..t, P t * (E s * g s)| ≤
          ∫ s in a..t, |P t * (E s * g s)| := abs_integral_le_integral_abs ht.1
      _ ≤ ∫ s in a..t, Real.exp A * |g s| := by
        apply integral_mono_on ht.1 hB.abs hC
        intro s hs
        rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
        calc
          P t * (E s * |g s|) = (P t * E s) * |g s| := by ring
          _ ≤ Real.exp A * |g s| :=
            mul_le_mul_of_nonneg_right (hPE_le s hs) (abs_nonneg _)
      _ = _ := by rw [integral_const_mul]
  have hrepr := eq_exp_mul_add_integral_of_integral_eq hab hk hg hky hy ht
  have hPnonneg : 0 ≤ P t := (Real.exp_pos _).le
  have hAn : 0 ≤ Real.exp A := (Real.exp_pos _).le
  calc
    |y t| = |P t * (y a + ∫ s in a..t, E s * g s)| := by rw [hrepr]
    _ ≤ P t * |y a| + |∫ s in a..t, P t * (E s * g s)| := by
      rw [abs_mul, abs_of_nonneg hPnonneg]
      calc
        P t * |y a + ∫ s in a..t, E s * g s| ≤
            P t * (|y a| + |∫ s in a..t, E s * g s|) :=
              mul_le_mul_of_nonneg_left (abs_add_le _ _) hPnonneg
        _ = _ := by
          rw [mul_add, integral_const_mul, abs_mul, abs_of_nonneg hPnonneg]
    _ ≤ Real.exp A * |y a| + Real.exp A * ∫ s in a..t, |g s| := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hP_le (abs_nonneg _)
      · exact hIntBound
    _ = _ := by ring

/-- Reflection turns a terminal-value integral equation into an initial-value equation.
The coefficient and forcing terms both change sign under reflection. -/
theorem backward_integral_eq_iff_reflected
    {a b : ℝ} {q y : ℝ → ℝ} :
    (∀ t ∈ Icc a b, y t - y b = ∫ s in b..t, q s) ↔
      (∀ x ∈ Icc (-b) (-a),
        y (-x) - y b = ∫ s in -b..x, -q (-s)) := by
  have hreflect (x : ℝ) :
      (∫ s in -b..x, -q (-s)) = ∫ s in b..-x, q s := by
    rw [integral_neg, integral_comp_neg, integral_symm]
    simp
  constructor
  · intro h x hx
    have hmem : -x ∈ Icc a b := by
      constructor <;> simp only [mem_Icc] at hx ⊢ <;> linarith
    rw [hreflect]
    exact h (-x) hmem
  · intro h t ht
    have hmem : -t ∈ Icc (-b) (-a) := by
      constructor <;> simp only [mem_Icc] at ht ⊢ <;> linarith
    simpa only [neg_neg, hreflect] using h (-t) hmem

end intervalIntegral

end
