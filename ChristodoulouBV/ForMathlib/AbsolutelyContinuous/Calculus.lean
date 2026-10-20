module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Calculus for absolutely continuous real functions

This file packages the fundamental theorem of calculus, the chain rule, and product rule
for absolutely continuous functions on a compact real interval.
-/

public section

open Set MeasureTheory

namespace LipschitzOnWith

/-- Inversion is Lipschitz on a set uniformly separated from zero. -/
theorem inv_of_norm_ge {s : Set ℝ} {c : ℝ} (hc : 0 < c)
    (hs : ∀ x ∈ s, c ≤ ‖x‖) :
    LipschitzOnWith ⟨c⁻¹ ^ 2, by positivity⟩ (fun x : ℝ ↦ x⁻¹) s := by
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro x hx y hy
  have hx0 : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hc (hs x hx))
  have hy0 : y ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hc (hs y hy))
  calc
    dist x⁻¹ y⁻¹ = ‖x‖⁻¹ * dist x y * ‖y‖⁻¹ := by
      rw [dist_inv_inv₀ hx0 hy0]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ c⁻¹ * dist x y * c⁻¹ := by
      gcongr
      · exact hs x hx
      · exact hs y hy
    _ = (⟨c⁻¹ ^ 2, by positivity⟩ : NNReal) * dist x y := by
      simp only [pow_two]
      ring

end LipschitzOnWith

namespace AbsolutelyContinuousOnInterval

/-- The derivative of a product of absolutely continuous real functions satisfies the
product rule almost everywhere on the interval. -/
theorem ae_deriv_mul {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    ∀ᵐ x ∂volume, x ∈ uIcc a b →
      deriv (fun t ↦ f t * g t) x = deriv f x * g x + f x * deriv g x := by
  filter_upwards [hf.ae_differentiableAt, hg.ae_differentiableAt] with x hfx hgx hx
  exact deriv_mul (hfx hx) (hgx hx)

/-- The reciprocal of an absolutely continuous real function stays absolutely continuous
when the function is uniformly separated from zero. Its usual derivative formula holds
almost everywhere. -/
theorem inv_and_ae_deriv {g : ℝ → ℝ} {a b c : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b) (hc : 0 < c)
    (hgc : ∀ x ∈ uIcc a b, c ≤ |g x|) :
    AbsolutelyContinuousOnInterval (fun x ↦ (g x)⁻¹) a b ∧
      ∀ᵐ x ∂volume, x ∈ uIcc a b →
        deriv (fun t ↦ (g t)⁻¹) x = -deriv g x / (g x) ^ 2 := by
  have hK := LipschitzOnWith.inv_of_norm_ge hc
    (s := g '' uIcc a b) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      simpa only [Real.norm_eq_abs] using hgc x hx)
  constructor
  · exact hK.comp_absolutelyContinuousOnInterval (mapsTo_image _ _) hg
  · filter_upwards [hg.ae_differentiableAt] with x hx hxu
    have hx0 : g x ≠ 0 := by
      have := hgc x hxu
      exact abs_pos.mp (lt_of_lt_of_le hc this)
    exact deriv_fun_inv'' (hx hxu) hx0

/-- The quotient of two absolutely continuous real functions is absolutely continuous
when the denominator is uniformly separated from zero, with its usual derivative
almost everywhere. -/
theorem div_and_ae_deriv {f g : ℝ → ℝ} {a b c : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) (hc : 0 < c)
    (hgc : ∀ x ∈ uIcc a b, c ≤ |g x|) :
    AbsolutelyContinuousOnInterval (fun x ↦ f x / g x) a b ∧
      ∀ᵐ x ∂volume, x ∈ uIcc a b →
        deriv (fun t ↦ f t / g t) x =
          (deriv f x * g x - f x * deriv g x) / (g x) ^ 2 := by
  obtain ⟨hgi, _⟩ := hg.inv_and_ae_deriv hc hgc
  constructor
  · simpa only [div_eq_mul_inv] using hf.fun_mul hgi
  · filter_upwards [hf.ae_differentiableAt, hg.ae_differentiableAt] with x hfx hgx hxu
    have hx0 : g x ≠ 0 := by
      have := hgc x hxu
      exact abs_pos.mp (lt_of_lt_of_le hc this)
    exact deriv_fun_div (hfx hxu) (hgx hxu) hx0

/-- A differentiable Lipschitz outer function obeys the chain rule almost everywhere when
composed with an absolutely continuous real function. -/
theorem ae_deriv_comp_of_lipschitzOnWith {f h : ℝ → ℝ} {a b : ℝ} {K : NNReal}
    {s : Set ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hh : LipschitzOnWith K h s) (hfs : MapsTo f (uIcc a b) s)
    (hd : ∀ x ∈ s, DifferentiableAt ℝ h x) :
    AbsolutelyContinuousOnInterval (h ∘ f) a b ∧
      ∀ᵐ x ∂volume, x ∈ uIcc a b →
        deriv (h ∘ f) x = deriv h (f x) * deriv f x := by
  constructor
  · exact hh.comp_absolutelyContinuousOnInterval hfs hf
  · filter_upwards [hf.ae_differentiableAt] with x hx hxu
    exact deriv_comp x (hd _ (hfs hxu)) (hx hxu)

/-- A differentiable function locally Lipschitz on the compact image of an absolutely
continuous function obeys the chain rule almost everywhere. -/
theorem ae_deriv_comp_of_locallyLipschitzOn {f h : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hh : LocallyLipschitzOn (f '' uIcc a b) h)
    (hd : ∀ x ∈ f '' uIcc a b, DifferentiableAt ℝ h x) :
    AbsolutelyContinuousOnInterval (h ∘ f) a b ∧
      ∀ᵐ x ∂volume, x ∈ uIcc a b →
        deriv (h ∘ f) x = deriv h (f x) * deriv f x := by
  obtain ⟨K, hK⟩ := hh.exists_lipschitzOnWith_of_compact
    (isCompact_uIcc.image_of_continuousOn hf.continuousOn)
  exact hf.ae_deriv_comp_of_lipschitzOnWith hK (mapsTo_image _ _) hd

/-- A globally `C¹` real function composed with an absolutely continuous real function
is absolutely continuous and satisfies the chain rule almost everywhere. -/
theorem ae_deriv_comp_of_contDiff {f h : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hh : ContDiff ℝ 1 h) :
    AbsolutelyContinuousOnInterval (h ∘ f) a b ∧
      ∀ᵐ x ∂volume, x ∈ uIcc a b →
        deriv (h ∘ f) x = deriv h (f x) * deriv f x := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  obtain ⟨K, hK⟩ := (hh.contDiffOn (s := Icc (-C) C)).exists_lipschitzOnWith
    (by decide) (convex_Icc _ _) isCompact_Icc
  exact hf.ae_deriv_comp_of_lipschitzOnWith hK
    (fun x hx ↦ by
      have hx' := hC x hx
      simpa only [Real.norm_eq_abs, mem_Icc] using (abs_le.mp hx'))
    (fun x _ ↦ hh.differentiable_one x)

/-- A function given pointwise on an interval by an integrable primitive is absolutely
continuous there. -/
theorem of_integral_eq_sub {F g : ℝ → ℝ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b)
    (hF : ∀ t ∈ uIcc a b, F t - F a = ∫ x in a..t, g x) :
    AbsolutelyContinuousOnInterval F a b := by
  have h := hg.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hc : AbsolutelyContinuousOnInterval
      (fun t ↦ F a + ∫ x in a..t, g x) a b := by
    exact (LipschitzWith.const (F a)).lipschitzOnWith.absolutelyContinuousOnInterval.add h
  apply hc.congr
  intro t ht
  dsimp
  linarith [hF t ht]

/-- The derivative of a function represented by an integrable primitive equals its
density almost everywhere on the interval. -/
theorem ae_deriv_eq_of_integral_eq_sub {F g : ℝ → ℝ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b)
    (hF : ∀ t ∈ uIcc a b, F t - F a = ∫ x in a..t, g x) :
    ∀ᵐ t ∂volume, t ∈ uIcc a b → deriv F t = g t := by
  have hEq : EqOn F (fun u ↦ F a + ∫ x in a..u, g x) (uIcc a b) := by
    intro u hu
    dsimp
    linarith [hF u hu]
  have hEq' : EqOn F (fun u ↦ F a + ∫ x in a..u, g x) (uIoo a b) :=
    hEq.mono uIoo_subset_uIcc_self
  have hopen : IsOpen (uIoo a b) := by
    rcases le_total a b with hab | hba
    · simpa [uIoo_of_le hab] using (isOpen_Ioo : IsOpen (Ioo a b))
    · simpa [uIoo_of_ge hba] using (isOpen_Ioo : IsOpen (Ioo b a))
  have hderiv := hEq'.deriv hopen
  have ha : ∀ᵐ t : ℝ ∂volume, t ≠ a := by simp [ae_iff, measure_singleton]
  have hb : ∀ᵐ t : ℝ ∂volume, t ≠ b := by simp [ae_iff, measure_singleton]
  filter_upwards [hg.ae_hasDerivAt_integral, ha, hb] with t ht hta htb htu
  have htu' : t ∈ uIoo a b := by
    rcases le_total a b with hab | hba
    · rw [uIcc_of_le hab] at htu
      rw [uIoo_of_le hab]
      exact ⟨lt_of_le_of_ne htu.1 (Ne.symm hta), lt_of_le_of_ne htu.2 htb⟩
    · rw [uIcc_of_ge hba] at htu
      rw [uIoo_of_ge hba]
      exact ⟨lt_of_le_of_ne htu.1 (Ne.symm htb), lt_of_le_of_ne htu.2 hta⟩
  rw [hderiv htu']
  have hprim := (ht htu a (by simp)).deriv
  simpa only [deriv_const_add] using hprim

/-- Two interval-integrable densities representing the same primitive agree almost
everywhere on the interval. -/
theorem ae_eq_of_integral_eq_sub {F g h : ℝ → ℝ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b)
    (hh : IntervalIntegrable h volume a b)
    (hFg : ∀ t ∈ uIcc a b, F t - F a = ∫ x in a..t, g x)
    (hFh : ∀ t ∈ uIcc a b, F t - F a = ∫ x in a..t, h x) :
    ∀ᵐ t ∂volume, t ∈ uIcc a b → g t = h t := by
  filter_upwards [ae_deriv_eq_of_integral_eq_sub hg hFg,
    ae_deriv_eq_of_integral_eq_sub hh hFh] with t hgt hht htu
  exact (hgt htu).symm.trans (hht htu)

/-- Product rule for functions specified by interval-integrable densities, at the
endpoints of the interval. -/
theorem integral_mul_eq_sub_of_integral_eq_sub
    {F G f g : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hF : ∀ t ∈ uIcc a b, F t - F a = ∫ x in a..t, f x)
    (hG : ∀ t ∈ uIcc a b, G t - G a = ∫ x in a..t, g x) :
    ∫ x in a..b, f x * G x + F x * g x = F b * G b - F a * G a := by
  have hFac := of_integral_eq_sub hf hF
  have hGac := of_integral_eq_sub hg hG
  rw [← hFac.integral_deriv_mul_eq_sub hGac]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_deriv_eq_of_integral_eq_sub hf hF,
    ae_deriv_eq_of_integral_eq_sub hg hG] with x hfx hgx hx
  have hxu : x ∈ uIcc a b := uIoc_subset_uIcc hx
  rw [hfx hxu, hgx hxu]

/-- Product rule in primitive form, for any two endpoints in the ambient interval. -/
theorem integral_mul_eq_sub_of_integral_eq_sub_all
    {F G f g : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hF : ∀ s ∈ uIcc a b, ∀ t ∈ uIcc a b,
      F t - F s = ∫ x in s..t, f x)
    (hG : ∀ s ∈ uIcc a b, ∀ t ∈ uIcc a b,
      G t - G s = ∫ x in s..t, g x)
    {s t : ℝ} (hs : s ∈ uIcc a b) (ht : t ∈ uIcc a b) :
    ∫ x in s..t, f x * G x + F x * g x = F t * G t - F s * G s := by
  have hst : uIcc s t ⊆ uIcc a b := uIcc_subset_uIcc hs ht
  apply integral_mul_eq_sub_of_integral_eq_sub
    (hf.mono_set hst) (hg.mono_set hst)
  · intro u hu
    exact hF s hs u (hst hu)
  · intro u hu
    exact hG s hs u (hst hu)

end AbsolutelyContinuousOnInterval
