module

public import ChristodoulouBV.ForMathlib.AbsolutelyContinuous.Calculus
public import ChristodoulouBV.ForMathlib.BoundedVariation.AbsolutelyContinuous
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# A weighted integration by parts inequality

This is the finite-interval analytic step in Christodoulou's proof of
Lemma 4.1. It handles the absolute value of the signed weighted numerator
without assuming that it is differentiable at its zeros.
-/

public section

open Set MeasureTheory Filter
open scoped Topology Interval

namespace ChristodoulouBV

private theorem deriv_abs_comp_le_abs_deriv {I : ℝ → ℝ} {x : ℝ}
    (hI : DifferentiableAt ℝ I x) :
    deriv (fun t => |I t|) x ≤ |deriv I x| := by
  by_cases hz : I x = 0
  · have hmin : IsLocalMin (fun t => |I t|) x := by
      change ∀ᶠ t in 𝓝 x, |I x| ≤ |I t|
      rw [hz, abs_zero]
      exact Filter.Eventually.of_forall fun t => abs_nonneg _
    rw [hmin.deriv_eq_zero]
    exact abs_nonneg _
  · rcases lt_or_gt_of_ne hz with hn | hp
    · have hd := (hasDerivAt_abs_neg hn).comp x hI.hasDerivAt
      have heq : deriv (fun t => |I t|) x = -deriv I x := by
        simpa [Function.comp_def] using hd.deriv
      rw [heq]
      exact neg_le_abs _
    · have hd := (hasDerivAt_abs_pos hp).comp x hI.hasDerivAt
      have heq : deriv (fun t => |I t|) x = deriv I x := by
        simpa only [Function.comp_def, one_mul] using hd.deriv
      rw [heq]
      exact le_abs_self _

private theorem neg_abs_deriv_le_deriv_abs_comp {I : ℝ → ℝ} {x : ℝ}
    (hI : DifferentiableAt ℝ I x) :
    -|deriv I x| ≤ deriv (fun t => |I t|) x := by
  by_cases hz : I x = 0
  · have hmin : IsLocalMin (fun t => |I t|) x := by
      change ∀ᶠ t in 𝓝 x, |I x| ≤ |I t|
      rw [hz, abs_zero]
      exact Filter.Eventually.of_forall fun t => abs_nonneg _
    rw [hmin.deriv_eq_zero]
    exact neg_nonpos.mpr (abs_nonneg _)
  · rcases lt_or_gt_of_ne hz with hn | hp
    · have hd := (hasDerivAt_abs_neg hn).comp x hI.hasDerivAt
      have heq : deriv (fun t => |I t|) x = -deriv I x := by
        simpa [Function.comp_def] using hd.deriv
      rw [heq]
      exact neg_le_neg (le_abs_self _)
    · have hd := (hasDerivAt_abs_pos hp).comp x hI.hasDerivAt
      have heq : deriv (fun t => |I t|) x = deriv I x := by
        simpa only [Function.comp_def, one_mul] using hd.deriv
      rw [heq]
      exact neg_abs_le _

/-- Integration by parts for a weighted numerator `I` satisfying
`I' = r f'` on a compact interval away from the zero of `r`. -/
theorem weighted_numerator_finite_interval_bound
    {I r f : ℝ → ℝ} {c w : ℝ} (hc : c ≤ w)
    (hI : ContDiffOn ℝ 1 I (Icc c w))
    (hr : ContDiffOn ℝ 1 r (Icc c w))
    (hf : ContDiffOn ℝ 1 f (Icc c w))
    (hrpos : ∀ t ∈ Icc c w, 0 < r t)
    (hIderiv : ∀ t ∈ Ioo c w, deriv I t = r t * deriv f t) :
    (∫ t in c..w, |I t| * deriv r t / (r t) ^ 2) ≤
      |I c| / r c + ∫ t in c..w, |deriv f t| := by
  let F : ℝ → ℝ := fun t => |I t|
  let G : ℝ → ℝ := fun t => (r t)⁻¹
  have hIAC : AbsolutelyContinuousOnInterval I c w :=
    (show ContDiffOn ℝ 1 I (uIcc c w) by
      simpa only [uIcc_of_le hc] using hI).absolutelyContinuousOnInterval
  have hFAC : AbsolutelyContinuousOnInterval F c w := by
    have hlip : LipschitzWith 1 (fun z : ℝ => |z|) := by
      convert (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)) using 1
    exact hlip.comp_absolutelyContinuousOnInterval hIAC
  have hGdiff : ContDiffOn ℝ 1 G (Icc c w) :=
    hr.inv (fun t ht => ne_of_gt (hrpos t ht))
  have hGAC : AbsolutelyContinuousOnInterval G c w :=
    (show ContDiffOn ℝ 1 G (uIcc c w) by
      simpa only [uIcc_of_le hc] using hGdiff).absolutelyContinuousOnInterval
  have hfAC : AbsolutelyContinuousOnInterval f c w :=
    (show ContDiffOn ℝ 1 f (uIcc c w) by
      simpa only [uIcc_of_le hc] using hf).absolutelyContinuousOnInterval
  have hIBP := hFAC.integral_mul_deriv_eq_deriv_mul hGAC
  have hGderiv : ∀ t ∈ Ioo c w,
      deriv G t = -deriv r t / (r t) ^ 2 := by
    intro t ht
    have hdiff : DifferentiableAt ℝ r t :=
      ((hr.differentiableOn (by norm_num)).mono Ioo_subset_Icc_self t ht)
        |>.differentiableAt (Ioo_mem_nhds ht.1 ht.2)
    exact deriv_fun_inv'' hdiff (ne_of_gt (hrpos t (Ioo_subset_Icc_self ht)))
  have hleft : (∫ t in c..w, F t * deriv G t) =
      -(∫ t in c..w, |I t| * deriv r t / (r t) ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume w] with t hne ht
    rw [uIoc_of_le hc] at ht
    have ht' : t ∈ Ioo c w := ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩
    rw [hGderiv t ht']
    dsimp [F]
    ring
  have hright : (∫ t in c..w, deriv F t * G t) ≤
      ∫ t in c..w, |deriv f t| := by
    have hfg : IntervalIntegrable (fun t => deriv F t * G t) volume c w :=
      hFAC.intervalIntegrable_deriv.mul_continuousOn hGAC.continuousOn
    apply intervalIntegral.integral_mono_on_of_le_Ioo hc hfg
      hfAC.intervalIntegrable_deriv.abs
    intro t ht
    have ht' : t ∈ Ioo c w := ht
    have htIcc : t ∈ Icc c w := Ioo_subset_Icc_self ht'
    have hIdiff : DifferentiableAt ℝ I t :=
      ((hI.differentiableOn (by norm_num)).mono Ioo_subset_Icc_self t ht')
        |>.differentiableAt (Ioo_mem_nhds ht'.1 ht'.2)
    have hderivAbs := deriv_abs_comp_le_abs_deriv hIdiff
    rw [hIderiv t ht', abs_mul, abs_of_pos (hrpos t htIcc)] at hderivAbs
    change deriv F t * (r t)⁻¹ ≤ |deriv f t|
    have hInv : 0 < (r t)⁻¹ := inv_pos.mpr (hrpos t htIcc)
    have hdiv := mul_le_mul_of_nonneg_right hderivAbs hInv.le
    have hid : r t * (|deriv f t| * (r t)⁻¹) = |deriv f t| := by
      field_simp [ne_of_gt (hrpos t htIcc)]
    simpa only [F, G, mul_assoc, hid] using hdiv
  rw [hleft] at hIBP
  have hFw : 0 ≤ F w := abs_nonneg _
  have hGw : 0 < G w := inv_pos.mpr (hrpos w ⟨hc, le_rfl⟩)
  have hFc : F c * G c = |I c| / r c := by
    dsimp [F, G]
    ring
  rw [hFc] at hIBP
  linarith only [hIBP, hright, mul_nonneg hFw hGw.le]

/-- The reflected weighted integration by parts inequality. Here `r`
decreases toward the right endpoint, which is the incoming axis. -/
theorem weighted_numerator_finite_interval_bound_incoming
    {I r f : ℝ → ℝ} {c w : ℝ} (hc : c ≤ w)
    (hI : ContDiffOn ℝ 1 I (Icc c w))
    (hr : ContDiffOn ℝ 1 r (Icc c w))
    (hf : ContDiffOn ℝ 1 f (Icc c w))
    (hrpos : ∀ t ∈ Icc c w, 0 < r t)
    (hIderiv : ∀ t ∈ Ioo c w, deriv I t = r t * deriv f t) :
    (∫ t in c..w, |I t| * (-deriv r t) / (r t) ^ 2) ≤
      |I w| / r w + ∫ t in c..w, |deriv f t| := by
  let F : ℝ → ℝ := fun t => |I t|
  let G : ℝ → ℝ := fun t => (r t)⁻¹
  have hIAC : AbsolutelyContinuousOnInterval I c w :=
    (show ContDiffOn ℝ 1 I (uIcc c w) by
      simpa only [uIcc_of_le hc] using hI).absolutelyContinuousOnInterval
  have hFAC : AbsolutelyContinuousOnInterval F c w := by
    have hlip : LipschitzWith 1 (fun z : ℝ => |z|) := by
      convert (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)) using 1
    exact hlip.comp_absolutelyContinuousOnInterval hIAC
  have hGdiff : ContDiffOn ℝ 1 G (Icc c w) :=
    hr.inv (fun t ht => ne_of_gt (hrpos t ht))
  have hGAC : AbsolutelyContinuousOnInterval G c w :=
    (show ContDiffOn ℝ 1 G (uIcc c w) by
      simpa only [uIcc_of_le hc] using hGdiff).absolutelyContinuousOnInterval
  have hfAC : AbsolutelyContinuousOnInterval f c w :=
    (show ContDiffOn ℝ 1 f (uIcc c w) by
      simpa only [uIcc_of_le hc] using hf).absolutelyContinuousOnInterval
  have hIBP := hFAC.integral_mul_deriv_eq_deriv_mul hGAC
  have hGderiv : ∀ t ∈ Ioo c w,
      deriv G t = -deriv r t / (r t) ^ 2 := by
    intro t ht
    have hdiff : DifferentiableAt ℝ r t :=
      ((hr.differentiableOn (by norm_num)).mono Ioo_subset_Icc_self t ht)
        |>.differentiableAt (Ioo_mem_nhds ht.1 ht.2)
    exact deriv_fun_inv'' hdiff (ne_of_gt (hrpos t (Ioo_subset_Icc_self ht)))
  have hleft : (∫ t in c..w, F t * deriv G t) =
      ∫ t in c..w, |I t| * (-deriv r t) / (r t) ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume w] with t hne ht
    rw [uIoc_of_le hc] at ht
    have ht' : t ∈ Ioo c w := ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩
    rw [hGderiv t ht']
    dsimp [F]
    ring
  have hright : -(∫ t in c..w, deriv F t * G t) ≤
      ∫ t in c..w, |deriv f t| := by
    rw [← intervalIntegral.integral_neg]
    have hfg : IntervalIntegrable (fun t => -(deriv F t * G t)) volume c w :=
      (hFAC.intervalIntegrable_deriv.mul_continuousOn hGAC.continuousOn).neg
    apply intervalIntegral.integral_mono_on_of_le_Ioo hc hfg
      hfAC.intervalIntegrable_deriv.abs
    intro t ht
    have htIcc : t ∈ Icc c w := Ioo_subset_Icc_self ht
    have hIdiff : DifferentiableAt ℝ I t :=
      ((hI.differentiableOn (by norm_num)).mono Ioo_subset_Icc_self t ht)
        |>.differentiableAt (Ioo_mem_nhds ht.1 ht.2)
    have hderivAbs := neg_abs_deriv_le_deriv_abs_comp hIdiff
    rw [hIderiv t ht, abs_mul, abs_of_pos (hrpos t htIcc)] at hderivAbs
    change -(deriv F t * (r t)⁻¹) ≤ |deriv f t|
    have hInv : 0 < (r t)⁻¹ := inv_pos.mpr (hrpos t htIcc)
    have hdiv := mul_le_mul_of_nonneg_right hderivAbs hInv.le
    have hid : r t * (|deriv f t| * (r t)⁻¹) = |deriv f t| := by
      field_simp [ne_of_gt (hrpos t htIcc)]
    nlinarith only [hdiv, hid]
  rw [hleft] at hIBP
  have hFc : 0 ≤ F c := abs_nonneg _
  have hGc : 0 < G c := inv_pos.mpr (hrpos c ⟨le_rfl, hc⟩)
  have hFw : F w * G w = |I w| / r w := by
    dsimp [F, G]
    ring
  rw [hFw] at hIBP
  linarith only [hIBP, hright, mul_nonneg hFc hGc.le]

/-- Remove a vanishing left boundary term from finite-interval bounds. -/
theorem interval_bound_of_vanishing_left_boundary {a b : ℝ} (hab : a < b)
    {g f q : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a b)
    (hf : IntervalIntegrable f volume a b)
    (hq : Tendsto q (𝓝[>] a) (𝓝 (0 : ℝ)))
    (hbound : ∀ c ∈ Ioo a b,
      (∫ t in c..b, g t) ≤ |q c| + ∫ t in c..b, f t) :
    (∫ t in a..b, g t) ≤ ∫ t in a..b, f t := by
  have hcontG : ContinuousOn (fun c => ∫ t in c..b, g t) (Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hg
      (show b ∈ uIcc a b by simp [hab.le])
    have heq : (fun c => ∫ t in c..b, g t) =
        (fun c => -(∫ t in b..c, g t)) := by
      funext c
      exact intervalIntegral.integral_symm b c
    rw [heq]
    have hneg : ContinuousOn (-(fun c => ∫ t in b..c, g t)) (Icc a b) := by
      simpa only [uIcc_of_le hab.le] using h.neg
    exact hneg.congr (by intro c hc; simp only [Pi.neg_apply])
  have hcontF : ContinuousOn (fun c => ∫ t in c..b, f t) (Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hf
      (show b ∈ uIcc a b by simp [hab.le])
    have heq : (fun c => ∫ t in c..b, f t) =
        (fun c => -(∫ t in b..c, f t)) := by
      funext c
      exact intervalIntegral.integral_symm b c
    rw [heq]
    have hneg : ContinuousOn (-(fun c => ∫ t in b..c, f t)) (Icc a b) := by
      simpa only [uIcc_of_le hab.le] using h.neg
    exact hneg.congr (by intro c hc; simp only [Pi.neg_apply])
  have hlimG : Tendsto (fun c => ∫ t in c..b, g t) (𝓝[>] a)
      (𝓝 (∫ t in a..b, g t)) :=
    (by simpa only [nhdsWithin_Ioo_eq_nhdsGT hab] using
      ((hcontG.continuousWithinAt ⟨le_rfl, hab.le⟩).mono
        Ioo_subset_Icc_self).tendsto)
  have hlimF : Tendsto (fun c => ∫ t in c..b, f t) (𝓝[>] a)
      (𝓝 (∫ t in a..b, f t)) :=
    (by simpa only [nhdsWithin_Ioo_eq_nhdsGT hab] using
      ((hcontF.continuousWithinAt ⟨le_rfl, hab.le⟩).mono
        Ioo_subset_Icc_self).tendsto)
  have hevent : ∀ᶠ c in 𝓝[>] a,
      (∫ t in c..b, g t) ≤ |q c| + ∫ t in c..b, f t :=
    by
      filter_upwards [Ioo_mem_nhdsGT hab] with c hc
      exact hbound c hc
  have h := le_of_tendsto_of_tendsto hlimG (hq.abs.add hlimF) hevent
  simpa using h

/-- Remove a vanishing right boundary term from finite-interval bounds. -/
theorem interval_bound_of_vanishing_right_boundary {a b : ℝ} (hab : a < b)
    {g f q : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a b)
    (hf : IntervalIntegrable f volume a b)
    (hq : Tendsto q (𝓝[<] b) (𝓝 (0 : ℝ)))
    (hbound : ∀ c ∈ Ioo a b,
      (∫ t in a..c, g t) ≤ |q c| + ∫ t in a..c, f t) :
    (∫ t in a..b, g t) ≤ ∫ t in a..b, f t := by
  have hcontG : ContinuousOn (fun c => ∫ t in a..c, g t) (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using
      (intervalIntegral.continuousOn_primitive_interval' hg
        (show a ∈ uIcc a b by simp [hab.le]))
  have hcontF : ContinuousOn (fun c => ∫ t in a..c, f t) (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using
      (intervalIntegral.continuousOn_primitive_interval' hf
        (show a ∈ uIcc a b by simp [hab.le]))
  have hlimG : Tendsto (fun c => ∫ t in a..c, g t) (𝓝[<] b)
      (𝓝 (∫ t in a..b, g t)) :=
    (by simpa only [nhdsWithin_Ioo_eq_nhdsLT hab] using
      ((hcontG.continuousWithinAt ⟨hab.le, le_rfl⟩).mono
        Ioo_subset_Icc_self).tendsto)
  have hlimF : Tendsto (fun c => ∫ t in a..c, f t) (𝓝[<] b)
      (𝓝 (∫ t in a..b, f t)) :=
    (by simpa only [nhdsWithin_Ioo_eq_nhdsLT hab] using
      ((hcontF.continuousWithinAt ⟨hab.le, le_rfl⟩).mono
        Ioo_subset_Icc_self).tendsto)
  have hevent : ∀ᶠ c in 𝓝[<] b,
      (∫ t in a..c, g t) ≤ |q c| + ∫ t in a..c, f t :=
    by
      filter_upwards [Ioo_mem_nhdsLT hab] with c hc
      exact hbound c hc
  have h := le_of_tendsto_of_tendsto hlimG (hq.abs.add hlimF) hevent
  simpa using h

/-- Identify an open-interval null integral with the variation of its
scalar primitive when the pointwise integrand is the absolute derivative. -/
theorem null_lintegral_eq_scalar_variation {a b : ℝ} (hab : a ≤ b)
    {g phi : ℝ → ℝ}
    (hphi : AbsolutelyContinuousOnInterval phi a b)
    (hpoint : ∀ t ∈ Ioo a b, g t = |deriv phi t|) :
    (∫⁻ t in Ioo a b, ENNReal.ofReal (g t)) =
      eVariationOn phi (Ioo a b) := by
  have hint : IntegrableOn (fun t => |deriv phi t|) (Ioo a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp
      hphi.intervalIntegrable_deriv.abs
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo a b)]
      (fun t => |deriv phi t|) :=
    Filter.Eventually.of_forall fun t => abs_nonneg _
  calc
    (∫⁻ t in Ioo a b, ENNReal.ofReal (g t)) =
        ∫⁻ t in Ioo a b, ENNReal.ofReal (|deriv phi t|) :=
      setLIntegral_congr_fun measurableSet_Ioo
        (fun t ht => congrArg ENNReal.ofReal (hpoint t ht))
    _ = ENNReal.ofReal (∫ t in Ioo a b, |deriv phi t|) :=
      (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
    _ = ENNReal.ofReal (∫ t in a..b, |deriv phi t|) := by
      rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
    _ = eVariationOn phi (Ioo a b) :=
      (AbsolutelyContinuousOnInterval.eVariationOn_Ioo_eq_integral_abs_deriv
        hab hphi).symm

end ChristodoulouBV

end
