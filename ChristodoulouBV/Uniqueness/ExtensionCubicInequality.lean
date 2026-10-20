module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Tactic

/-!
# A weighted cubic inequality on a finite interval

This is the one-variable inequality (5.7) in Christodoulou's extension proof.
The hypotheses are the energy average and weighted derivative bounds on a
finite radius interval.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

private theorem weighted_square_integral_bound
    {δ R a : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 ≤ R) (ha : 0 ≤ a)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 R))
    (henergy : ∀ t ∈ Ioc 0 R, (∫ s in 0..t, (f s) ^ 2) / t ≤ a) :
    ∀ r ∈ Icc 0 R,
      (∫ t in 0..r, t^(-δ) * (f t)^2) ≤ a * r^(1-δ) / (1-δ) := by
  intro r hr
  rcases eq_or_lt_of_le hr.1 with hr0 | hr0
  · subst r
    simp [Real.zero_rpow (by linarith : (1 - δ) ≠ 0)]
  have hrR : r ≤ R := hr.2
  have hfr : ContinuousOn (fun t => (f t)^2) (Icc 0 R) := hf.pow 2
  have hfi : IntervalIntegrable (fun t => (f t)^2) volume 0 R :=
    hfr.intervalIntegrable_of_Icc hR
  let G : ℝ → ℝ := fun t => ∫ s in 0..t, (f s)^2
  have hGac : AbsolutelyContinuousOnInterval G 0 R := by
    exact hfi.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp [hR])
  have hGbound : ∀ t ∈ Ioc 0 R, G t ≤ a * t := by
    intro t ht
    have ht0 : 0 < t := ht.1
    exact (div_le_iff₀ ht0).mp (henergy t ht)
  have hGnonneg : ∀ t ∈ Icc 0 R, 0 ≤ G t := by
    intro t ht
    exact intervalIntegral.integral_nonneg ht.1 (fun s _ => sq_nonneg _)
  have hwint : IntervalIntegrable (fun t => t^(-δ)) volume 0 r :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hFint : IntervalIntegrable (fun t => t^(-δ) * (f t)^2) volume 0 r :=
    hwint.mul_continuousOn (hfr.mono (by
      rw [uIcc_of_le hr0.le]
      exact Icc_subset_Icc le_rfl hrR))
  have hFcont : ContinuousOn (fun c => ∫ t in 0..c, t^(-δ) * (f t)^2)
      (Icc 0 r) := by
    have hac := hFint.absolutelyContinuousOnInterval_intervalIntegral (c := 0)
      (by simp [hr0.le])
    simpa only [uIcc_of_le hr0.le] using hac.continuousOn
  have htail : Tendsto (fun c => ∫ t in c..r, t^(-δ) * (f t)^2)
      (𝓝[>] 0) (𝓝 (∫ t in 0..r, t^(-δ) * (f t)^2)) := by
    have hmem : Icc 0 r ∈ 𝓝[>] (0 : ℝ) :=
      mem_of_superset (Ioc_mem_nhdsGT hr0) Ioc_subset_Icc_self
    have hprim := (hFcont.continuousWithinAt (by simp [hr0.le])).mono_of_mem_nhdsWithin hmem
    have hzero : Tendsto (fun c => ∫ t in 0..c, t^(-δ) * (f t)^2)
        (𝓝[>] 0) (𝓝 0) := by
      change Tendsto (fun c => ∫ t in 0..c, t^(-δ) * (f t)^2)
        (𝓝[>] 0) (𝓝 (∫ t in 0..0, t^(-δ) * (f t)^2)) at hprim
      simpa using hprim
    have heq : ∀ᶠ c in 𝓝[>] (0 : ℝ),
        (∫ t in c..r, t^(-δ) * (f t)^2) =
          (∫ t in 0..r, t^(-δ) * (f t)^2) -
          (∫ t in 0..c, t^(-δ) * (f t)^2) := by
      filter_upwards [Ioc_mem_nhdsGT hr0] with c hc
      have hleft : IntervalIntegrable (fun t => t^(-δ) * (f t)^2) volume 0 c := by
        apply hFint.mono_set
        rw [uIcc_of_le hc.1.le, uIcc_of_le hr0.le]
        exact Icc_subset_Icc le_rfl hc.2
      have hright : IntervalIntegrable (fun t => t^(-δ) * (f t)^2) volume c r := by
        apply hFint.mono_set
        rw [uIcc_of_le hc.2, uIcc_of_le hr0.le]
        exact Icc_subset_Icc hc.1.le le_rfl
      linarith [intervalIntegral.integral_add_adjacent_intervals hleft hright]
    have hlim := (tendsto_const_nhds (x := ∫ t in 0..r, t^(-δ) * (f t)^2)).sub hzero
    simpa using hlim.congr' (heq.mono fun _ hc => hc.symm)
  apply le_of_tendsto htail
  filter_upwards [Ioc_mem_nhdsGT hr0] with c hc
  have hcpos : 0 < c := hc.1
  have hcr : c ≤ r := hc.2
  have hGI : AbsolutelyContinuousOnInterval G c r := by
    apply hGac.mono
    rw [uIcc_of_le hcr, uIcc_of_le hR]
    exact Icc_subset_Icc hcpos.le hrR
  have hWc : ContDiffOn ℝ 1 (fun t : ℝ => t^(-δ)) (Icc c r) := by
    apply ContDiffOn.rpow_const_of_ne contDiffOn_id
    intro t ht
    exact ne_of_gt (hcpos.trans_le ht.1)
  have hWI : AbsolutelyContinuousOnInterval (fun t : ℝ => t^(-δ)) c r := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hcr] using hWc
  have hDg : ∀ᵐ t ∂volume, t ∈ uIoc c r → deriv G t = (f t)^2 := by
    filter_upwards [hfi.ae_hasDerivAt_integral] with t ht htu
    have hsub : uIcc c r ⊆ uIcc 0 R := by
      rw [uIcc_of_le hcr, uIcc_of_le hR]
      exact Icc_subset_Icc hcpos.le hrR
    exact (ht (hsub (uIoc_subset_uIcc htu)) 0 (by simp [hR])).deriv
  have hDw : ∀ t ∈ uIcc c r,
      deriv (fun x : ℝ => x^(-δ)) t = (-δ) * t^(-δ-1) := by
    intro t ht
    have ht' : t ∈ Icc c r := by simpa only [uIcc_of_le hcr] using ht
    exact Real.deriv_rpow_const t (-δ)
  have hIBP := hGI.integral_mul_deriv_eq_deriv_mul hWI
  have hleft :
      (∫ t in c..r, G t * deriv (fun x : ℝ => x^(-δ)) t) =
      ∫ t in c..r, G t * ((-δ) * t^(-δ-1)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    change G t * deriv (fun x : ℝ => x^(-δ)) t = G t * ((-δ) * t^(-δ-1))
    rw [hDw t ht]
  have hright :
      (∫ t in c..r, deriv G t * t^(-δ)) =
      ∫ t in c..r, t^(-δ) * (f t)^2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hDg] with t ht htu
    rw [ht htu]
    ring
  rw [hleft, hright] at hIBP
  have hGrr : G r ≤ a * r := hGbound r ⟨hr0, hrR⟩
  have hGn : 0 ≤ G c := hGnonneg c ⟨hcpos.le, hc.2.trans hrR⟩
  have hwc : 0 ≤ c^(-δ) := Real.rpow_nonneg hcpos.le _
  have hwr : 0 ≤ r^(-δ) := Real.rpow_nonneg hr0.le _
  have hIntG : IntervalIntegrable (fun t => G t * t^(-δ-1)) volume c r := by
    have hw : IntervalIntegrable (fun t => t^(-δ-1)) volume c r :=
      intervalIntegral.intervalIntegrable_rpow (Or.inr (by
        rw [uIcc_of_le hcr]
        intro h0
        exact (lt_irrefl (0 : ℝ)) (lt_of_lt_of_le hcpos h0.1)))
    exact hw.continuousOn_mul (hGI.continuousOn)
  have hIntP : IntervalIntegrable (fun t => a * t^(-δ)) volume c r := by
    have hw : IntervalIntegrable (fun t => t^(-δ)) volume c r :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    simpa [mul_comm] using hw.mul_continuousOn continuousOn_const
  have hGp : (∫ t in c..r, G t * t^(-δ-1)) ≤
      ∫ t in c..r, a * t^(-δ) := by
    apply intervalIntegral.integral_mono_on hcr hIntG hIntP
    intro t ht
    have htpos : 0 < t := hcpos.trans_le ht.1
    have hGt : G t ≤ a * t := hGbound t ⟨htpos, ht.2.trans hrR⟩
    have hpow : t * t^(-δ-1) = t^(-δ) := by
      calc
        t * t^(-δ-1) = t^1 * t^(-δ-1) := by rw [Real.rpow_one]
        _ = t^(1 + (-δ-1)) := (Real.rpow_add htpos _ _).symm
        _ = t^(-δ) := by congr 1; ring
    calc
      G t * t^(-δ-1) ≤ (a*t) * t^(-δ-1) :=
        mul_le_mul_of_nonneg_right hGt (Real.rpow_nonneg htpos.le _)
      _ = a * t^(-δ) := by rw [mul_assoc, hpow]
  have hPow : (∫ t in c..r, t^(-δ)) =
      (r^(1-δ) - c^(1-δ)) / (1-δ) := by
    convert integral_rpow (a := c) (b := r) (r := -δ) (Or.inl (by linarith)) using 1
    ring_nf
  have hcPow : 0 ≤ c^(1-δ) := Real.rpow_nonneg hcpos.le _
  have hPowR : r * r^(-δ) = r^(1-δ) := by
    calc
      r * r^(-δ) = r^1 * r^(-δ) := by rw [Real.rpow_one]
      _ = r^(1 + -δ) := (Real.rpow_add hr0 _ _).symm
      _ = r^(1-δ) := by congr 1
  have hδpos : 0 < 1-δ := by linarith
  have hmain : (∫ t in c..r, t^(-δ) * (f t)^2) ≤
      a * r^(-δ) * r + δ * (∫ t in c..r, a * t^(-δ)) := by
    have hterm : 0 ≤ G c * c^(-δ) := mul_nonneg hGn hwc
    have hGterm : G r * r^(-δ) ≤ (a*r) * r^(-δ) :=
      mul_le_mul_of_nonneg_right hGrr hwr
    have hI : (∫ t in c..r, G t * ((-δ) * t^(-δ-1))) =
        (-δ) * (∫ t in c..r, G t * t^(-δ-1)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      ring
    rw [hI] at hIBP
    have hGint := mul_le_mul_of_nonneg_left hGp hδ₀.le
    rw [intervalIntegral.integral_const_mul] at hGint ⊢
    nlinarith
  rw [intervalIntegral.integral_const_mul, hPow] at hmain
  have hmain' : (∫ t in c..r, t^(-δ) * (f t)^2) ≤
      a * r^(1-δ) + δ * a * ((r^(1-δ) - c^(1-δ)) / (1-δ)) := by
    nlinarith [hmain, hPowR]
  apply hmain'.trans
  apply (le_div_iff₀ hδpos).mpr
  have hdiv : ((r^(1-δ) - c^(1-δ)) / (1-δ)) * (1-δ) =
      r^(1-δ) - c^(1-δ) := div_mul_cancel₀ _ hδpos.ne'
  have hnum :
      (a * r^(1-δ) + δ * a * ((r^(1-δ) - c^(1-δ)) / (1-δ))) * (1-δ) =
        a * r^(1-δ) - δ * a * c^(1-δ) := by
    calc
      _ = a * r^(1-δ) * (1-δ) + δ * a *
            (((r^(1-δ) - c^(1-δ)) / (1-δ)) * (1-δ)) := by ring
      _ = a * r^(1-δ) - δ * a * c^(1-δ) := by rw [hdiv]; ring
  rw [hnum]
  nlinarith [mul_nonneg hδ₀.le (mul_nonneg ha hcPow)]


/-- Christodoulou's weighted cubic inequality (5.7) on a finite radius interval. -/
theorem cubic_weighted_interval_bound
    {δ rStar a b : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hr : 0 ≤ rStar) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Icc 0 rStar))
    (hf0 : f 0 = 0)
    (henergy : ∀ r ∈ Set.Ioc 0 rStar,
      (∫ t in 0..r, (f t) ^ 2) / r ≤ a)
    (hderiv : ∀ r ∈ Set.Ioo 0 rStar,
      r ^ δ * |deriv f r| ≤ b) :
    ∀ r ∈ Set.Icc 0 rStar,
      |f r|^3 ≤ 3 * a * b * r^(1-δ) / (1-δ) := by
  intro r hrr
  rcases eq_or_lt_of_le hrr.1 with hr0 | hr0
  · subst r
    simp [hf0, Real.zero_rpow (by linarith : (1 - δ) ≠ 0)]
  have hrR : r ≤ rStar := hrr.2
  have hfc : ContDiffOn ℝ 1 f (Icc 0 r) :=
    hf.mono (Icc_subset_Icc le_rfl hrR)
  have hfcube : ContDiffOn ℝ 1 (fun t => (f t)^3) (Icc 0 r) := hfc.pow 3
  have hAC : AbsolutelyContinuousOnInterval (fun t => (f t)^3) 0 r := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hr0.le] using hfcube
  have hDint : IntervalIntegrable (fun t => deriv (fun s => (f s)^3) t) volume 0 r :=
    hAC.intervalIntegrable_deriv
  have hAbsInt : IntervalIntegrable (fun t => |deriv (fun s => (f s)^3) t|) volume 0 r :=
    hDint.abs
  have hfi : IntervalIntegrable (fun t => t^(-δ) * (f t)^2) volume 0 r :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -δ)).mul_continuousOn
      ((hf.continuousOn.pow 2).mono (by
        rw [uIcc_of_le hr0.le]
        exact Icc_subset_Icc le_rfl hrR))
  have hBoundInt : IntervalIntegrable (fun t => (3*b) * (t^(-δ) * (f t)^2)) volume 0 r :=
    hfi.const_mul _
  have hIntLe : (∫ t in 0..r, |deriv (fun s => (f s)^3) t|) ≤
      ∫ t in 0..r, (3*b) * (t^(-δ) * (f t)^2) := by
    rw [intervalIntegral.integral_of_le hr0.le, intervalIntegral.integral_of_le hr0.le]
    apply MeasureTheory.integral_mono_ae
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hr0.le).mp hAbsInt
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hr0.le).mp hBoundInt
    · filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume r),
        ae_restrict_mem measurableSet_Ioc] with t hne ht
      have htr : t ∈ Ioo 0 r := ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩
      have htR : t ∈ Ioo 0 rStar := ⟨htr.1, htr.2.trans_le hrR⟩
      have hdiff : DifferentiableAt ℝ f t :=
        (hf.differentiableOn (by norm_num)) t ⟨htR.1.le, htR.2.le⟩ |>.differentiableAt
          (Icc_mem_nhds htR.1 htR.2)
      have hDcube : deriv (fun s => (f s)^3) t = 3 * (f t)^2 * deriv f t := by
        convert (hdiff.hasDerivAt.pow 3).deriv using 1
      have hpow : t^δ * t^(-δ) = 1 := by
        rw [← Real.rpow_add htr.1]
        simp
      have hD : |deriv f t| ≤ b * t^(-δ) := by
        have h := mul_le_mul_of_nonneg_right (hderiv t htR)
          (Real.rpow_nonneg htr.1.le (-δ))
        calc
          |deriv f t| = (t^δ * |deriv f t|) * t^(-δ) := by
            rw [mul_assoc, mul_comm (|deriv f t|), ← mul_assoc, hpow, one_mul]
          _ ≤ b * t^(-δ) := h
      rw [hDcube, abs_mul, abs_mul]
      have hnonneg : 0 ≤ (f t)^2 := sq_nonneg _
      have hpowNonneg : 0 ≤ t^(-δ) := Real.rpow_nonneg htr.1.le _
      simp only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3),
        abs_of_nonneg hnonneg]
      nlinarith [mul_le_mul_of_nonneg_left hD (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hnonneg)]
  have hFTC : (∫ t in 0..r, deriv (fun s => (f s)^3) t) = (f r)^3 := by
    rw [hAC.integral_deriv_eq_sub, hf0]
    norm_num
  have hpoint : |f r|^3 = |(f r)^3| := (abs_pow _ _).symm
  calc
    |f r|^3 = |∫ t in 0..r, deriv (fun s => (f s)^3) t| := by rw [hpoint, hFTC]
    _ ≤ (∫ t in 0..r, |deriv (fun s => (f s)^3) t|) :=
      intervalIntegral.abs_integral_le_integral_abs hr0.le
    _ ≤ ∫ t in 0..r, (3*b) * (t^(-δ) * (f t)^2) := hIntLe
    _ = (3*b) * (∫ t in 0..r, t^(-δ) * (f t)^2) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (3*b) * (a * r^(1-δ) / (1-δ)) := by
      exact mul_le_mul_of_nonneg_left
        (weighted_square_integral_bound hδ₀ hδ₁ hr ha hf.continuousOn henergy r hrr)
        (by positivity)
    _ = 3 * a * b * r^(1-δ) / (1-δ) := by ring

end ChristodoulouBV.Uniqueness

end
