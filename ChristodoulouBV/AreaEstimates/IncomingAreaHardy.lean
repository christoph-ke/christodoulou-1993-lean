module

public import ChristodoulouBV.AreaEstimates.IncomingAreaTransport
import Mathlib.Tactic

/-!
# Forward Hardy inequality for the incoming area

The boundary term at the lower endpoint is retained until the outgoing-axis
limit is taken.
-/

public section

open Set MeasureTheory
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

/-- A numerator satisfying `I' = R J` on a forward interval obeys the
weighted inequality with its lower-endpoint boundary term. -/
theorem incoming_area_finite_hardy
    {I R J : ℝ → ℝ} {a c : ℝ} (hac : a ≤ c)
    (hI : ContDiffOn ℝ 1 I (Icc a c))
    (hR : ContDiffOn ℝ 1 R (Icc a c))
    (hRpos : ∀ t ∈ Icc a c, 0 < R t)
    (hIderiv : ∀ t ∈ Ioo a c, deriv I t = R t * J t)
    (hJ : IntervalIntegrable (fun t => |J t|) volume a c) :
    (∫ t in a..c, |I t| * deriv R t / R t ^ 2) ≤
      |I a| / R a + ∫ t in a..c, |J t| := by
  let F : ℝ → ℝ := fun t => |I t|
  let G : ℝ → ℝ := fun t => (R t)⁻¹
  have hIAC : AbsolutelyContinuousOnInterval I a c :=
    (show ContDiffOn ℝ 1 I (uIcc a c) by
      simpa only [uIcc_of_le hac] using hI).absolutelyContinuousOnInterval
  have hFAC : AbsolutelyContinuousOnInterval F a c := by
    have hlip : LipschitzWith 1 (fun z : ℝ => |z|) := by
      convert (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)) using 1
    exact hlip.comp_absolutelyContinuousOnInterval hIAC
  have hGdiff : ContDiffOn ℝ 1 G (Icc a c) :=
    hR.inv (fun t ht => ne_of_gt (hRpos t ht))
  have hGAC : AbsolutelyContinuousOnInterval G a c :=
    (show ContDiffOn ℝ 1 G (uIcc a c) by
      simpa only [uIcc_of_le hac] using hGdiff).absolutelyContinuousOnInterval
  have hIBP := hFAC.integral_mul_deriv_eq_deriv_mul hGAC
  have hGderiv : ∀ t ∈ Ioo a c,
      deriv G t = -deriv R t / (R t) ^ 2 := by
    intro t ht
    have hdiff : DifferentiableAt ℝ R t :=
      ((hR.differentiableOn (by norm_num)).mono Ioo_subset_Icc_self t ht)
        |>.differentiableAt (Ioo_mem_nhds ht.1 ht.2)
    exact deriv_fun_inv'' hdiff (ne_of_gt (hRpos t (Ioo_subset_Icc_self ht)))
  have hleft : -(∫ t in a..c, F t * deriv G t) =
      ∫ t in a..c, |I t| * deriv R t / R t ^ 2 := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume c] with t hne ht
    rw [uIoc_of_le hac] at ht
    have ht' : t ∈ Ioo a c := ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩
    rw [hGderiv t ht']
    dsimp [F]
    ring
  have hright : (∫ t in a..c, deriv F t * G t) ≤
      ∫ t in a..c, |J t| := by
    have hfg : IntervalIntegrable (fun t => deriv F t * G t) volume a c :=
      hFAC.intervalIntegrable_deriv.mul_continuousOn hGAC.continuousOn
    apply intervalIntegral.integral_mono_on_of_le_Ioo hac hfg hJ
    intro t ht
    have htIcc : t ∈ Icc a c := Ioo_subset_Icc_self ht
    have hIdiff : DifferentiableAt ℝ I t :=
      ((hI.differentiableOn (by norm_num)).mono Ioo_subset_Icc_self t ht)
        |>.differentiableAt (Ioo_mem_nhds ht.1 ht.2)
    have hderivAbs : deriv F t ≤ |deriv I t| := by
      by_cases hz : I t = 0
      · have hmin : IsLocalMin F t := by
          change ∀ᶠ x in 𝓝 t, |I t| ≤ |I x|
          rw [hz, abs_zero]
          exact Filter.Eventually.of_forall fun x => abs_nonneg _
        rw [hmin.deriv_eq_zero]
        exact abs_nonneg _
      · rcases lt_or_gt_of_ne hz with hn | hp
        · have hd := (hasDerivAt_abs_neg hn).comp t hIdiff.hasDerivAt
          have heq : deriv F t = -deriv I t := by
            simpa [F, Function.comp_def] using hd.deriv
          rw [heq]
          exact neg_le_abs _
        · have hd := (hasDerivAt_abs_pos hp).comp t hIdiff.hasDerivAt
          have heq : deriv F t = deriv I t := by
            simpa [F, Function.comp_def] using hd.deriv
          rw [heq]
          exact le_abs_self _
    rw [hIderiv t ht, abs_mul, abs_of_pos (hRpos t htIcc)] at hderivAbs
    change deriv F t * (R t)⁻¹ ≤ |J t|
    have hInv : 0 < (R t)⁻¹ := inv_pos.mpr (hRpos t htIcc)
    have hdiv := mul_le_mul_of_nonneg_right hderivAbs hInv.le
    have hid : R t * (|J t| * (R t)⁻¹) = |J t| := by
      field_simp [ne_of_gt (hRpos t htIcc)]
    nlinarith only [hdiv, hid]
  rw [← hleft]
  have hFc : 0 ≤ F c := abs_nonneg _
  have hGc : 0 < G c := inv_pos.mpr (hRpos c ⟨hac, le_rfl⟩)
  have hFa : F a * G a = |I a| / R a := by
    dsimp [F, G]
    ring
  rw [hFa] at hIBP
  linarith only [hIBP, hright, mul_nonneg hFc hGc.le]

end ChristodoulouBV

end
