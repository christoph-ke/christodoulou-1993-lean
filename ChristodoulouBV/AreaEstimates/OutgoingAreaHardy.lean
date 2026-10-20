module

public import ChristodoulouBV.AreaEstimates.OutgoingAreaTransport
public import ChristodoulouBV.ForMathlib.AbsolutelyContinuous.Calculus
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
# Finite interval Hardy estimate for the outgoing area

The radius in this estimate is squared. This is the integration by parts
step in (4.23), before passage to the axis endpoint.
-/

public section

open Set MeasureTheory Filter
open scoped Interval Topology ENNReal

namespace ChristodoulouBV

/-- On an interval away from the axis, a numerator satisfying `I' = R J`
obeys the terminal weighted inequality. No derivative of `|I|` at its zeros
is assumed. -/
theorem outgoing_area_finite_hardy
    {I R J : ℝ → ℝ} {a c : ℝ} (hac : a ≤ c)
    (hI : ContDiffOn ℝ 1 I (Icc a c))
    (hR : ContDiffOn ℝ 1 R (Icc a c))
    (hRpos : ∀ t ∈ Icc a c, 0 < R t)
    (hIderiv : ∀ t ∈ Ioo a c, deriv I t = R t * J t)
    (hJ : IntervalIntegrable (fun t => |J t|) volume a c) :
    (∫ t in a..c, |I t| * (-deriv R t) / R t ^ 2) ≤
      |I c| / R c + ∫ t in a..c, |J t| := by
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
  have hleft : (∫ t in a..c, F t * deriv G t) =
      ∫ t in a..c, |I t| * (-deriv R t) / R t ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume c] with t hne ht
    rw [uIoc_of_le hac] at ht
    have ht' : t ∈ Ioo a c := ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩
    rw [hGderiv t ht']
    dsimp [F]
    ring
  have hright : -(∫ t in a..c, deriv F t * G t) ≤
      ∫ t in a..c, |J t| := by
    rw [← intervalIntegral.integral_neg]
    have hfg : IntervalIntegrable (fun t => -(deriv F t * G t)) volume a c :=
      (hFAC.intervalIntegrable_deriv.mul_continuousOn hGAC.continuousOn).neg
    apply intervalIntegral.integral_mono_on_of_le_Ioo hac hfg hJ
    intro t ht
    have htIcc : t ∈ Icc a c := Ioo_subset_Icc_self ht
    have hIdiff : DifferentiableAt ℝ I t :=
      ((hI.differentiableOn (by norm_num)).mono Ioo_subset_Icc_self t ht)
        |>.differentiableAt (Ioo_mem_nhds ht.1 ht.2)
    have hderivAbs : -|deriv I t| ≤ deriv F t := by
      by_cases hz : I t = 0
      · have hmin : IsLocalMin F t := by
          change ∀ᶠ x in 𝓝 t, |I t| ≤ |I x|
          rw [hz, abs_zero]
          exact Filter.Eventually.of_forall fun x => abs_nonneg _
        rw [hmin.deriv_eq_zero]
        exact neg_nonpos.mpr (abs_nonneg _)
      · rcases lt_or_gt_of_ne hz with hn | hp
        · have hd := (hasDerivAt_abs_neg hn).comp t hIdiff.hasDerivAt
          have heq : deriv F t = -deriv I t := by
            simpa [F, Function.comp_def] using hd.deriv
          rw [heq]
          exact neg_le_neg (le_abs_self _)
        · have hd := (hasDerivAt_abs_pos hp).comp t hIdiff.hasDerivAt
          have heq : deriv F t = deriv I t := by
            simpa [F, Function.comp_def] using hd.deriv
          rw [heq]
          exact neg_abs_le _
    rw [hIderiv t ht, abs_mul, abs_of_pos (hRpos t htIcc)] at hderivAbs
    change -(deriv F t * (R t)⁻¹) ≤ |J t|
    have hInv : 0 < (R t)⁻¹ := inv_pos.mpr (hRpos t htIcc)
    have hdiv := mul_le_mul_of_nonneg_right hderivAbs hInv.le
    have hid : R t * (|J t| * (R t)⁻¹) = |J t| := by
      field_simp [ne_of_gt (hRpos t htIcc)]
    nlinarith only [hdiv, hid]
  rw [hleft] at hIBP
  have hFa : 0 ≤ F a := abs_nonneg _
  have hGa : 0 < G a := inv_pos.mpr (hRpos a ⟨le_rfl, hac⟩)
  have hFc : F c * G c = |I c| / R c := by
    dsimp [F, G]
    ring
  rw [hFc] at hIBP
  linarith only [hIBP, hright, mul_nonneg hFa hGa.le]

/-- A nonnegative finite-interval inequality passes to a terminal endpoint
when its boundary correction tends to zero. No integrability on the full
interval is assumed; the conclusion is an extended nonnegative integral
inequality and so also covers infinite right-hand side. -/
theorem outgoing_area_terminal_lintegral_bound
    {a b : ℝ} (hab : a < b) {g f q : ℝ → ℝ}
    (hg : ∀ t, 0 ≤ g t) (hf : ∀ t, 0 ≤ f t)
    (hgi : ∀ c ∈ Ioo a b, IntervalIntegrable g volume a c)
    (hfi : ∀ c ∈ Ioo a b, IntervalIntegrable f volume a c)
    (hq : Filter.Tendsto q (𝓝[<] b) (𝓝 (0 : ℝ)))
    (hbound : ∀ c ∈ Ioo a b,
      (∫ t in a..c, g t) ≤ |q c| + ∫ t in a..c, f t) :
    (∫⁻ t in Ioo a b, ENNReal.ofReal (g t)) ≤
      ∫⁻ t in Ioo a b, ENNReal.ofReal (f t) := by
  let c : ℕ → ℝ := fun n => b - (b - a) / ((n : ℝ) + 1)
  let E : ℕ → Set ℝ := fun n => Ioo a (c n)
  have hc_le (n : ℕ) : a ≤ c n := by
    dsimp [c]
    have hpos : (0 : ℝ) < n + 1 := by positivity
    have hden : (1 : ℝ) ≤ n + 1 := by
      have hnonneg : (0 : ℝ) ≤ n := by positivity
      linarith
    have hdiv := (div_le_iff₀ hpos).2
      (show b - a ≤ (b - a) * ((n : ℝ) + 1) from
        le_mul_of_one_le_right (sub_nonneg.mpr hab.le) hden)
    linarith only [hdiv]
  have hc_lt (n : ℕ) : c n < b := by
    dsimp [c]
    have : 0 < (b - a) / ((n : ℝ) + 1) :=
      div_pos (sub_pos.mpr hab) (by positivity)
    linarith only [this]
  have hc_lim : Filter.Tendsto c Filter.atTop (𝓝 b) := by
    have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (b - a))
    have hs := (tendsto_const_nhds (x := b)).sub h
    simpa only [c, div_eq_mul_inv, one_mul, mul_zero, sub_zero] using hs
  have hc_within : Filter.Tendsto c Filter.atTop (𝓝[<] b) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hc_lim, Filter.Eventually.of_forall fun n => hc_lt n⟩
  have hq_lim : Filter.Tendsto (fun n => |q (c n)|) Filter.atTop
      (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, abs_zero] using (hq.comp hc_within).abs
  have hc_mono : Monotone c := by
    intro n m hnm
    dsimp [c]
    have hden : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    have hpos : (0 : ℝ) < n + 1 := by positivity
    have hfrac : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le hpos hden
    have hmul := mul_le_mul_of_nonneg_left hfrac (sub_nonneg.mpr hab.le)
    simpa only [c, div_eq_mul_inv, mul_comm, one_mul] using sub_le_sub_left hmul b
  have hEmono : Monotone E := by
    intro n m hnm x hx
    exact ⟨hx.1, hx.2.trans_le (hc_mono hnm)⟩
  have hcover : (⋃ n, E n) = Ioo a b := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
      exact ⟨hxn.1, hxn.2.trans (hc_lt n)⟩
    · intro hx
      have hratio : 0 < (b - x) / (b - a) :=
        div_pos (sub_pos.mpr hx.2) (sub_pos.mpr hab)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hratio
      apply Set.mem_iUnion.mpr
      refine ⟨n, hx.1, ?_⟩
      have hden : (0 : ℝ) < n + 1 := by positivity
      have hprod := mul_lt_mul_of_pos_right hn (sub_pos.mpr hab)
      have hright : (b - x) / (b - a) * (b - a) = b - x := by
        field_simp [ne_of_gt (sub_pos.mpr hab)]
      rw [hright] at hprod
      change x < c n
      dsimp [c]
      have hmul : 1 / ((n : ℝ) + 1) * (b - a) =
          (b - a) / ((n : ℝ) + 1) := by ring
      rw [hmul] at hprod
      linarith only [hprod]
  have hdir : Directed (· ⊆ ·) E := by
    intro n m
    exact ⟨max n m, hEmono (le_max_left n m), hEmono (le_max_right n m)⟩
  have hfinite (n : ℕ) :
      (∫⁻ t in E n, ENNReal.ofReal (g t)) ≤
        ENNReal.ofReal |q (c n)| +
          ∫⁻ t in E n, ENNReal.ofReal (f t) := by
    by_cases hn : n = 0
    · subst n
      have hE : E 0 = ∅ := by simp [E, c]
      simp [hE]
    · have hcan : a < c n := by
        have hnpos : (0 : ℝ) < n := by
          exact_mod_cast Nat.pos_of_ne_zero hn
        have hden : (0 : ℝ) < n + 1 := by positivity
        have hmul : b - a < (b - a) * ((n : ℝ) + 1) := by
          nlinarith [mul_pos (sub_pos.mpr hab) hnpos]
        have hdiv : (b - a) / ((n : ℝ) + 1) < b - a :=
          (div_lt_iff₀ hden).2 hmul
        dsimp [c]
        linarith only [hdiv]
      have hcn : c n ∈ Ioo a b := ⟨hcan, hc_lt n⟩
      have hgOn : IntegrableOn g (Ioo a (c n)) :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le hcan.le).mp (hgi (c n) hcn)
      have hfOn : IntegrableOn f (Ioo a (c n)) :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le hcan.le).mp (hfi (c n) hcn)
      have hgCast : (∫⁻ t in E n, ENNReal.ofReal (g t)) =
          ENNReal.ofReal (∫ t in a..c n, g t) := by
        rw [intervalIntegral.integral_of_le hcan.le,
          integral_Ioc_eq_integral_Ioo]
        exact (ofReal_integral_eq_lintegral_ofReal hgOn
          (Filter.Eventually.of_forall fun t => hg t)).symm
      have hfCast : (∫⁻ t in E n, ENNReal.ofReal (f t)) =
          ENNReal.ofReal (∫ t in a..c n, f t) := by
        rw [intervalIntegral.integral_of_le hcan.le,
          integral_Ioc_eq_integral_Ioo]
        exact (ofReal_integral_eq_lintegral_ofReal hfOn
          (Filter.Eventually.of_forall fun t => hf t)).symm
      have hfin0 : 0 ≤ ∫ t in a..c n, f t :=
        intervalIntegral.integral_nonneg hcan.le (fun t _ => hf t)
      rw [hgCast, hfCast, ← ENNReal.ofReal_add (abs_nonneg _) hfin0]
      exact ENNReal.ofReal_le_ofReal (hbound (c n) hcn)
  have htarget : ∀ ε : NNReal, 0 < ε →
      (∫⁻ t in Ioo a b, ENNReal.ofReal (f t)) < ∞ →
      (∫⁻ t in Ioo a b, ENNReal.ofReal (g t)) ≤
        (∫⁻ t in Ioo a b, ENNReal.ofReal (f t)) + ε := by
    intro ε hε _
    have hεreal : (0 : ℝ) < (ε : ℝ) := hε
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        ENNReal.ofReal |q (c n)| ≤ (ε : ℝ≥0∞) := by
      have hEv := hq_lim.eventually (Iio_mem_nhds hεreal)
      filter_upwards [hEv] with n hn
      have hnonneg : 0 ≤ |q (c n)| := abs_nonneg _
      simpa only [ENNReal.ofReal_coe_nnreal] using
        ENNReal.ofReal_le_ofReal hn.le
    have hm (m : ℕ) :
        (∫⁻ t in E m, ENNReal.ofReal (g t)) ≤
          (∫⁻ t in Ioo a b, ENNReal.ofReal (f t)) + ε := by
      obtain ⟨n, hmn, hεn⟩ :=
        ((Filter.eventually_ge_atTop m).and hev).exists
      calc
        (∫⁻ t in E m, ENNReal.ofReal (g t)) ≤
            ∫⁻ t in E n, ENNReal.ofReal (g t) :=
          lintegral_mono_set (hEmono hmn)
        _ ≤ ENNReal.ofReal |q (c n)| +
              ∫⁻ t in E n, ENNReal.ofReal (f t) := hfinite n
        _ ≤ ε + ∫⁻ t in Ioo a b, ENNReal.ofReal (f t) :=
          add_le_add hεn (lintegral_mono_set (by
            intro t ht
            exact ⟨ht.1, ht.2.trans (hc_lt n)⟩))
        _ = _ := by ac_rfl
    calc
      (∫⁻ t in Ioo a b, ENNReal.ofReal (g t)) =
          ∫⁻ t in ⋃ n, E n, ENNReal.ofReal (g t) := by rw [hcover]
      _ = ⨆ n, ∫⁻ t in E n, ENNReal.ofReal (g t) :=
        setLIntegral_iUnion_of_directed _ hdir
      _ ≤ _ := iSup_le hm
  exact ENNReal.le_of_forall_pos_le_add htarget

end ChristodoulouBV

end
