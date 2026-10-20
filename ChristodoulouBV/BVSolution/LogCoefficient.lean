module

public import ChristodoulouBV.BVSolution.AxisTraces
public import ChristodoulouBV.BVSolution.CoefficientBounds
public import ChristodoulouBV.ForMathlib.AbsolutelyContinuous.Log
import ChristodoulouBV.ForMathlib.BoundedVariation.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Logarithmic mass-gap calculus and outgoing coefficient estimates

The mass-ratio derivative is an almost-everywhere identity on off-axis
compact intervals. The logarithm is handled by absolute continuity.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.IsBVSolution

/-- The logarithmic mass gap is absolutely continuous on every compact
off-axis outgoing interval. -/
theorem log_mass_gap_ac_out
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v a b : ℝ} (huv : (u, v) ∈ U) (hua : u < a)
    (hab : a ≤ b) (hbv : b ≤ v) :
    AbsolutelyContinuousOnInterval
      (fun t => Real.log (1 - 2 * S.m u t / S.r u t)) a b := by
  have hq := h.mass_div_radius_ac_out huv hua hab hbv
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  have hgap : AbsolutelyContinuousOnInterval
      (fun t => 1 - 2 * S.m u t / S.r u t) a b := by
    convert hconst.sub (hq.const_mul 2) using 1
    funext t
    simp only [Pi.sub_apply]
    ring
  obtain ⟨δ, hδ, hlow⟩ := h.exists_mass_gap_ratio_lower_out huv hua hab hbv
  exact (hgap.log_and_ae_deriv hδ (by
    simpa only [uIcc_of_le hab] using hlow)).1

/-- Almost everywhere on a compact outgoing interval, the logarithmic mass
gap derivative differs from the radial coefficient by the scalar square. -/
theorem log_mass_gap_ae_deriv_out
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v a b : ℝ} (huv : (u, v) ∈ U) (hua : u < a)
    (hab : a ≤ b) (hbv : b ≤ v) :
    ∀ᵐ t ∂volume, t ∈ Icc a b →
      deriv (fun s => Real.log (1 - 2 * S.m u s / S.r u s)) t =
        nuCoeff S u t - S.theta u t ^ 2 / (S.lam u t * S.r u t) := by
  have hq := h.mass_div_radius_ac_out huv hua hab hbv
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  have hgap : AbsolutelyContinuousOnInterval
      (fun t => 1 - 2 * S.m u t / S.r u t) a b := by
    convert hconst.sub (hq.const_mul 2) using 1
    funext t
    simp only [Pi.sub_apply]
    ring
  obtain ⟨δ, hδ, hlow⟩ := h.exists_mass_gap_ratio_lower_out huv hua hab hbv
  have hlog := (hgap.log_and_ae_deriv hδ (by
    simpa only [uIcc_of_le hab] using hlow)).2
  filter_upwards [hlog, h.mass_ratio_ae_deriv_out huv hua hab hbv]
    with t hlog' hq' ht
  have htU := h.solution.development.outgoing_mem huv
    (hua.trans_le ht.1) (ht.2.trans hbv)
  have hr : S.r u t ≠ 0 := ne_of_gt (h.solution.radius_pos (u, t) htU)
  have hl : S.lam u t ≠ 0 := ne_of_gt (h.solution.lam_pos (u, t) htU)
  have hg : 1 - 2 * S.m u t / S.r u t ≠ 0 := by
    have := (h.mass_ratio_bounds htU).2
    linarith
  have hg' : S.r u t - 2 * S.m u t ≠ 0 := by
    intro hzero
    apply hg
    have hratio : 2 * S.m u t / S.r u t = 1 := by
      apply (div_eq_iff hr).2
      linarith
    linarith
  have hDer : deriv (fun s => 1 - 2 * S.m u s / S.r u s) t =
      -2 * deriv (fun s => S.m u s / S.r u s) t := by
    have hfun : (fun s => 1 - 2 * S.m u s / S.r u s) =
        (fun s => 1 - 2 * (S.m u s / S.r u s)) := by
      funext s
      ring
    rw [hfun, deriv_const_sub, deriv_const_mul_field]
    ring
  rw [uIcc_of_le hab] at hlog'
  rw [hlog' ht, hDer, hq' ht]
  unfold massV nuCoeff gap
  field_simp [hr, hl, hg, hg']
  ring

/-- The outgoing coefficient bound on a compact off-axis interval, retaining
the logarithmic boundary contribution at both ends. -/
theorem eq3_1a_compact
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v a b M : ℝ} (huv : (u, v) ∈ U) (hua : u < a)
    (hab : a ≤ b) (hbv : b ≤ v)
    (hM : ∀ t ∈ Ioc a b, |S.theta u t / S.lam u t| ≤ M) :
    (∫ t in a..b, nuCoeff S u t) ≤
      Real.log (1 - 2 * S.m u b / S.r u b) -
        Real.log (1 - 2 * S.m u a / S.r u a) +
        M * (eVariationOn (S.phi u) (Ioc a b)).toReal := by
  have hD := h.solution.development
  have hseg := hD.out_seg_subset huv hua hab hbv
  have hφAC := h.item3_ac_out u a b hab hseg
  have hlogAC := h.log_mass_gap_ac_out huv hua hab hbv
  have hcoeffInt := nu_coeff_integrable hD h huv hua hab hbv
  have hlogInt := hlogAC.intervalIntegrable_deriv
  have hφInt := hφAC.intervalIntegrable_deriv.abs
  have hupperInt := hlogInt.add (hφInt.const_mul M)
  have hae : ∀ᵐ t ∂volume.restrict (Icc a b),
      nuCoeff S u t ≤
        deriv (fun s => Real.log (1 - 2 * S.m u s / S.r u s)) t +
          M * |deriv (S.phi u) t| := by
    rw [← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [h.log_mass_gap_ae_deriv_out huv hua hab hbv,
      h.scalar_ae_deriv_out huv hua hab hbv] with t hlog hφ ht
    have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
    have htU := hD.outgoing_mem huv
      (hua.trans_le ht'.1) (ht'.2.trans hbv)
    have hl : 0 < S.lam u t := h.solution.lam_pos (u, t) htU
    have hr : 0 < S.r u t := h.solution.radius_pos (u, t) htU
    have hsquare : S.theta u t ^ 2 / (S.lam u t * S.r u t) =
        |S.theta u t / S.lam u t| * |S.theta u t / S.r u t| := by
      rw [abs_div, abs_div, abs_of_pos hl, abs_of_pos hr]
      field_simp
      nlinarith [sq_abs (S.theta u t)]
    have hbound := hM t ⟨ht.1, ht.2.le⟩
    rw [hlog ht', hφ ht', hsquare]
    have hmul := mul_le_mul_of_nonneg_right hbound
      (abs_nonneg (S.theta u t / S.r u t))
    linarith only [hmul]
  have hle := intervalIntegral.integral_mono_ae_restrict hab hcoeffInt
    hupperInt hae
  have hvar := hφAC.eVariationOn_Ioc_eq_integral_abs_deriv hab
  have hvarReal : (eVariationOn (S.phi u) (Ioc a b)).toReal =
      ∫ t in a..b, |deriv (S.phi u) t| := by
    rw [hvar, ENNReal.toReal_ofReal]
    exact intervalIntegral.integral_nonneg_of_forall hab (fun t => abs_nonneg _)
  rw [intervalIntegral.integral_add hlogInt (hφInt.const_mul M),
    hlogAC.integral_deriv_eq_sub, intervalIntegral.integral_const_mul,
    ← hvarReal] at hle
  exact hle

/-- The outgoing radial coefficient is integrable on the complete half-open
axis-to-point interval when its scalar ratio has a finite bound there. -/
theorem nu_coeff_integrable_axis
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v M : ℝ} (huv : (u, v) ∈ U)
    (hM : ∀ t ∈ Ioc u v, |S.theta u t / S.lam u t| ≤ M) :
    IntegrableOn (nuCoeff S u) (Ioc u v) := by
  have huvlt : u < v := (h.solution.development.wedge huv).2
  have hMnonneg : 0 ≤ M := (abs_nonneg _).trans (hM v ⟨huvlt, le_rfl⟩)
  have haxis := h.mass_ratio_tendsto_zero_axis_out huv
  have hlogAxis : Tendsto
      (fun a => Real.log (1 - 2 * S.m u a / S.r u a))
      (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    have hgap : Tendsto (fun a => 1 - 2 * S.m u a / S.r u a)
        (𝓝[>] u) (𝓝 (1 : ℝ)) := by
      simpa using (tendsto_const_nhds.sub haxis)
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hgap
  obtain ⟨C, hvarOut, _⟩ := h.item3_variation
  have hslice : Ioc u v ⊆ {t | (u, t) ∈ U} := by
    intro t ht
    exact h.solution.development.outgoing_mem huv ht.1 ht.2
  have hvarFinite : eVariationOn (S.phi u) (Ioc u v) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((eVariationOn.mono (S.phi u) hslice).trans (hvarOut u))
  let V : ℝ := (eVariationOn (S.phi u) (Ioc u v)).toReal
  have hVnonneg : 0 ≤ V := ENNReal.toReal_nonneg
  let a : ℕ → ℝ := fun n => u + (v - u) * (1 / ((n : ℝ) + 1))
  have hau (n : ℕ) : u < a n := by
    dsimp [a]
    have hp : 0 < ((n : ℝ) + 1) := by positivity
    have hd : 0 < (v - u) * (1 / ((n : ℝ) + 1)) :=
      mul_pos (sub_pos.mpr huvlt) (one_div_pos.mpr hp)
    linarith
  have hav (n : ℕ) : a n ≤ v := by
    dsimp [a]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hp : 1 ≤ ((n : ℝ) + 1) := by linarith
    have hone : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_iff₀ (by positivity)).2 (by linarith)
    nlinarith [mul_nonneg (sub_pos.mpr huvlt).le (sub_nonneg.mpr hone)]
  have ha : Tendsto a atTop (𝓝 u) := by
    have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hconstu : Tendsto (fun _ : ℕ => u) atTop (𝓝 u) := tendsto_const_nhds
    have hconstd : Tendsto (fun _ : ℕ => v - u) atTop (𝓝 (v - u)) :=
      tendsto_const_nhds
    simpa only [a, mul_zero, add_zero] using hconstu.add (hconstd.mul hzero)
  have haRight : Tendsto a atTop (𝓝[>] u) := by
    exact tendsto_nhdsWithin_iff.mpr ⟨ha,
      Filter.Eventually.of_forall (fun n => hau n)⟩
  have hlogEventually : ∀ᶠ n : ℕ in atTop,
      -(Real.log (1 - 2 * S.m u (a n) / S.r u (a n))) ≤ 1 := by
    have hh := hlogAxis.comp haRight
    have hev := hh.eventually (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 0))
    exact hev.mono (fun _ hn => by dsimp only [Function.comp_def] at hn; linarith)
  have hlogV : Real.log (1 - 2 * S.m u v / S.r u v) ≤ 0 := by
    have hm := h.mass_ratio_bounds huv
    exact Real.log_nonpos (by linarith) (by linarith)
  have hInt (n : ℕ) : IntegrableOn (nuCoeff S u) (Ioc (a n) v) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (hav n)).1
      (nu_coeff_integrable h.solution.development h huv (hau n) (hav n) le_rfl)
  have hBound : ∀ᶠ n : ℕ in atTop,
      (∫ t in Ioc (a n) v, ‖nuCoeff S u t‖) ≤ M * V + 1 := by
    filter_upwards [hlogEventually] with n hlogN
    have hvarN : (eVariationOn (S.phi u) (Ioc (a n) v)).toReal ≤ V :=
      ENNReal.toReal_mono hvarFinite
        (eVariationOn.mono (S.phi u) (Ioc_subset_Ioc_left (hau n).le))
    have hcomp := h.eq3_1a_compact huv (hau n) (hav n) le_rfl
      (fun t ht => hM t ⟨(hau n).trans ht.1, ht.2⟩)
    have hnorm : (∫ t in Ioc (a n) v, ‖nuCoeff S u t‖) =
        ∫ t in a n..v, nuCoeff S u t := by
      rw [intervalIntegral.integral_of_le (hav n)]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      have htU := h.solution.development.outgoing_mem huv
        ((hau n).trans_le ht.1.le) ht.2
      simp only [Real.norm_eq_abs, abs_of_nonneg
        (nu_coeff_nonneg h.solution.development h htU)]
    rw [hnorm]
    have hmul := mul_le_mul_of_nonneg_left hvarN hMnonneg
    linarith only [hcomp, hlogN, hlogV, hmul]
  exact integrableOn_Ioc_of_intervalIntegral_norm_bounded_left hInt ha hBound

/-- The outgoing coefficient estimate (3.1a) with its integrable
`nuCoeff` representative. The right-hand side is the full half-open scalar
variation. -/
theorem eq3_1a_nuCoeff
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v M : ℝ} (huv : (u, v) ∈ U)
    (hM : ∀ t ∈ Ioc u v, |S.theta u t / S.lam u t| ≤ M) :
    (∫ t in u..v, nuCoeff S u t) ≤
      M * (eVariationOn (S.phi u) (Ioc u v)).toReal := by
  have huvlt : u < v := (h.solution.development.wedge huv).2
  have hMnonneg : 0 ≤ M := (abs_nonneg _).trans (hM v ⟨huvlt, le_rfl⟩)
  have hfull : IntervalIntegrable (nuCoeff S u) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huvlt.le).2
      (h.nu_coeff_integrable_axis huv hM)
  let F : ℝ → ℝ := fun a => ∫ t in u..a, nuCoeff S u t
  have hFAC : AbsolutelyContinuousOnInterval F u v :=
    hfull.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hright : Tendsto (fun a : ℝ => a) (𝓝[>] u) (𝓝[Icc u v] u) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left inf_le_left,
      mem_of_superset (Ioo_mem_nhdsGT huvlt)
        (fun a ha => ⟨ha.1.le, ha.2.le⟩)⟩
  have hF : Tendsto F (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    have hcont : ContinuousOn F (Icc u v) := by
      simpa only [uIcc_of_le huvlt.le] using hFAC.continuousOn
    have hh := (hcont.continuousWithinAt
      (show u ∈ Icc u v from ⟨le_rfl, huvlt.le⟩)).tendsto.comp hright
    simpa only [F, Function.comp_def, intervalIntegral.integral_same] using hh
  have hsplit : ∀ᶠ a in 𝓝[>] u,
      (∫ t in a..v, nuCoeff S u t) =
        (∫ t in u..v, nuCoeff S u t) - F a := by
    filter_upwards [Ioo_mem_nhdsGT huvlt] with a ha
    have hleft : IntervalIntegrable (nuCoeff S u) volume u a :=
      hfull.mono_set (by
        rw [uIcc_of_le huvlt.le, uIcc_of_le ha.1.le]
        exact Icc_subset_Icc_right ha.2.le)
    have hright' : IntervalIntegrable (nuCoeff S u) volume a v :=
      hfull.mono_set (by
        rw [uIcc_of_le huvlt.le, uIcc_of_le ha.2.le]
        exact Icc_subset_Icc_left ha.1.le)
    have hh := intervalIntegral.integral_add_adjacent_intervals hleft hright'
    dsimp [F]
    linarith
  have hlim : Tendsto (fun a => ∫ t in a..v, nuCoeff S u t)
      (𝓝[>] u) (𝓝 (∫ t in u..v, nuCoeff S u t)) := by
    have hh : Tendsto (fun a => (∫ t in u..v, nuCoeff S u t) - F a)
        (𝓝[>] u) (𝓝 (∫ t in u..v, nuCoeff S u t)) := by
      simpa using tendsto_const_nhds.sub hF
    exact hh.congr' (hsplit.mono fun _ heq => heq.symm)
  have hlogAxis : Tendsto
      (fun a => Real.log (1 - 2 * S.m u a / S.r u a))
      (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    have hgap : Tendsto (fun a => 1 - 2 * S.m u a / S.r u a)
        (𝓝[>] u) (𝓝 (1 : ℝ)) := by
      simpa using (tendsto_const_nhds.sub (h.mass_ratio_tendsto_zero_axis_out huv))
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hgap
  have hlogV : Real.log (1 - 2 * S.m u v / S.r u v) ≤ 0 := by
    have hm := h.mass_ratio_bounds huv
    exact Real.log_nonpos (by linarith) (by linarith)
  obtain ⟨C, hvarOut, _⟩ := h.item3_variation
  have hslice : Ioc u v ⊆ {t | (u, t) ∈ U} := by
    intro t ht
    exact h.solution.development.outgoing_mem huv ht.1 ht.2
  have hvarFinite : eVariationOn (S.phi u) (Ioc u v) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((eVariationOn.mono (S.phi u) hslice).trans (hvarOut u))
  let V : ℝ := (eVariationOn (S.phi u) (Ioc u v)).toReal
  have hupper : ∀ᶠ a in 𝓝[>] u,
      (∫ t in a..v, nuCoeff S u t) ≤
        Real.log (1 - 2 * S.m u v / S.r u v) -
          Real.log (1 - 2 * S.m u a / S.r u a) + M * V := by
    filter_upwards [Ioo_mem_nhdsGT huvlt] with a ha
    have hcomp := h.eq3_1a_compact huv ha.1 ha.2.le le_rfl
      (fun t ht => hM t ⟨ha.1.trans ht.1, ht.2⟩)
    have hvarA : (eVariationOn (S.phi u) (Ioc a v)).toReal ≤ V :=
      ENNReal.toReal_mono hvarFinite
        (eVariationOn.mono (S.phi u) (Ioc_subset_Ioc_left ha.1.le))
    have hmul := mul_le_mul_of_nonneg_left hvarA hMnonneg
    linarith only [hcomp, hmul]
  have hlimitRight : Tendsto
      (fun a => Real.log (1 - 2 * S.m u v / S.r u v) -
        Real.log (1 - 2 * S.m u a / S.r u a) + M * V)
      (𝓝[>] u) (𝓝 (Real.log (1 - 2 * S.m u v / S.r u v) + M * V)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub hlogAxis).add
        (tendsto_const_nhds (x := M * V))
  have hle := le_of_tendsto_of_tendsto hlim hlimitRight hupper
  dsimp [V] at hle ⊢
  linarith only [hle, hlogV]

/-- On the development, `nuCoeff` is the coefficient printed in (3.1a). -/
theorem nuCoeff_eq_mass_ratio_coefficient_out
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u t : ℝ} (hut : (u, t) ∈ U) :
    nuCoeff S u t =
      (2 * S.m u t / S.r u t) * S.lam u t /
        ((1 - 2 * S.m u t / S.r u t) * S.r u t) := by
  have hr : S.r u t ≠ 0 := ne_of_gt (h.solution.radius_pos (u, t) hut)
  have hg : 1 - 2 * S.m u t / S.r u t ≠ 0 := by
    have := (h.mass_ratio_bounds hut).2
    linarith
  have hg' : S.r u t - 2 * S.m u t ≠ 0 := by
    intro hzero
    apply hg
    have hratio : 2 * S.m u t / S.r u t = 1 := by
      apply (div_eq_iff hr).2
      linarith
    linarith
  unfold nuCoeff gap
  field_simp [hr, hg, hg']

/-- Christodoulou's outgoing coefficient bound (3.1a), using a finite
pointwise ratio bound on the complete outgoing characteristic. -/
theorem eq3_1a
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v M : ℝ} (huv : (u, v) ∈ U)
    (hM : ∀ t ∈ Ioc u v, |S.theta u t / S.lam u t| ≤ M) :
    (∫ t in u..v,
      (2 * S.m u t / S.r u t) * S.lam u t /
        ((1 - 2 * S.m u t / S.r u t) * S.r u t)) ≤
      M * (eVariationOn (S.phi u) (Ioc u v)).toReal := by
  have heq : (∫ t in u..v,
      (2 * S.m u t / S.r u t) * S.lam u t /
        ((1 - 2 * S.m u t / S.r u t) * S.r u t)) =
      ∫ t in u..v, nuCoeff S u t := by
    apply intervalIntegral.integral_congr_Ioo_of_le
      (h.solution.development.wedge huv).2.le
    intro t ht
    exact (h.nuCoeff_eq_mass_ratio_coefficient_out
      (h.solution.development.outgoing_mem huv ht.1 ht.2.le)).symm
  rw [heq]
  exact h.eq3_1a_nuCoeff huv hM

end ChristodoulouBV.IsBVSolution

end
