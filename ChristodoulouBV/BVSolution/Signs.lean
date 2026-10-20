module

public import ChristodoulouBV.BVSolution.SignAux
public import ChristodoulouBV.ForMathlib.BoundedVariation.SliceFacts

/-!
# Strict signs and expansion bounds for frozen BV solutions

These estimates hold at every actual development point, without selecting
right-continuous representatives of the BV fields.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.IsBVSolution

/-- The mixed expansion density from the frozen characteristic equations. -/
noncomputable def radiusCoeff (S : Fields) (u v : ℝ) : ℝ :=
  (2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
    ((1 - 2 * S.m u v / S.r u v) * S.r u v)

/-- The coefficient in the linear mass-gap equation is nonnegative on the development. -/
theorem barrier_coeff_nonneg
    {D : Set (ℝ × ℝ)} {S : Fields}
    (_hD : IsDomainOfDevelopment D)
    (hS : IsBVSolution D S)
    {u v : ℝ} (huv : (u, v) ∈ D) : 0 ≤ barrierCoeff S u v := by
  have hr := hS.solution.radius_pos (u, v) huv
  obtain ⟨c, hc, hlam⟩ := hS.lam_bounded_below
  have hl := lt_of_lt_of_le hc (hlam (u, v) huv)
  have hθ : 0 ≤ S.theta u v * S.theta u v := mul_self_nonneg _
  unfold barrierCoeff
  exact mul_nonneg (mul_nonneg hθ (inv_nonneg.mpr hr.le)) (inv_nonneg.mpr hl.le)

/-- The outgoing Hawking-mass integrand is nonnegative once the gap is positive. -/
theorem mass_density_nonneg
    {D : Set (ℝ × ℝ)} {S : Fields}
    (hD : IsDomainOfDevelopment D)
    (hS : IsBVSolution D S)
    {u v : ℝ} (huv : (u, v) ∈ D) : 0 ≤ massV S u v := by
  have hcoeff := barrier_coeff_nonneg hD hS huv
  have hgap := gap_pos_aux hD hS huv
  have hid := barrier_coeff_mul_gap_eq_two_mass_density hD hS huv
  nlinarith [mul_nonneg hcoeff hgap.le]

/-- The mass axis trace and outgoing monotonicity force nonnegative Hawking mass. -/
theorem mass_nonneg_aux
    {D : Set (ℝ × ℝ)} {S : Fields}
    (hD : IsDomainOfDevelopment D)
    (hS : IsBVSolution D S)
    {u v : ℝ} (huv : (u, v) ∈ D) : 0 ≤ S.m u v := by
  have hlt : u < v := (hD.1 huv).2
  have haxis : Tendsto (S.m u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [hD.axis_filter_eq huv] using
      hS.solution.mass_axis u (hD.axis_mem huv)
  have hbound : ∀ᶠ a in 𝓝[>] u, S.m u a ≤ S.m u v := by
    filter_upwards [Ioo_mem_nhdsGT hlt] with a ha
    have hseg := outgoing_primitive_on_subsegments hD huv ha.1 ha.2.le le_rfl
      v ⟨ha.2.le, le_rfl⟩
    obtain ⟨hint, heq⟩ := hS.solution.mass_out u a v ha.2.le hseg
    have hnonneg : 0 ≤ ∫ s in a..v, massV S u s := by
      apply intervalIntegral.integral_nonneg ha.2.le
      intro s hs
      exact mass_density_nonneg hD hS
        (hD.outgoing_mem huv (ha.1.trans_le hs.1) hs.2)
    change S.m u v - S.m u a = ∫ s in a..v, massV S u s at heq
    linarith
  exact le_of_tendsto haxis hbound

/-- The mass ratio is in the physical interval `[0,1)` on every development point. -/
theorem mass_ratio_bounds_aux
    {D : Set (ℝ × ℝ)} {S : Fields}
    (hD : IsDomainOfDevelopment D)
    (hS : IsBVSolution D S)
    {u v : ℝ} (huv : (u, v) ∈ D) :
    0 ≤ 2 * S.m u v / S.r u v ∧ 2 * S.m u v / S.r u v < 1 := by
  have hr := hS.solution.radius_pos (u, v) huv
  have hm := mass_nonneg_aux hD hS huv
  have hgap := gap_pos_aux hD hS huv
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) hm) hr.le
  · apply (div_lt_iff₀ hr).2
    dsimp [gap] at hgap
    linarith


/-- The outgoing growth coefficient in the linear equation for `ν`. -/
noncomputable def nuCoeff (S : Fields) (u t : ℝ) : ℝ :=
  2 * S.m u t * (S.r u t)⁻¹ * (gap S u t)⁻¹ * S.lam u t

/-- The frozen mixed radius coefficient equals `nuCoeff * ν` after the mass gap is positive. -/
theorem radius_coeff_eq_nu_coeff_mul_nu
    {D : Set (ℝ × ℝ)} {S : Fields}
    (hD : IsDomainOfDevelopment D)
    (hS : IsBVSolution D S)
    {u t : ℝ} (hut : (u, t) ∈ D) :
    radiusCoeff S u t = nuCoeff S u t * S.nu u t := by
  have hr : S.r u t ≠ 0 := ne_of_gt (hS.solution.radius_pos (u, t) hut)
  have hgap : gap S u t ≠ 0 := ne_of_gt (gap_pos_aux hD hS hut)
  have hden : 1 - 2 * S.m u t / S.r u t ≠ 0 := by
    have hlt := (mass_ratio_bounds_aux hD hS hut).2
    linarith
  unfold nuCoeff gap radiusCoeff at *
  field_simp

/-- The `ν` coefficient is nonnegative on the actual development. -/
theorem nu_coeff_nonneg
    {D : Set (ℝ × ℝ)} {S : Fields}
    (hD : IsDomainOfDevelopment D)
    (hS : IsBVSolution D S)
    {u t : ℝ} (hut : (u, t) ∈ D) : 0 ≤ nuCoeff S u t := by
  have hm := mass_nonneg_aux hD hS hut
  have hr := hS.solution.radius_pos (u, t) hut
  have hgap := gap_pos_aux hD hS hut
  obtain ⟨c, hc, hlam⟩ := hS.lam_bounded_below
  have hl := lt_of_lt_of_le hc (hlam (u, t) hut)
  unfold nuCoeff
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hm)
    (inv_nonneg.mpr hr.le)) (inv_nonneg.mpr hgap.le)) hl.le

/-- `nuCoeff` is locally integrable on closed outgoing intervals away from the axis. -/
theorem nu_coeff_integrable
    {D : Set (ℝ × ℝ)} {S : Fields} {u v a b : ℝ}
    (hD : IsDomainOfDevelopment D)
    (hS : IsBVSolution D S)
    (huv : (u, v) ∈ D) (hua : u < a) (hab : a ≤ b) (hbv : b ≤ v) :
    IntervalIntegrable (nuCoeff S u) volume a b := by
  have hrCont : ContinuousOn (S.r u) (Icc a b) := by
    simpa [uIcc_of_le hab] using
      (radius_ac_on_outgoing hD hS.solution huv hua hab hbv).continuousOn
  have hmCont : ContinuousOn (S.m u) (Icc a b) := by
    simpa [uIcc_of_le hab] using
      (mass_ac_on_outgoing hD hS.solution huv hua hab hbv).continuousOn
  have hgapCont : ContinuousOn (gap S u) (Icc a b) := by
    change ContinuousOn (fun t => S.r u t - 2 * S.m u t) (Icc a b)
    exact hrCont.sub (continuousOn_const.mul hmCont)
  have hrInv : ContinuousOn (fun t => (S.r u t)⁻¹) (Icc a b) :=
    hrCont.inv₀ (by
      intro t ht
      exact ne_of_gt (hS.solution.radius_pos (u, t)
        (hD.outgoing_mem huv (hua.trans_le ht.1) (ht.2.trans hbv))))
  have hgapInv : ContinuousOn (fun t => (gap S u t)⁻¹) (Icc a b) :=
    hgapCont.inv₀ (by
      intro t ht
      exact ne_of_gt (gap_pos_aux hD hS
        (hD.outgoing_mem huv (hua.trans_le ht.1) (ht.2.trans hbv))))
  obtain ⟨C, hvarOut, _⟩ := hS.item1
  have hLamBV : BoundedVariationOn (S.lam u) (Icc a b) :=
    bounded_variation_on_outgoing_of_le hD huv hua hab hbv (by
      exact hvarOut u)
  have hLamInt : IntervalIntegrable (S.lam u) volume a b :=
    hLamBV.intervalIntegrable (by simp [uIcc_of_le hab])
  have hFactor : ContinuousOn
      (fun t => 2 * S.m u t * (S.r u t)⁻¹ * (gap S u t)⁻¹)
      (Icc a b) := ((continuousOn_const.mul hmCont).mul hrInv).mul hgapInv
  change IntervalIntegrable
    (fun t => (2 * S.m u t * (S.r u t)⁻¹ * (gap S u t)⁻¹) * S.lam u t)
    volume a b
  exact hLamInt.continuousOn_mul (by simpa [uIcc_of_le hab] using hFactor)

/-- The outgoing `ν` primitive is a homogeneous linear equation with nonnegative coefficient. -/
theorem nu_local_linear_equation
    {D : Set (ℝ × ℝ)} {S : Fields} {u v a b : ℝ}
    (hD : IsDomainOfDevelopment D)
    (hS : IsBVSolution D S)
    (huv : (u, v) ∈ D) (hua : u < a) (hab : a ≤ b) (hbv : b ≤ v) :
    IntervalIntegrable (nuCoeff S u) volume a b ∧
    IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a b ∧
    IntervalIntegrable (fun s => nuCoeff S u s * S.nu u s) volume a b ∧
    ∀ t ∈ Icc a b,
      S.nu u t - S.nu u a =
        ∫ s in a..t, (nuCoeff S u s * S.nu u s + 0) := by
  have hq := nu_coeff_integrable hD hS huv hua hab hbv
  have hseg := outgoing_primitive_on_subsegments hD huv hua hab hbv
  have hNuFull := hS.solution.nu_out u a b hab (hseg b ⟨hab, le_rfl⟩)
  have hqNu : IntervalIntegrable (fun s => nuCoeff S u s * S.nu u s)
      volume a b := by
    apply hNuFull.1.congr_uIoo
    intro s hs
    rw [uIoo_of_le hab] at hs
    exact radius_coeff_eq_nu_coeff_mul_nu hD hS
      (hD.outgoing_mem huv (hua.trans_le hs.1.le) (hs.2.le.trans hbv))
  refine ⟨hq, intervalIntegrable_const, hqNu, ?_⟩
  intro t ht
  obtain ⟨hint, heq⟩ := hS.solution.nu_out u a t ht.1 (hseg t ht)
  have heqInt : (∫ s in a..t, radiusCoeff S u s) =
      ∫ s in a..t, nuCoeff S u s * S.nu u s := by
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1
    intro s hs
    exact radius_coeff_eq_nu_coeff_mul_nu hD hS
      (hD.outgoing_mem huv (hua.trans_le hs.1.le)
        (hs.2.le.trans (ht.2.trans hbv)))
  change S.nu u t - S.nu u a = ∫ s in a..t, radiusCoeff S u s at heq
  rw [heqInt] at heq
  simpa using heq

/-- The outgoing homogeneous equation propagates the exact initial `ν` value. -/
theorem nu_eq_exp_mul
    {D : Set (ℝ × ℝ)} {S : Fields} {u v a b : ℝ}
    (hD : IsDomainOfDevelopment D)
    (hS : IsBVSolution D S)
    (huv : (u, v) ∈ D) (hua : u < a) (hab : a ≤ b) (hbv : b ≤ v) :
    S.nu u b = Real.exp (∫ s in a..b, nuCoeff S u s) * S.nu u a := by
  obtain ⟨hq, hzero, hqnu, hEq⟩ :=
    nu_local_linear_equation hD hS huv hua hab hbv
  have hformula := intervalIntegral.eq_exp_mul_add_integral_of_integral_eq
    hab hq hzero hqnu hEq (show b ∈ Icc a b from ⟨hab, le_rfl⟩)
  simpa using hformula

/-- The axis expansion trace and nonnegative coefficient force `ν ≤ -c`. -/
theorem nu_le_neg_lower_expansion
    {D : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (hD : IsDomainOfDevelopment D)
    (hS : IsBVSolution D S)
    (hc : 0 < c)
    (hlam : ∀ p ∈ D, c ≤ S.lam p.1 p.2)
    {u v : ℝ} (huv : (u, v) ∈ D) : S.nu u v ≤ -c := by
  have hlt : u < v := (hD.1 huv).2
  have haxis : Tendsto (fun t => S.nu u t + S.lam u t)
      (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [hD.axis_filter_eq huv] using
      hS.item2 u (hD.axis_mem huv)
  have hsmall : ∀ᶠ a in 𝓝[>] u, S.nu u a + S.lam u a < c :=
    haxis.eventually (eventually_lt_nhds hc)
  have hbound : ∀ᶠ a in 𝓝[>] u,
      S.nu u v + c ≤ S.nu u a + S.lam u a := by
    filter_upwards [hsmall, Ioo_mem_nhdsGT hlt] with a hsum ha
    have haD := hD.outgoing_mem huv ha.1 ha.2.le
    have hla := hlam (u, a) haD
    have hnuA : S.nu u a < 0 := by linarith
    have hform := nu_eq_exp_mul hD hS huv ha.1 ha.2.le le_rfl
    have hqInt := nu_coeff_integrable hD hS huv ha.1 ha.2.le le_rfl
    have hqNonneg : 0 ≤ ∫ s in a..v, nuCoeff S u s := by
      apply intervalIntegral.integral_nonneg ha.2.le
      intro s hs
      exact nu_coeff_nonneg hD hS
        (hD.outgoing_mem huv (ha.1.trans_le hs.1) hs.2)
    have hExp : 1 ≤ Real.exp (∫ s in a..v, nuCoeff S u s) :=
      Real.one_le_exp_iff.mpr hqNonneg
    have hNuLe : S.nu u v ≤ S.nu u a := by
      rw [hform]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hExp) hnuA.le]
    linarith
  have hle : S.nu u v + c ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds haxis hbound
  linarith

/-- In particular, the incoming expansion is strictly negative on the development. -/
theorem nu_neg_aux
    {D : Set (ℝ × ℝ)} {S : Fields}
    (hD : IsDomainOfDevelopment D)
    (hS : IsBVSolution D S)
    {u v : ℝ} (huv : (u, v) ∈ D) : S.nu u v < 0 := by
  obtain ⟨c, hc, hlam⟩ := hS.lam_bounded_below
  have hle := nu_le_neg_lower_expansion hD hS hc hlam huv
  linarith

/-- The lower expansion bound integrates to a quantitative radius bound. -/
theorem radius_lower {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsBVSolution U S) {c u v : ℝ}
    (hlam : ∀ p ∈ U, c ≤ S.lam p.1 p.2) (huv : (u, v) ∈ U) :
    c * (v - u) ≤ S.r u v :=
  radius_ge_of_lam_ge h.solution.development h.solution hlam huv

/-- The Hawking mass is nonnegative at every development point. -/
theorem mass_nonneg {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsBVSolution U S) {u v : ℝ} (huv : (u, v) ∈ U) :
    0 ≤ S.m u v :=
  mass_nonneg_aux h.solution.development h huv

/-- Twice the mass is strictly smaller than the radius. -/
theorem two_mass_lt_radius {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsBVSolution U S) {u v : ℝ} (huv : (u, v) ∈ U) :
    2 * S.m u v < S.r u v := by
  have hgap := gap_pos_aux h.solution.development h huv
  dsimp [gap] at hgap
  linarith

/-- The mass ratio lies in `[0,1)` pointwise. -/
theorem mass_ratio_bounds {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsBVSolution U S) {u v : ℝ} (huv : (u, v) ∈ U) :
    0 ≤ 2 * S.m u v / S.r u v ∧ 2 * S.m u v / S.r u v < 1 :=
  mass_ratio_bounds_aux h.solution.development h huv

/-- The incoming expansion has the opposite strict sign, with the same lower
constant as the outgoing expansion. -/
theorem nu_le_neg_lower {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsBVSolution U S) {c u v : ℝ} (hc : 0 < c)
    (hlam : ∀ p ∈ U, c ≤ S.lam p.1 p.2) (huv : (u, v) ∈ U) :
    S.nu u v ≤ -c :=
  nu_le_neg_lower_expansion h.solution.development h hc hlam huv

/-- Every conformal witness has the quotient value determined by the signed
expansions and the mass ratio. -/
theorem conformal_witness_consistent {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsBVSolution U S) {u v : ℝ} (huv : (u, v) ∈ U) :
    ∃ Ω : ℝ, 0 < Ω ∧
      Ω ^ 2 = -(4 * S.lam u v * S.nu u v) /
        (1 - 2 * S.m u v / S.r u v) := by
  obtain ⟨Ω, hΩ, hEq⟩ := h.solution.conformal (u, v) huv
  refine ⟨Ω, hΩ, ?_⟩
  have hden : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hlt := (h.mass_ratio_bounds huv).2
    linarith
  apply (eq_div_iff hden).2
  nlinarith [hEq]

/-- A uniform BV bound controls the outgoing expansion by its axis trace and
the uniform bound on the incoming expansion. -/
theorem lam_le_of_variation_bound {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsBVSolution U S) {N C u v : ℝ} (hC : 0 ≤ C)
    (hnu : ∀ p ∈ U, -S.nu p.1 p.2 ≤ N)
    (hvar : ∀ a, eVariationOn (S.lam a) {t | (a, t) ∈ U} ≤ ENNReal.ofReal C)
    (huv : (u, v) ∈ U) : S.lam u v ≤ N + C := by
  let hD := h.solution.development
  have hlt : u < v := (hD.wedge huv).2
  have haxis : Tendsto (fun t => S.nu u t + S.lam u t)
      (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [hD.axis_filter_eq huv] using h.item2 u (hD.axis_mem huv)
  have hBV : BoundedVariationOn (S.lam u) {t | (u, t) ∈ U} := by
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hvar u)
  have hTV : (eVariationOn (S.lam u) {t | (u, t) ∈ U}).toReal ≤ C :=
    ENNReal.toReal_le_of_le_ofReal hC (hvar u)
  have hbound : ∀ᶠ a in 𝓝[>] u,
      S.lam u v - (N + C) ≤ S.nu u a + S.lam u a := by
    filter_upwards [Ioo_mem_nhdsGT hlt] with a ha
    have haU := hD.outgoing_mem huv ha.1 ha.2.le
    have hdiff := hBV.abs_sub_le_variation huv haU
    have hnuA := hnu (u, a) haU
    linarith [le_abs_self (S.lam u v - S.lam u a)]
  have hle : S.lam u v - (N + C) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds haxis hbound
  linarith

/-- A pointwise upper expansion bound integrates from the excluded axis. -/
theorem radius_upper_of_lam_le {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsBVSolution U S) {K u v : ℝ}
    (hlam : ∀ p ∈ U, S.lam p.1 p.2 ≤ K) (huv : (u, v) ∈ U) :
    S.r u v ≤ K * (v - u) := by
  let hD := h.solution.development
  have hlt : u < v := (hD.wedge huv).2
  have haxis : Tendsto (S.r u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [hD.axis_filter_eq huv] using
      h.solution.radius_axis u (hD.axis_mem huv)
  have hlimK : Tendsto (fun a : ℝ => K * (v - a)) (𝓝[>] u)
      (𝓝 (K * (v - u))) :=
    ((show Continuous (fun a : ℝ => K * (v - a)) by fun_prop).tendsto u).mono_left
      inf_le_left
  have hlim : Tendsto (fun a : ℝ => S.r u a + K * (v - a))
      (𝓝[>] u) (𝓝 (K * (v - u))) := by
    simpa using haxis.add hlimK
  have hbound : ∀ᶠ a in 𝓝[>] u, S.r u v ≤ S.r u a + K * (v - a) := by
    filter_upwards [Ioo_mem_nhdsGT hlt] with a ha
    have hseg := hD.out_seg_subset huv ha.1 ha.2.le le_rfl
    obtain ⟨hint, heq⟩ := h.solution.radius_out u a v ha.2.le hseg
    have hcint : IntervalIntegrable (fun _ : ℝ => K) volume a v :=
      intervalIntegrable_const
    have hmono : (∫ t in a..v, S.lam u t) ≤ ∫ _ in a..v, K := by
      apply intervalIntegral.integral_mono_on ha.2.le hint hcint
      intro t ht
      exact hlam (u, t) (hD.outgoing_mem huv (ha.1.trans_le ht.1) ht.2)
    rw [intervalIntegral.integral_const] at hmono
    simp only [smul_eq_mul] at hmono
    linarith
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hbound

/-- The BV hypotheses give one uniform bound for `λ` and the radius. -/
theorem exists_uniform_radius_upper {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsBVSolution U S) :
    ∃ K : ℝ, (∀ p ∈ U, S.lam p.1 p.2 ≤ K) ∧
      ∀ u v, (u, v) ∈ U → S.r u v ≤ K * (v - u) := by
  obtain ⟨N, hnu⟩ := h.nu_bounded_below
  obtain ⟨C, hvar, _⟩ := h.item1
  let K := N + max C 0
  have hC : 0 ≤ max C 0 := le_max_right _ _
  have hvar' : ∀ a, eVariationOn (S.lam a) {t | (a, t) ∈ U} ≤
      ENNReal.ofReal (max C 0) := by
    intro a
    exact (hvar a).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hlam : ∀ p ∈ U, S.lam p.1 p.2 ≤ K := by
    intro p hp
    exact h.lam_le_of_variation_bound hC hnu hvar' hp
  exact ⟨K, hlam, fun u v huv => h.radius_upper_of_lam_le hlam huv⟩


end ChristodoulouBV.IsBVSolution

end
