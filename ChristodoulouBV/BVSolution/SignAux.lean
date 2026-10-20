module

public import ChristodoulouBV.BVSolution.Geometry
public import ChristodoulouBV.Frozen.IsBVSolution
public import ChristodoulouBV.ForMathlib.AbsolutelyContinuous.Calculus
public import ChristodoulouBV.ForMathlib.BoundedVariation.Algebra
public import ChristodoulouBV.ForMathlib.IntervalIntegral.LinearEquation

/-!
# Local regularity and mass-gap barrier for BV solutions

The linear-equation argument uses variation bounds and primitives, with no
right-continuity hypothesis.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.IsBVSolution

/-- The outgoing mass density from the frozen characteristic equation. -/
noncomputable def massV (S : Fields) (u v : ℝ) : ℝ :=
  (1 - 2 * S.m u v / S.r u v) * (S.theta u v) ^ 2 / (2 * S.lam u v)

/-- The positive lower outgoing expansion integrates from the excluded axis by its trace. -/
theorem radius_ge_of_lam_ge
    {D : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (hD : IsDomainOfDevelopment D)
    (hcore : IsSolution D S)
    (hlam : ∀ p ∈ D, c ≤ S.lam p.1 p.2)
    {u v : ℝ} (huv : (u, v) ∈ D) :
    c * (v - u) ≤ S.r u v := by
  have hu0 := (hD.1 huv).1
  have hlt : u < v := (hD.1 huv).2
  have haxis : Tendsto (S.r u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [hD.axis_filter_eq huv] using
      hcore.radius_axis u (hD.axis_mem huv)
  have hlimc : Tendsto (fun t : ℝ => c * (v - t)) (𝓝[>] u) (𝓝 (c * (v - u))) :=
    ((show Continuous (fun t : ℝ => c * (v - t)) by fun_prop).tendsto u).mono_left
      inf_le_left
  have hlim : Tendsto (fun t : ℝ => S.r u t + c * (v - t)) (𝓝[>] u)
      (𝓝 (c * (v - u))) := by
    simpa using haxis.add hlimc
  have hbound : ∀ᶠ a in 𝓝[>] u, S.r u a + c * (v - a) ≤ S.r u v := by
    filter_upwards [Ioo_mem_nhdsGT hlt] with a ha
    have hseg : outSeg u a v ⊆ D := by
      intro p hp
      have ⟨hpu, hpv⟩ : p.1 = u ∧ p.2 ∈ Icc a v := by
        simpa [outSeg] using hp
      rcases p with ⟨s, t⟩
      dsimp at hpu hpv ⊢
      subst s
      exact hD.outgoing_mem huv (ha.1.trans_le hpv.1) hpv.2
    obtain ⟨hint, heq⟩ := hcore.radius_out u a v ha.2.le hseg
    have hcint : IntervalIntegrable (fun _ : ℝ => c) volume a v :=
      intervalIntegrable_const
    have hmono : (∫ _ in a..v, c) ≤ ∫ t in a..v, S.lam u t := by
      apply intervalIntegral.integral_mono_on ha.2.le hcint hint
      intro t ht
      exact hlam (u, t) (hD.outgoing_mem huv (ha.1.trans_le ht.1) ht.2)
    rw [intervalIntegral.integral_const] at hmono
    simp only [smul_eq_mul] at hmono
    nlinarith
  exact le_of_tendsto hlim hbound


/-- A primitive from one fixed endpoint to every point is absolutely continuous. -/
theorem absolutely_continuous_on_interval_of_primitive
    {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hprim : ∀ t ∈ Icc a b, IntervalPrimitive f g a t) :
    AbsolutelyContinuousOnInterval f a b := by
  have hfull := hprim b ⟨hab, le_rfl⟩
  apply AbsolutelyContinuousOnInterval.of_integral_eq_sub hfull.1
  intro t ht
  exact (hprim t (by simpa [uIcc_of_le hab] using ht)).2

/-- A closed outgoing segment contained in a development has the frozen primitives on
all of its subsegments. -/
theorem outgoing_primitive_on_subsegments
    {D : Set (ℝ × ℝ)} {u v a b : ℝ}
    (hD : IsDomainOfDevelopment D)
    (huv : (u, v) ∈ D) (hua : u < a) (_hab : a ≤ b) (hbv : b ≤ v) :
    ∀ t ∈ Icc a b, outSeg u a t ⊆ D := by
  intro t ht p hp
  have ⟨hpu, hpv⟩ : p.1 = u ∧ p.2 ∈ Icc a t := by
    simpa [outSeg] using hp
  rcases p with ⟨s, w⟩
  dsimp at hpu hpv ⊢
  subst s
  exact hD.outgoing_mem huv (hua.trans_le hpv.1) (hpv.2.trans (ht.2.trans hbv))

/-- The radius is absolutely continuous on every compact outgoing segment off the axis. -/
theorem radius_ac_on_outgoing
    {D : Set (ℝ × ℝ)} {S : Fields} {u v a b : ℝ}
    (hD : IsDomainOfDevelopment D)
    (hcore : IsSolution D S)
    (huv : (u, v) ∈ D) (hua : u < a) (hab : a ≤ b) (hbv : b ≤ v) :
    AbsolutelyContinuousOnInterval (S.r u) a b := by
  refine absolutely_continuous_on_interval_of_primitive (g := S.lam u) hab ?_
  intro t ht
  exact hcore.radius_out u a t ht.1
    (outgoing_primitive_on_subsegments hD huv hua hab hbv t ht)

/-- The mass is absolutely continuous on every compact outgoing segment off the axis. -/
theorem mass_ac_on_outgoing
    {D : Set (ℝ × ℝ)} {S : Fields} {u v a b : ℝ}
    (hD : IsDomainOfDevelopment D)
    (hcore : IsSolution D S)
    (huv : (u, v) ∈ D) (hua : u < a) (hab : a ≤ b) (hbv : b ≤ v) :
    AbsolutelyContinuousOnInterval (S.m u) a b := by
  refine absolutely_continuous_on_interval_of_primitive (g := massV S u) hab ?_
  intro t ht
  exact hcore.mass_out u a t ht.1
    (outgoing_primitive_on_subsegments hD huv hua hab hbv t ht)

/-- Every outgoing field with the frozen uniform variation bound is BV on its compact
subintervals. -/
theorem bounded_variation_on_outgoing_of_le
    {D : Set (ℝ × ℝ)} {f : ℝ → ℝ} {C u v a b : ℝ}
    (hD : IsDomainOfDevelopment D)
    (huv : (u, v) ∈ D) (hua : u < a) (_hab : a ≤ b) (hbv : b ≤ v)
    (hvar : eVariationOn f {t | (u, t) ∈ D} ≤ ENNReal.ofReal C) :
    BoundedVariationOn f (Icc a b) := by
  have hsubset : Icc a b ⊆ {t | (u, t) ∈ D} := by
    intro t ht
    exact hD.outgoing_mem huv (hua.trans_le ht.1) (ht.2.trans hbv)
  exact ne_top_of_le_ne_top (lt_top_iff_ne_top.mp (lt_of_le_of_lt hvar ENNReal.ofReal_lt_top))
    (eVariationOn.mono f hsubset)

/-- Reciprocal of a BV function is BV when the function is separated from zero. -/
theorem bounded_variation_on_inv_of_abs_ge
    {g : ℝ → ℝ} {s : Set ℝ} {d : ℝ}
    (hd : 0 < d) (hg : BoundedVariationOn g s)
    (hbound : ∀ x ∈ s, d ≤ |g x|) :
    BoundedVariationOn (fun x => (g x)⁻¹) s := by
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg)
    (eVariationOn.inv_le_of_abs_ge hd hbound)

/-- The nonsingular mass-barrier coefficient is locally interval-integrable. -/
theorem barrier_coefficient_integrable
    {D : Set (ℝ × ℝ)} {S : Fields} {u v a b : ℝ}
    (hD : IsDomainOfDevelopment D)
    (hS : IsBVSolution D S)
    (huv : (u, v) ∈ D) (hua : u < a) (hab : a ≤ b) (hbv : b ≤ v) :
    IntervalIntegrable
      (fun t => S.theta u t * S.theta u t * (S.r u t)⁻¹ * (S.lam u t)⁻¹)
      volume a b := by
  obtain ⟨c, hc, hlam⟩ := hS.lam_bounded_below
  obtain ⟨C, hvarOut, _⟩ := hS.item1
  have hLam : BoundedVariationOn (S.lam u) (Icc a b) :=
    bounded_variation_on_outgoing_of_le hD huv hua hab hbv (by
      exact hvarOut u)
  have hθ : BoundedVariationOn (S.theta u) (Icc a b) :=
    bounded_variation_on_outgoing_of_le hD huv hua hab hbv (hS.item5.choose_spec.1 u)
  have hrAC := radius_ac_on_outgoing hD hS.solution huv hua hab hbv
  have hr : BoundedVariationOn (S.r u) (Icc a b) := by
    simpa [uIcc_of_le hab] using hrAC.boundedVariationOn
  have hLamInv : BoundedVariationOn (fun t => (S.lam u t)⁻¹) (Icc a b) :=
    bounded_variation_on_inv_of_abs_ge hc hLam (by
      intro t ht
      have htD := hD.outgoing_mem huv (hua.trans_le ht.1) (ht.2.trans hbv)
      have hct := hlam (u, t) htD
      rw [abs_of_nonneg (le_trans hc.le hct)]
      exact hct)
  have hd : 0 < c * (a - u) := mul_pos hc (sub_pos.mpr hua)
  have hrInv : BoundedVariationOn (fun t => (S.r u t)⁻¹) (Icc a b) :=
    bounded_variation_on_inv_of_abs_ge hd hr (by
      intro t ht
      have htD := hD.outgoing_mem huv (hua.trans_le ht.1) (ht.2.trans hbv)
      have hrt := radius_ge_of_lam_ge hD hS.solution
        hlam htD
      have hct : c * (a - u) ≤ c * (t - u) := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        linarith [ht.1]
      rw [abs_of_nonneg (le_trans hd.le (hct.trans hrt))]
      exact hct.trans hrt)
  have hkBV : BoundedVariationOn
      (fun t => S.theta u t * S.theta u t * (S.r u t)⁻¹ * (S.lam u t)⁻¹)
      (Icc a b) := (hθ.mul hθ |>.mul hrInv).mul hLamInv
  exact hkBV.intervalIntegrable (by simp [uIcc_of_le hab])


/-- The source term in the integrating-factor formula is strictly positive on a genuine
interval when the forcing is pointwise positive. -/
theorem linear_source_integral_pos
    {a b c : ℝ} {k g : ℝ → ℝ} (hab : a < b) (hc : 0 < c)
    (hk : IntervalIntegrable k volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hgpos : ∀ s ∈ Icc a b, c ≤ g s) :
    0 < ∫ s in a..b, Real.exp (-(∫ σ in a..s, k σ)) * g s := by
  have hK : AbsolutelyContinuousOnInterval (fun s => ∫ σ in a..s, k σ) a b :=
    hk.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hF : IntervalIntegrable
      (fun s => Real.exp (-(∫ σ in a..s, k σ)) * g s) volume a b :=
    hg.continuousOn_mul hK.neg.exp.continuousOn
  apply intervalIntegral.intervalIntegral_pos_of_pos_on hF _ hab
  intro s hs
  exact mul_pos (Real.exp_pos _) (lt_of_lt_of_le hc (hgpos s ⟨hs.1.le, hs.2.le⟩))

/-- A nonpositive linear coefficient and nonnegative source prevent an interval solution
from falling below minus the absolute value of its initial data. -/
theorem linear_solution_ge_neg_abs_initial
    {a b : ℝ} {k g y : ℝ → ℝ} (hab : a ≤ b)
    (hk : IntervalIntegrable k volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hky : IntervalIntegrable (fun s => k s * y s) volume a b)
    (hy : ∀ t ∈ Icc a b,
      y t - y a = ∫ s in a..t, (k s * y s + g s))
    (hk_nonpos : ∀ s ∈ Icc a b, k s ≤ 0)
    (hg_nonneg : ∀ s ∈ Icc a b, 0 ≤ g s) :
    -|y a| ≤ y b := by
  have hformula := intervalIntegral.eq_exp_mul_add_integral_of_integral_eq
    hab hk hg hky hy (show b ∈ Icc a b from ⟨hab, le_rfl⟩)
  let E : ℝ := Real.exp (∫ s in a..b, k s)
  let J : ℝ := ∫ s in a..b, Real.exp (-(∫ σ in a..s, k σ)) * g s
  have hJ : 0 ≤ J := by
    dsimp [J]
    apply intervalIntegral.integral_nonneg hab
    intro s hs
    exact mul_nonneg (Real.exp_pos _).le (hg_nonneg s hs)
  have hK : (∫ s in a..b, k s) ≤ 0 := by
    have hn : 0 ≤ ∫ s in a..b, -k s := by
      apply intervalIntegral.integral_nonneg hab
      intro s hs
      exact neg_nonneg.mpr (hk_nonpos s hs)
    rw [intervalIntegral.integral_neg] at hn
    linarith
  have hEpos : 0 < E := Real.exp_pos _
  have hEle : E ≤ 1 := Real.exp_le_one_iff.mpr hK
  have hA : 0 ≤ y a + |y a| := by linarith [neg_abs_le (y a)]
  have hProdA := mul_nonneg hEpos.le hA
  have hProdB := mul_nonneg (sub_nonneg.mpr hEle) (abs_nonneg (y a))
  change y b = E * (y a + J) at hformula
  nlinarith [mul_nonneg hEpos.le hJ]

/-- A zero right trace and a positive forcing give a strict positive barrier even when
the nonpositive coefficient is not integrable at the excluded axis. -/
theorem linear_solution_pos_of_axis_trace
    {u b c : ℝ} {k g y : ℝ → ℝ} (hub : u < b) (hc : 0 < c)
    (haxis : Tendsto y (𝓝[>] u) (𝓝 (0 : ℝ)))
    (hlocal : ∀ a d, u < a → a ≤ d → d ≤ b →
      IntervalIntegrable k volume a d ∧
      IntervalIntegrable g volume a d ∧
      IntervalIntegrable (fun s => k s * y s) volume a d ∧
      ∀ t ∈ Icc a d,
        y t - y a = ∫ s in a..t, (k s * y s + g s))
    (hk_nonpos : ∀ s, u < s → s ≤ b → k s ≤ 0)
    (hg_pos : ∀ s, u < s → s ≤ b → c ≤ g s) :
    0 < y b := by
  let mid : ℝ := (u + b) / 2
  have hum : u < mid := by dsimp [mid]; linarith
  have hmb : mid < b := by dsimp [mid]; linarith
  obtain ⟨hkM, hgM, hkyM, hyM⟩ := hlocal mid b hum hmb.le le_rfl
  have hJ : 0 < ∫ s in mid..b,
      Real.exp (-(∫ σ in mid..s, k σ)) * g s := by
    apply linear_source_integral_pos hmb hc hkM hgM
    intro s hs
    exact hg_pos s (hum.trans_le hs.1) hs.2
  have hSmall : ∀ᶠ a in 𝓝[>] u,
      |y a| < ∫ s in mid..b, Real.exp (-(∫ σ in mid..s, k σ)) * g s := by
    have ht := haxis.abs
    simpa using ht.eventually (eventually_lt_nhds (by simpa only [abs_zero] using hJ))
  obtain ⟨a, haSmall, ha⟩ := (hSmall.and (Ioo_mem_nhdsGT hum)).exists
  obtain ⟨hkA, hgA, hkyA, hyA⟩ := hlocal a mid ha.1 ha.2.le hmb.le
  have hMid : -|y a| ≤ y mid :=
    linear_solution_ge_neg_abs_initial ha.2.le hkA hgA hkyA hyA
      (fun s hs => hk_nonpos s (ha.1.trans_le hs.1) (hs.2.trans hmb.le))
      (fun s hs => (lt_of_lt_of_le hc (hg_pos s (ha.1.trans_le hs.1)
        (hs.2.trans hmb.le))).le)
  have hFinal := intervalIntegral.eq_exp_mul_add_integral_of_integral_eq
    hmb.le hkM hgM hkyM hyM (show b ∈ Icc mid b from ⟨hmb.le, le_rfl⟩)
  rw [hFinal]
  apply mul_pos (Real.exp_pos _)
  linarith


/-- The mass gap `r - 2m`, defined even outside the development. -/
def gap (S : Fields) (u t : ℝ) : ℝ :=
  S.r u t - 2 * S.m u t

/-- A coefficient of the outgoing mass-gap equation, defined off axis without a mass-ratio
denominator. -/
noncomputable def barrierCoeff (S : Fields) (u t : ℝ) : ℝ :=
  S.theta u t * S.theta u t * (S.r u t)⁻¹ * (S.lam u t)⁻¹

/-- The frozen mass integrand is exactly half the gap times the barrier coefficient on D. -/
theorem barrier_coeff_mul_gap_eq_two_mass_density
    {D : Set (ℝ × ℝ)} {S : Fields}
    (_hD : IsDomainOfDevelopment D)
    (hS : IsBVSolution D S)
    {u t : ℝ} (hut : (u, t) ∈ D) :
    barrierCoeff S u t * gap S u t = 2 * massV S u t := by
  have hr : S.r u t ≠ 0 := ne_of_gt (hS.solution.radius_pos (u, t) hut)
  obtain ⟨c, hc, hlam⟩ := hS.lam_bounded_below
  have hl : S.lam u t ≠ 0 := ne_of_gt (lt_of_lt_of_le hc (hlam (u, t) hut))
  unfold barrierCoeff gap massV
  field_simp

/-- On each compact outgoing interval, the mass gap solves a linear integral equation.
This uses no prior sign of the mass gap. -/
theorem gap_local_linear_equation
    {D : Set (ℝ × ℝ)} {S : Fields} {u v a b : ℝ}
    (hD : IsDomainOfDevelopment D)
    (hS : IsBVSolution D S)
    (huv : (u, v) ∈ D) (hua : u < a) (hab : a ≤ b) (hbv : b ≤ v) :
    IntervalIntegrable (fun s => -barrierCoeff S u s) volume a b ∧
    IntervalIntegrable (S.lam u) volume a b ∧
    IntervalIntegrable (fun s => -barrierCoeff S u s * gap S u s) volume a b ∧
    ∀ t ∈ Icc a b,
      gap S u t - gap S u a =
        ∫ s in a..t, (-barrierCoeff S u s * gap S u s + S.lam u s) := by
  have hk : IntervalIntegrable (barrierCoeff S u) volume a b := by
    exact barrier_coefficient_integrable hD hS huv hua hab hbv
  have hkNeg : IntervalIntegrable (fun s => -barrierCoeff S u s) volume a b := hk.neg
  have hseg := outgoing_primitive_on_subsegments hD huv hua hab hbv
  have hRfull := hS.solution.radius_out u a b hab (hseg b ⟨hab, le_rfl⟩)
  have hMfull := hS.solution.mass_out u a b hab (hseg b ⟨hab, le_rfl⟩)
  have hKg : IntervalIntegrable (fun s => -barrierCoeff S u s * gap S u s)
      volume a b := by
    have htwo : IntervalIntegrable (fun s => -(2 * massV S u s)) volume a b :=
      (hMfull.1.const_mul (2 : ℝ)).neg
    apply htwo.congr_uIoo
    intro s hs
    rw [uIoo_of_le hab] at hs
    have hsD : (u, s) ∈ D := hD.outgoing_mem huv
      (hua.trans_le (le_of_lt hs.1)) (le_trans (le_of_lt hs.2) hbv)
    have hid := barrier_coeff_mul_gap_eq_two_mass_density hD hS hsD
    dsimp only [Pi.neg_apply]
    linarith
  refine ⟨hkNeg, hRfull.1, hKg, ?_⟩
  intro t ht
  obtain ⟨hRi, hReq⟩ := hS.solution.radius_out u a t ht.1 (hseg t ht)
  obtain ⟨hMi, hMeq⟩ := hS.solution.mass_out u a t ht.1 (hseg t ht)
  have hKgAt : IntervalIntegrable (fun s => -barrierCoeff S u s * gap S u s)
      volume a t := hKg.mono_set (by
        rw [uIcc_of_le hab, uIcc_of_le ht.1]
        exact Icc_subset_Icc_right ht.2)
  have hId : (∫ s in a..t, -barrierCoeff S u s * gap S u s) =
      ∫ s in a..t, -(2 * massV S u s) := by
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1
    intro s hs
    have hsD : (u, s) ∈ D := hD.outgoing_mem huv
      (hua.trans_le hs.1.le) (hs.2.le.trans (ht.2.trans hbv))
    have hid := barrier_coeff_mul_gap_eq_two_mass_density hD hS hsD
    dsimp only [Pi.neg_apply]
    linarith
  calc
    gap S u t - gap S u a =
        (S.r u t - S.r u a) - 2 * (S.m u t - S.m u a) := by unfold gap; ring
    _ = (∫ s in a..t, S.lam u s) - 2 * (∫ s in a..t, massV S u s) := by
      rw [hReq, hMeq]
      rfl
    _ = (∫ s in a..t, S.lam u s) +
        (∫ s in a..t, -barrierCoeff S u s * gap S u s) := by
      rw [hId, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
      ring
    _ = ∫ s in a..t, (-barrierCoeff S u s * gap S u s + S.lam u s) := by
      rw [intervalIntegral.integral_add hKgAt hRi]
      ring

/-- The outgoing mass gap is strictly positive at every actual development point. -/
theorem gap_pos_aux
    {D : Set (ℝ × ℝ)} {S : Fields}
    (hD : IsDomainOfDevelopment D)
    (hS : IsBVSolution D S)
    {u v : ℝ} (huv : (u, v) ∈ D) : 0 < gap S u v := by
  obtain ⟨c, hc, hlam⟩ := hS.lam_bounded_below
  have hlt : u < v := (hD.1 huv).2
  have hRaxis : Tendsto (S.r u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [hD.axis_filter_eq huv] using
      hS.solution.radius_axis u (hD.axis_mem huv)
  have hMaxis : Tendsto (S.m u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa only [hD.axis_filter_eq huv] using
      hS.solution.mass_axis u (hD.axis_mem huv)
  have hGapAxis : Tendsto (gap S u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    have h2 : Tendsto (fun t => 2 * S.m u t) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
      simpa using tendsto_const_nhds.mul hMaxis
    change Tendsto (fun t => S.r u t - 2 * S.m u t) (𝓝[>] u) (𝓝 (0 : ℝ))
    simpa using hRaxis.sub h2
  apply linear_solution_pos_of_axis_trace (u := u) (b := v) (c := c)
    (k := fun t => -barrierCoeff S u t) (g := S.lam u) (y := gap S u)
    hlt hc hGapAxis
  · intro a d hua had hdv
    exact gap_local_linear_equation hD hS huv hua had hdv
  · intro t hut htv
    have htD := hD.outgoing_mem huv hut htv
    have hr := hS.solution.radius_pos (u, t) htD
    have hl := lt_of_lt_of_le hc (hlam (u, t) htD)
    have hθ : 0 ≤ S.theta u t * S.theta u t := mul_self_nonneg _
    have hCoeff : 0 ≤ barrierCoeff S u t := by
      unfold barrierCoeff
      exact mul_nonneg (mul_nonneg hθ (inv_nonneg.mpr hr.le))
        (inv_nonneg.mpr hl.le)
    linarith
  · intro t hut htv
    exact hlam (u, t) (hD.outgoing_mem huv hut htv)


end ChristodoulouBV.IsBVSolution

end
