module

public import ChristodoulouBV.BVSolution.Signs
public import ChristodoulouBV.ForMathlib.BoundedVariation.SliceFacts
import ChristodoulouBV.BVSolution.CoefficientBounds
import ChristodoulouBV.ForMathlib.BoundedVariation.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# Axis-side bounds and one-sided traces

Every actual outgoing slice approaches its axis point inside a development.
The corresponding incoming assertion needs an explicit contained segment.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.IsBVSolution

/-- The radius is bounded above and below by uniform multiples of the
coordinate distance from the axis. -/
theorem exists_uniform_radius_bounds
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S) :
    ∃ c K : ℝ, 0 < c ∧
      ∀ u v, (u, v) ∈ U →
        c * (v - u) ≤ S.r u v ∧ S.r u v ≤ K * (v - u) := by
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  obtain ⟨K, _, hK⟩ := h.exists_uniform_radius_upper
  exact ⟨c, K, hc, fun u v huv => ⟨h.radius_lower hlam huv, hK u v huv⟩⟩

/-- The mass is bounded by half of a uniform linear radius upper bound. -/
theorem mass_le_axis_distance
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {K u v : ℝ} (hK : ∀ p ∈ U, S.lam p.1 p.2 ≤ K)
    (huv : (u, v) ∈ U) :
    0 ≤ S.m u v ∧ S.m u v ≤ K * (v - u) / 2 := by
  have hm := h.mass_nonneg huv
  have hmr := h.two_mass_lt_radius huv
  have hr := h.radius_upper_of_lam_le hK huv
  constructor
  · exact hm
  · linarith

/-- On any outgoing slice containing a development point, the radius tends
to zero at its excluded axis endpoint. -/
theorem radius_tendsto_axis_out
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    Tendsto (S.r u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
  rw [← h.solution.development.axis_filter_eq huv]
  exact h.solution.radius_axis u (h.solution.development.axis_mem huv)

/-- On any outgoing slice containing a development point, the mass tends
to zero at its excluded axis endpoint. -/
theorem mass_tendsto_axis_out
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    Tendsto (S.m u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
  rw [← h.solution.development.axis_filter_eq huv]
  exact h.solution.mass_axis u (h.solution.development.axis_mem huv)

/-- The outgoing BV amplitude has a one-sided axis limit.  Its vanishing
requires the scalar variation argument, so the value is not specified here. -/
theorem exists_theta_axis_limit_out
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    ∃ L : ℝ, Tendsto (S.theta u) (𝓝[>] u) (𝓝 L) := by
  have hBV : BoundedVariationOn (S.theta u) {t | (u, t) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item5.choose_spec.1 u)
  obtain ⟨L, hL⟩ := hBV.exists_tendsto_right u
  refine ⟨L, ?_⟩
  have hfilter : 𝓝[{t | (u, t) ∈ U} ∩ Ioi u] u = 𝓝[>] u := by
    calc
      𝓝[{t | (u, t) ∈ U} ∩ Ioi u] u =
          𝓝[>] u ⊓ 𝓟 {t | (u, t) ∈ U} := by
            simp only [nhdsWithin, ← Filter.inf_principal]
            ac_rfl
      _ = 𝓝[>] u := h.solution.development.axis_filter_eq huv
  simpa only [hfilter] using hL

/-- The outgoing scalar field has a one-sided axis limit from its BV bound. -/
theorem exists_phi_axis_limit_out
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    ∃ L : ℝ, Tendsto (S.phi u) (𝓝[>] u) (𝓝 L) := by
  have hBV : BoundedVariationOn (S.phi u) {t | (u, t) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item3_variation.choose_spec.1 u)
  obtain ⟨L, hL⟩ := hBV.exists_tendsto_right u
  refine ⟨L, ?_⟩
  have hfilter : 𝓝[{t | (u, t) ∈ U} ∩ Ioi u] u = 𝓝[>] u := by
    calc
      𝓝[{t | (u, t) ∈ U} ∩ Ioi u] u =
          𝓝[>] u ⊓ 𝓟 {t | (u, t) ∈ U} := by
            simp only [nhdsWithin, ← Filter.inf_principal]
            ac_rfl
      _ = 𝓝[>] u := h.solution.development.axis_filter_eq huv
  simpa only [hfilter] using hL

/-- The derivative of the scalar field is integrable all the way to the
excluded outgoing axis.  Uniform BV variation bounds its absolute integral
on every compact subinterval, and an improper-integral criterion supplies
integrability on the half-open slice. -/
theorem scalar_deriv_integrable_on_axis_slice
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    IntegrableOn (deriv (S.phi u)) (Ioc u v) := by
  have hlt : u < v := (h.solution.development.wedge huv).2
  obtain ⟨C, hvar, _⟩ := h.item3_variation
  let B : ℝ := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have hvarB : eVariationOn (S.phi u) {t | (u, t) ∈ U} ≤ ENNReal.ofReal B :=
    (hvar u).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  let a : ℕ → ℝ := fun n => u + (v - u) * (1 / ((n : ℝ) + 1))
  have hau (n : ℕ) : u < a n := by
    dsimp [a]
    have hp : 0 < ((n : ℝ) + 1) := by positivity
    have hd : 0 < (v - u) * (1 / ((n : ℝ) + 1)) :=
      mul_pos (sub_pos.mpr hlt) (one_div_pos.mpr hp)
    linarith
  have hav (n : ℕ) : a n ≤ v := by
    dsimp [a]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hp : 1 ≤ ((n : ℝ) + 1) := by linarith
    have hone : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_iff₀ (by positivity)).2 (by linarith)
    nlinarith [mul_nonneg (sub_pos.mpr hlt).le (sub_nonneg.mpr hone)]
  have hInt (n : ℕ) : IntegrableOn (deriv (S.phi u)) (Ioc (a n) v) := by
    have hseg := h.solution.development.out_seg_subset huv (hau n) (hav n) le_rfl
    have hAC := h.item3_ac_out u (a n) v (hav n) hseg
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (hav n)).1
      hAC.intervalIntegrable_deriv
  have hbound (n : ℕ) :
      ∫ t in Ioc (a n) v, ‖deriv (S.phi u) t‖ ≤ B := by
    have hsubset : Icc (a n) v ⊆ {t | (u, t) ∈ U} := by
      intro t ht
      exact h.solution.development.outgoing_mem huv
        ((hau n).trans_le ht.1) ht.2
    have hBV : BoundedVariationOn (S.phi u) (Icc (a n) v) :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        ((eVariationOn.mono (S.phi u) hsubset).trans hvarB)
    have hbound' := hBV.integral_abs_deriv_le_eVariationOn (hav n)
    have hvar' : (eVariationOn (S.phi u) (Icc (a n) v)).toReal ≤ B :=
      ENNReal.toReal_le_of_le_ofReal hB
        ((eVariationOn.mono (S.phi u) hsubset).trans hvarB)
    rw [intervalIntegral.integral_of_le (hav n)] at hbound'
    simpa only [Real.norm_eq_abs] using hbound'.trans hvar'
  have ha : Tendsto a atTop (𝓝 u) := by
    have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hconstu : Tendsto (fun _ : ℕ => u) atTop (𝓝 u) := tendsto_const_nhds
    have hconstd : Tendsto (fun _ : ℕ => v - u) atTop (𝓝 (v - u)) :=
      tendsto_const_nhds
    have hh := hconstu.add (hconstd.mul hzero)
    simpa only [a, mul_zero, add_zero] using hh
  exact integrableOn_Ioc_of_intervalIntegral_norm_bounded_left hInt ha
    (Filter.Eventually.of_forall hbound)

/-- The outgoing BV amplitude tends to zero at the axis.  If its BV trace
were nonzero, the scalar derivative identity and the linear upper radius
bound would force a nonintegrable reciprocal distance. -/
theorem theta_tendsto_zero_axis_out
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    Tendsto (S.theta u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
  obtain ⟨L, hL⟩ := h.exists_theta_axis_limit_out huv
  suffices hL0 : L = 0 by simpa only [hL0] using hL
  by_contra hL0
  let c : ℝ := |L| / 2
  have hc : 0 < c := by
    dsimp [c]
    have hp : 0 < |L| := abs_pos.mpr hL0
    linarith
  have hcL : c < |L| := by
    have hp : 0 < |L| := abs_pos.mpr hL0
    dsimp [c]
    linarith
  have hev : {t : ℝ | c < |S.theta u t|} ∈ 𝓝[>] u :=
    hL.abs.eventually (eventually_gt_nhds hcL)
  obtain ⟨d, hud, hd⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have huvlt : u < v := (h.solution.development.wedge huv).2
  let b : ℝ := (u + min d v) / 2
  have hub : u < b := by dsimp [b]; linarith [lt_min hud huvlt]
  have hbd : b < d := by
    have hmin : u < min d v := lt_min hud huvlt
    dsimp [b]
    linarith [min_le_left d v]
  have hbv : b ≤ v := by dsimp [b]; linarith [min_le_right d v]
  obtain ⟨K, hK, _⟩ := h.exists_uniform_radius_upper
  have hbU : (u, b) ∈ U := h.solution.development.outgoing_mem huv hub hbv
  have hKpos : 0 < K := by
    have hrad := h.radius_upper_of_lam_le hK hbU
    have hrpos := h.solution.radius_pos (u, b) hbU
    nlinarith [sub_pos.mpr hub]
  have hderiv : IntegrableOn (deriv (S.phi u)) (Ioc u b) :=
    (h.scalar_deriv_integrable_on_axis_slice huv).mono_set
      (Ioc_subset_Ioc_right hbv)
  have hscaled : IntegrableOn
      (fun t => (K / c) * deriv (S.phi u) t) (Ioc u b) :=
    hderiv.const_mul (K / c)
  have hinv : IntegrableOn (fun t => (t - u)⁻¹) (Ioc u b) := by
    apply Integrable.mono hscaled
    · exact ((measurable_id.sub_const u).inv).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [h.scalar_ae_deriv_out_on_slice huv] with t hφ ht
      have htv : t ∈ Ioc u v := ⟨ht.1, ht.2.trans hbv⟩
      have htU := h.solution.development.outgoing_mem huv ht.1 htv.2
      have hrpos := h.solution.radius_pos (u, t) htU
      have hrle := h.radius_upper_of_lam_le hK htU
      have hθ : c < |S.theta u t| := hd ⟨ht.1, ht.2.trans_lt hbd⟩
      have hx : 0 < t - u := sub_pos.mpr ht.1
      have hcross₁ : c * S.r u t ≤ c * (K * (t - u)) :=
        mul_le_mul_of_nonneg_left hrle hc.le
      have hcross₂ : (K * (t - u)) * c ≤
          (K * (t - u)) * |S.theta u t| :=
        mul_le_mul_of_nonneg_left hθ.le
          (mul_nonneg hKpos.le hx.le)
      rw [hφ htv]
      simp only [Real.norm_eq_abs, abs_inv, abs_of_pos hx,
        abs_mul, abs_of_pos (div_pos hKpos hc), abs_div, abs_of_pos hrpos]
      rw [inv_eq_one_div]
      have hrewrite : K / c * (|S.theta u t| / S.r u t) =
          K * |S.theta u t| / (c * S.r u t) := by ring
      rw [hrewrite]
      apply (div_le_div_iff₀ hx (mul_pos hc hrpos)).2
      nlinarith [hcross₁, hcross₂]
  have hi : IntervalIntegrable (fun t => (t - u)⁻¹) volume u b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hub.le).2 hinv
  rcases intervalIntegrable_sub_inv_iff.mp hi with heq | hnot
  · exact (ne_of_lt hub heq).elim
  · rw [uIcc_of_le hub.le] at hnot
    exact (hnot ⟨le_rfl, hub.le⟩).elim

/-- A small outgoing scalar amplitude bounds the mass by the corresponding
linear distance to the axis.  The mass primitive is integrated from compact
segments and the axis value is recovered by its frozen trace. -/
theorem mass_le_axis_distance_of_theta_sq_le
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v c ε : ℝ} (huv : (u, v) ∈ U) (hc : 0 < c) (hε : 0 ≤ ε)
    (hlam : ∀ p ∈ U, c ≤ S.lam p.1 p.2)
    (hθ : ∀ t, u < t → t ≤ v → S.theta u t ^ 2 ≤ 2 * c * ε) :
    S.m u v ≤ ε * (v - u) := by
  let hD := h.solution.development
  have huvlt : u < v := (hD.wedge huv).2
  have hlim : Tendsto (fun a : ℝ => S.m u a + ε * (v - a))
      (𝓝[>] u) (𝓝 (ε * (v - u))) := by
    have hcont : Tendsto (fun a : ℝ => ε * (v - a)) (𝓝[>] u)
        (𝓝 (ε * (v - u))) :=
      ((show Continuous (fun a : ℝ => ε * (v - a)) by fun_prop).tendsto u).mono_left
        inf_le_left
    simpa using (h.mass_tendsto_axis_out huv).add hcont
  have hbound : ∀ᶠ a in 𝓝[>] u,
      S.m u v ≤ S.m u a + ε * (v - a) := by
    filter_upwards [Ioo_mem_nhdsGT huvlt] with a ha
    have hseg := hD.out_seg_subset huv ha.1 ha.2.le le_rfl
    obtain ⟨hint, heq⟩ := h.solution.mass_out u a v ha.2.le hseg
    have hconst : IntervalIntegrable (fun _ : ℝ => ε) volume a v :=
      intervalIntegrable_const
    have hmono : (∫ t in a..v,
        (1 - 2 * S.m u t / S.r u t) * S.theta u t ^ 2 / (2 * S.lam u t)) ≤
        ∫ _ in a..v, ε := by
      apply intervalIntegral.integral_mono_on ha.2.le hint hconst
      intro t ht
      have htU := hD.outgoing_mem huv (ha.1.trans_le ht.1) ht.2
      have hmu := h.mass_ratio_bounds htU
      have htheta := hθ t (ha.1.trans_le ht.1) ht.2
      have hlam := hlam (u, t) htU
      have hden : 0 < 2 * S.lam u t := mul_pos (by norm_num) (hc.trans_le hlam)
      have hnum : (1 - 2 * S.m u t / S.r u t) * S.theta u t ^ 2 ≤
          S.theta u t ^ 2 := by
        nlinarith [mul_nonneg hmu.1 (sq_nonneg (S.theta u t))]
      have hlast : 2 * c * ε ≤ 2 * S.lam u t * ε := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hlam) hε]
      exact (div_le_iff₀ hden).2 (by linarith)
    rw [intervalIntegral.integral_const] at hmono
    simp only [smul_eq_mul] at hmono
    linarith
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hbound

/-- The outgoing mass is little-oh of the coordinate distance to the axis. -/
theorem mass_div_axis_distance_tendsto_zero
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    Tendsto (fun t => S.m u t / (t - u)) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
  have huvlt : u < v := (h.solution.development.wedge huv).2
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  have hθsq : Tendsto (fun t => S.theta u t ^ 2) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa using (h.theta_tendsto_zero_axis_out huv).pow 2
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [Ioo_mem_nhdsGT huvlt] with t ht
    have htU := h.solution.development.outgoing_mem huv ht.1 ht.2.le
    have hm := h.mass_nonneg htU
    have hx : 0 < t - u := sub_pos.mpr ht.1
    have hdiv : 0 ≤ S.m u t / (t - u) := div_nonneg hm hx.le
    linarith
  · intro ε hε
    let η : ℝ := ε / 2
    have hη : 0 ≤ η := by dsimp [η]; linarith
    have hηlt : η < ε := by dsimp [η]; linarith
    have hsmall : 0 < 2 * c * η := by positivity
    have hev : {t : ℝ | S.theta u t ^ 2 < 2 * c * η} ∈ 𝓝[>] u :=
      hθsq.eventually (eventually_lt_nhds hsmall)
    obtain ⟨d, hud, hd⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
    let b : ℝ := (u + min d v) / 2
    have hub : u < b := by dsimp [b]; linarith [lt_min hud huvlt]
    have hbd : b < d := by
      have hmin : u < min d v := lt_min hud huvlt
      dsimp [b]
      linarith [min_le_left d v]
    have hbv : b ≤ v := by dsimp [b]; linarith [min_le_right d v]
    filter_upwards [Ioo_mem_nhdsGT hub] with t ht
    have htU := h.solution.development.outgoing_mem huv ht.1 (ht.2.le.trans hbv)
    have hmass : S.m u t ≤ η * (t - u) :=
      h.mass_le_axis_distance_of_theta_sq_le htU hc hη hlam (by
        intro s hus hst
        exact (hd ⟨hus, hst.trans_lt (ht.2.trans hbd)⟩).le)
    have hx : 0 < t - u := sub_pos.mpr ht.1
    have hdiv : S.m u t / (t - u) ≤ η := (div_le_iff₀ hx).2 hmass
    exact hdiv.trans_lt hηlt

/-- The outgoing Hawking mass ratio tends to zero at the axis. -/
theorem mass_ratio_tendsto_zero_axis_out
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    Tendsto (fun t => 2 * S.m u t / S.r u t) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  have huvlt : u < v := (h.solution.development.wedge huv).2
  have hupper : ∀ᶠ t in 𝓝[>] u,
      2 * S.m u t / S.r u t ≤ (2 / c) * (S.m u t / (t - u)) := by
    filter_upwards [Ioo_mem_nhdsGT huvlt] with t ht
    have htU := h.solution.development.outgoing_mem huv ht.1 ht.2.le
    have hm := h.mass_nonneg htU
    have hr := h.radius_lower hlam htU
    have hrpos := h.solution.radius_pos (u, t) htU
    have hx : 0 < t - u := sub_pos.mpr ht.1
    have hrewrite : (2 / c) * (S.m u t / (t - u)) =
        2 * S.m u t / (c * (t - u)) := by
      field_simp
    rw [hrewrite]
    apply (div_le_div_iff₀ hrpos (mul_pos hc hx)).2
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hm)
      (sub_nonneg.mpr hr)]
  have hlower : ∀ᶠ t in 𝓝[>] u,
      0 ≤ 2 * S.m u t / S.r u t := by
    filter_upwards [Ioo_mem_nhdsGT huvlt] with t ht
    exact (h.mass_ratio_bounds
      (h.solution.development.outgoing_mem huv ht.1 ht.2.le)).1
  have hzero : Tendsto (fun t => (2 / c) * (S.m u t / (t - u)))
      (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa using (h.mass_div_axis_distance_tendsto_zero huv).const_mul (2 / c)
  exact squeeze_zero' hlower hupper hzero

/-- The outgoing mass is the limit of its off-axis characteristic integrals.
The expression uses the frozen integrable density on each compact segment;
integrability on the entire half-open slice is a separate assertion. -/
theorem mass_out_integral_tendsto_axis
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    Tendsto (fun a => ∫ t in a..v, massV S u t)
      (𝓝[>] u) (𝓝 (S.m u v)) := by
  have huvlt : u < v := (h.solution.development.wedge huv).2
  have heq : ∀ᶠ a in 𝓝[>] u,
      (∫ t in a..v, massV S u t) = S.m u v - S.m u a := by
    filter_upwards [Ioo_mem_nhdsGT huvlt] with a ha
    have hseg := h.solution.development.out_seg_subset huv ha.1 ha.2.le le_rfl
    exact (h.solution.mass_out u a v ha.2.le hseg).2.symm
  have hlim : Tendsto (fun a : ℝ => S.m u v - S.m u a)
      (𝓝[>] u) (𝓝 (S.m u v)) := by
    simpa using tendsto_const_nhds.sub (h.mass_tendsto_axis_out huv)
  exact hlim.congr' (heq.mono fun _ hh => hh.symm)

/-- The nonnegative outgoing mass density is integrable up to the excluded
axis endpoint. -/
theorem mass_density_integrable_on_axis_slice
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    IntegrableOn (massV S u) (Ioc u v) := by
  have huvlt : u < v := (h.solution.development.wedge huv).2
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
  have hprim (n : ℕ) :
      IntervalPrimitive (S.m u) (massV S u) (a n) v := by
    have hseg := h.solution.development.out_seg_subset huv (hau n) (hav n) le_rfl
    change IntervalPrimitive (S.m u)
      (fun t => (1 - 2 * S.m u t / S.r u t) * S.theta u t ^ 2 /
        (2 * S.lam u t)) (a n) v
    exact h.solution.mass_out u (a n) v (hav n) hseg
  have hInt (n : ℕ) : IntegrableOn (massV S u) (Ioc (a n) v) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (hav n)).1 (hprim n).1
  have hbound (n : ℕ) :
      ∫ t in Ioc (a n) v, ‖massV S u t‖ ≤ S.m u v := by
    have hnorm : (∫ t in Ioc (a n) v, ‖massV S u t‖) =
        ∫ t in Ioc (a n) v, massV S u t := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      have htU := h.solution.development.outgoing_mem huv
        ((hau n).trans_le ht.1.le) ht.2
      simp only [Real.norm_eq_abs, abs_of_nonneg
        (mass_density_nonneg h.solution.development h htU)]
    have heq := (hprim n).2
    rw [intervalIntegral.integral_of_le (hav n)] at heq
    rw [hnorm, ← heq]
    linarith [h.mass_nonneg
      (h.solution.development.outgoing_mem huv (hau n) (hav n))]
  have ha : Tendsto a atTop (𝓝 u) := by
    have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hconstu : Tendsto (fun _ : ℕ => u) atTop (𝓝 u) := tendsto_const_nhds
    have hconstd : Tendsto (fun _ : ℕ => v - u) atTop (𝓝 (v - u)) :=
      tendsto_const_nhds
    simpa only [a, mul_zero, add_zero] using hconstu.add (hconstd.mul hzero)
  exact integrableOn_Ioc_of_intervalIntegral_norm_bounded_left hInt ha
    (Filter.Eventually.of_forall hbound)

/-- The outgoing mass equals the integral of the frozen mass density over
the full half-open axis-to-point slice. -/
theorem mass_out_integral_from_axis
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    S.m u v = ∫ t in u..v, massV S u t := by
  have huvlt : u < v := (h.solution.development.wedge huv).2
  have hint : IntervalIntegrable (massV S u) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huvlt.le).2
      (h.mass_density_integrable_on_axis_slice huv)
  let F : ℝ → ℝ := fun a => ∫ t in u..a, massV S u t
  have hAC : AbsolutelyContinuousOnInterval F u v := by
    exact hint.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hright : Tendsto (fun a : ℝ => a) (𝓝[>] u) (𝓝[Icc u v] u) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left inf_le_left,
      mem_of_superset (Ioo_mem_nhdsGT huvlt) (fun a ha => ⟨ha.1.le, ha.2.le⟩)⟩
  have hF : Tendsto F (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    have hcont : ContinuousOn F (Icc u v) := by
      simpa only [uIcc_of_le huvlt.le] using hAC.continuousOn
    have hh := (hcont.continuousWithinAt
      (show u ∈ Icc u v from ⟨le_rfl, huvlt.le⟩)).tendsto.comp hright
    simpa only [F, Function.comp_def, intervalIntegral.integral_same] using hh
  have hsplit : ∀ᶠ a in 𝓝[>] u,
      (∫ t in a..v, massV S u t) = (∫ t in u..v, massV S u t) - F a := by
    filter_upwards [Ioo_mem_nhdsGT huvlt] with a ha
    have hleft : IntervalIntegrable (massV S u) volume u a :=
      hint.mono_set (by
        rw [uIcc_of_le huvlt.le, uIcc_of_le ha.1.le]
        exact Icc_subset_Icc_right ha.2.le)
    have hright : IntervalIntegrable (massV S u) volume a v :=
      hint.mono_set (by
        rw [uIcc_of_le huvlt.le, uIcc_of_le ha.2.le]
        exact Icc_subset_Icc_left ha.1.le)
    have hh := intervalIntegral.integral_add_adjacent_intervals hleft hright
    dsimp [F]
    linarith
  have hlim : Tendsto (fun a => ∫ t in a..v, massV S u t)
      (𝓝[>] u) (𝓝 (∫ t in u..v, massV S u t)) := by
    have hh : Tendsto (fun a => (∫ t in u..v, massV S u t) - F a)
        (𝓝[>] u) (𝓝 (∫ t in u..v, massV S u t)) := by
      simpa using tendsto_const_nhds.sub hF
    exact hh.congr' (hsplit.mono fun _ hEq => hEq.symm)
  exact tendsto_nhds_unique (h.mass_out_integral_tendsto_axis huv) hlim

end ChristodoulouBV.IsBVSolution

end
