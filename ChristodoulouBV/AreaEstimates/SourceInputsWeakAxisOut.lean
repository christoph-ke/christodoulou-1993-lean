module

public import ChristodoulouBV.AreaEstimates.SourceInputsWeakCalculus

/-!
# Outgoing zero-axis mass ratio from directional BV

Only reduced solution identities, directional BV/AC and the displayed
pointwise geometry enter these proofs. No BV axis item is assumed.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.SourceInputsWeak

open IsBVSolution

/-- On any outgoing slice containing a development point, the radius tends
to zero at its excluded axis endpoint. -/
theorem radius_tendsto_axis_out
    {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    Tendsto (S.r u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
  rw [← h.development.axis_filter_eq huv]
  exact h.radius_axis u (h.development.axis_mem huv)

/-- On any outgoing slice containing a development point, the mass tends
to zero at its excluded axis endpoint. -/
theorem mass_tendsto_axis_out
    {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    Tendsto (S.m u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
  rw [← h.development.axis_filter_eq huv]
  exact h.mass_axis u (h.development.axis_mem huv)

/-- The outgoing BV amplitude has a one-sided axis limit.  Its vanishing
requires the scalar variation argument, so the value is not specified here. -/
theorem exists_theta_axis_limit_out
    {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsSolution U S)
    (hThetaBV : ∀ u, BoundedVariationOn (S.theta u) {v | (u, v) ∈ U})
    {u v : ℝ} (huv : (u, v) ∈ U) :
    ∃ L : ℝ, Tendsto (S.theta u) (𝓝[>] u) (𝓝 L) := by
  have hBV : BoundedVariationOn (S.theta u) {t | (u, t) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_of_eq (ENNReal.ofReal_toReal (hThetaBV u)).symm)
  obtain ⟨L, hL⟩ := hBV.exists_tendsto_right u
  refine ⟨L, ?_⟩
  have hfilter : 𝓝[{t | (u, t) ∈ U} ∩ Ioi u] u = 𝓝[>] u := by
    calc
      𝓝[{t | (u, t) ∈ U} ∩ Ioi u] u =
          𝓝[>] u ⊓ 𝓟 {t | (u, t) ∈ U} := by
            simp only [nhdsWithin, ← Filter.inf_principal]
            ac_rfl
      _ = 𝓝[>] u := h.development.axis_filter_eq huv
  simpa only [hfilter] using hL

/-- The derivative of the scalar field is integrable all the way to the
excluded outgoing axis. Finite section variation bounds its absolute integral
on every compact subinterval, and an improper-integral criterion supplies
integrability on the half-open slice. -/
theorem scalar_deriv_integrable_on_axis_slice
    {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsSolution U S)
    (hACOut : ∀ u a b, a ≤ b → outSeg u a b ⊆ U →
      AbsolutelyContinuousOnInterval (S.phi u) a b)
    (hPhiBVOut : ∀ u, BoundedVariationOn (S.phi u) {v | (u, v) ∈ U})
    {u v : ℝ} (huv : (u, v) ∈ U) :
    IntegrableOn (deriv (S.phi u)) (Ioc u v) := by
  have hlt : u < v := (h.development.wedge huv).2
  let C : ℝ := (eVariationOn (S.phi u) {t | (u, t) ∈ U}).toReal
  have hvar (x : ℝ) := le_of_eq (ENNReal.ofReal_toReal (hPhiBVOut x)).symm
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
    have hseg := h.development.out_seg_subset huv (hau n) (hav n) le_rfl
    have hAC := hACOut u (a n) v (hav n) hseg
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (hav n)).1
      hAC.intervalIntegrable_deriv
  have hbound (n : ℕ) :
      ∫ t in Ioc (a n) v, ‖deriv (S.phi u) t‖ ≤ B := by
    have hsubset : Icc (a n) v ⊆ {t | (u, t) ∈ U} := by
      intro t ht
      exact h.development.outgoing_mem huv
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
    {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsSolution U S)
    (hR : ∃ K : ℝ, ∀ u v, (u, v) ∈ U → S.r u v ≤ K * (v - u))
    (hACOut : ∀ u a b, a ≤ b → outSeg u a b ⊆ U →
      AbsolutelyContinuousOnInterval (S.phi u) a b)
    (hPhiBVOut : ∀ u, BoundedVariationOn (S.phi u) {v | (u, v) ∈ U})
    (hThetaBV : ∀ u, BoundedVariationOn (S.theta u) {v | (u, v) ∈ U})
    {u v : ℝ} (huv : (u, v) ∈ U) :
    Tendsto (S.theta u) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
  obtain ⟨L, hL⟩ := (exists_theta_axis_limit_out h hThetaBV) huv
  suffices hL0 : L = 0 by simpa only [hL0] using hL
  by_contra hL0
  let k : ℝ := |L| / 2
  have hk : 0 < k := by
    dsimp [k]
    have hp : 0 < |L| := abs_pos.mpr hL0
    linarith
  have hcL : k < |L| := by
    have hp : 0 < |L| := abs_pos.mpr hL0
    dsimp [k]
    linarith
  have hev : {t : ℝ | k < |S.theta u t|} ∈ 𝓝[>] u :=
    hL.abs.eventually (eventually_gt_nhds hcL)
  obtain ⟨d, hud, hd⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have huvlt : u < v := (h.development.wedge huv).2
  let b : ℝ := (u + min d v) / 2
  have hub : u < b := by dsimp [b]; linarith [lt_min hud huvlt]
  have hbd : b < d := by
    have hmin : u < min d v := lt_min hud huvlt
    dsimp [b]
    linarith [min_le_left d v]
  have hbv : b ≤ v := by dsimp [b]; linarith [min_le_right d v]
  obtain ⟨K, hK⟩ := hR
  have hbU : (u, b) ∈ U := h.development.outgoing_mem huv hub hbv
  have hKpos : 0 < K := by
    have hrad := hK u b hbU
    have hrpos := h.radius_pos (u, b) hbU
    nlinarith [sub_pos.mpr hub]
  have hderiv : IntegrableOn (deriv (S.phi u)) (Ioc u b) :=
    ((scalar_deriv_integrable_on_axis_slice h hACOut hPhiBVOut) huv).mono_set
      (Ioc_subset_Ioc_right hbv)
  have hscaled : IntegrableOn
      (fun t => (K / k) * deriv (S.phi u) t) (Ioc u b) :=
    hderiv.const_mul (K / k)
  have hinv : IntegrableOn (fun t => (t - u)⁻¹) (Ioc u b) := by
    apply Integrable.mono hscaled
    · exact ((measurable_id.sub_const u).inv).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [(scalar_ae_deriv_out_on_slice h hACOut) huv] with t hφ ht
      have htv : t ∈ Ioc u v := ⟨ht.1, ht.2.trans hbv⟩
      have htU := h.development.outgoing_mem huv ht.1 htv.2
      have hrpos := h.radius_pos (u, t) htU
      have hrle := hK u t htU
      have hθ : k < |S.theta u t| := hd ⟨ht.1, ht.2.trans_lt hbd⟩
      have hx : 0 < t - u := sub_pos.mpr ht.1
      have hcross₁ : k * S.r u t ≤ k * (K * (t - u)) :=
        mul_le_mul_of_nonneg_left hrle hk.le
      have hcross₂ : (K * (t - u)) * k ≤
          (K * (t - u)) * |S.theta u t| :=
        mul_le_mul_of_nonneg_left hθ.le
          (mul_nonneg hKpos.le hx.le)
      rw [hφ htv]
      simp only [Real.norm_eq_abs, abs_inv, abs_of_pos hx,
        abs_mul, abs_of_pos (div_pos hKpos hk), abs_div, abs_of_pos hrpos]
      rw [inv_eq_one_div]
      have hrewrite : K / k * (|S.theta u t| / S.r u t) =
          K * |S.theta u t| / (k * S.r u t) := by ring
      rw [hrewrite]
      apply (div_le_div_iff₀ hx (mul_pos hk hrpos)).2
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
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (h : IsSolution U S)
    (hc : 0 < c)
    (hlam : ∀ p ∈ U, c ≤ S.lam p.1 p.2)
    (hmu : ∀ p ∈ U, 0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1)
    {u v ε : ℝ} (huv : (u, v) ∈ U) (hε : 0 ≤ ε)
    (hθ : ∀ t, u < t → t ≤ v → S.theta u t ^ 2 ≤ 2 * c * ε) :
    S.m u v ≤ ε * (v - u) := by
  let hD := h.development
  have huvlt : u < v := (hD.wedge huv).2
  have hlim : Tendsto (fun a : ℝ => S.m u a + ε * (v - a))
      (𝓝[>] u) (𝓝 (ε * (v - u))) := by
    have hcont : Tendsto (fun a : ℝ => ε * (v - a)) (𝓝[>] u)
        (𝓝 (ε * (v - u))) :=
      ((show Continuous (fun a : ℝ => ε * (v - a)) by fun_prop).tendsto u).mono_left
        inf_le_left
    simpa using ((mass_tendsto_axis_out h) huv).add hcont
  have hbound : ∀ᶠ a in 𝓝[>] u,
      S.m u v ≤ S.m u a + ε * (v - a) := by
    filter_upwards [Ioo_mem_nhdsGT huvlt] with a ha
    have hseg := hD.out_seg_subset huv ha.1 ha.2.le le_rfl
    obtain ⟨hint, heq⟩ := h.mass_out u a v ha.2.le hseg
    have hconst : IntervalIntegrable (fun _ : ℝ => ε) volume a v :=
      intervalIntegrable_const
    have hmono : (∫ t in a..v,
        (1 - 2 * S.m u t / S.r u t) * S.theta u t ^ 2 / (2 * S.lam u t)) ≤
        ∫ _ in a..v, ε := by
      apply intervalIntegral.integral_mono_on ha.2.le hint hconst
      intro t ht
      have htU := hD.outgoing_mem huv (ha.1.trans_le ht.1) ht.2
      have hmu := hmu _ htU
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
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (h : IsSolution U S)
    (hc : 0 < c)
    (hlam : ∀ p ∈ U, c ≤ S.lam p.1 p.2)
    (hR : ∃ K : ℝ, ∀ u v, (u, v) ∈ U → S.r u v ≤ K * (v - u))
    (hmu : ∀ p ∈ U, 0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1)
    (hACOut : ∀ u a b, a ≤ b → outSeg u a b ⊆ U →
      AbsolutelyContinuousOnInterval (S.phi u) a b)
    (hPhiBVOut : ∀ u, BoundedVariationOn (S.phi u) {v | (u, v) ∈ U})
    (hThetaBV : ∀ u, BoundedVariationOn (S.theta u) {v | (u, v) ∈ U})
    {u v : ℝ} (huv : (u, v) ∈ U) :
    Tendsto (fun t => S.m u t / (t - u)) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
  have huvlt : u < v := (h.development.wedge huv).2
  have hθsq : Tendsto (fun t => S.theta u t ^ 2) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa using ((theta_tendsto_zero_axis_out h hR hACOut hPhiBVOut hThetaBV) huv).pow 2
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [Ioo_mem_nhdsGT huvlt] with t ht
    have htU := h.development.outgoing_mem huv ht.1 ht.2.le
    have hm := (mass_nonneg h hmu) htU
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
    have htU := h.development.outgoing_mem huv ht.1 (ht.2.le.trans hbv)
    have hmass : S.m u t ≤ η * (t - u) :=
      (mass_le_axis_distance_of_theta_sq_le h hc hlam hmu) htU hη (by
        intro s hus hst
        exact (hd ⟨hus, hst.trans_lt (ht.2.trans hbd)⟩).le)
    have hx : 0 < t - u := sub_pos.mpr ht.1
    have hdiv : S.m u t / (t - u) ≤ η := (div_le_iff₀ hx).2 hmass
    exact hdiv.trans_lt hηlt

/-- The outgoing Hawking mass ratio tends to zero at the axis. -/
theorem mass_ratio_tendsto_zero_axis_out
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (h : IsSolution U S)
    (hc : 0 < c)
    (hlam : ∀ p ∈ U, c ≤ S.lam p.1 p.2)
    (hR : ∃ K : ℝ, ∀ u v, (u, v) ∈ U → S.r u v ≤ K * (v - u))
    (hmu : ∀ p ∈ U, 0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1)
    (hACOut : ∀ u a b, a ≤ b → outSeg u a b ⊆ U →
      AbsolutelyContinuousOnInterval (S.phi u) a b)
    (hPhiBVOut : ∀ u, BoundedVariationOn (S.phi u) {v | (u, v) ∈ U})
    (hThetaBV : ∀ u, BoundedVariationOn (S.theta u) {v | (u, v) ∈ U})
    {u v : ℝ} (huv : (u, v) ∈ U) :
    Tendsto (fun t => 2 * S.m u t / S.r u t) (𝓝[>] u) (𝓝 (0 : ℝ)) := by
  have huvlt : u < v := (h.development.wedge huv).2
  have hupper : ∀ᶠ t in 𝓝[>] u,
      2 * S.m u t / S.r u t ≤ (2 / c) * (S.m u t / (t - u)) := by
    filter_upwards [Ioo_mem_nhdsGT huvlt] with t ht
    have htU := h.development.outgoing_mem huv ht.1 ht.2.le
    have hm := (mass_nonneg h hmu) htU
    have hr := (radius_lower h hlam) htU
    have hrpos := h.radius_pos (u, t) htU
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
    exact (hmu _
      (h.development.outgoing_mem huv ht.1 ht.2.le)).1
  have hzero : Tendsto (fun t => (2 / c) * (S.m u t / (t - u)))
      (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    simpa using ((mass_div_axis_distance_tendsto_zero h hc hlam hR hmu hACOut hPhiBVOut hThetaBV)
      huv).const_mul (2 / c)
  exact squeeze_zero' hlower hupper hzero

end ChristodoulouBV.SourceInputsWeak

end
