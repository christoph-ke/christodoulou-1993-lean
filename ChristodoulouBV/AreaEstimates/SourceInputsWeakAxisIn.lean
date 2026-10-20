module

public import ChristodoulouBV.AreaEstimates.SourceInputsWeakAxisOut

/-!
# Incoming zero-axis mass ratio on accessible half-open rays

Only reduced solution identities, directional BV/AC and the displayed
pointwise geometry enter these proofs. No BV axis item is assumed.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.SourceInputsWeak

open IsBVSolution

/-- On a complete incoming half-open ray, the mass tends to zero at the
diagonal. The estimate uses only `0 ≤ 2m < r` and the global radius upper
bound. -/
theorem mass_tendsto_axis_in_of_half_open_access
    {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsSolution U S)
    (hR : ∃ K : ℝ, ∀ u v, (u, v) ∈ U → S.r u v ≤ K * (v - u))
    (hmu : ∀ p ∈ U, 0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1)
    {u v : ℝ} (huv : u < v)
    (haccess : ∀ s ∈ Ico u v, (s, v) ∈ U) :
    Tendsto (fun s => S.m s v) (𝓝[<] v) (𝓝 (0 : ℝ)) := by
  obtain ⟨K, hK⟩ := hR
  have hlower : ∀ᶠ s in 𝓝[<] v, 0 ≤ S.m s v := by
    filter_upwards [Ioo_mem_nhdsLT huv] with s hs
    exact (mass_nonneg h hmu) (haccess s ⟨hs.1.le, hs.2⟩)
  have hupper : ∀ᶠ s in 𝓝[<] v,
      S.m s v ≤ K * (v - s) / 2 := by
    filter_upwards [Ioo_mem_nhdsLT huv] with s hs
    have hsv := haccess s ⟨hs.1.le, hs.2⟩
    have hm := (div_lt_iff₀ (h.radius_pos (s, v) hsv)).mp (hmu _ hsv).2
    have hr := hK s v hsv
    linarith
  have hzero : Tendsto (fun s => K * (v - s) / 2)
      (𝓝[<] v) (𝓝 (0 : ℝ)) := by
    have hid : Tendsto (fun s : ℝ => s) (𝓝[<] v) (𝓝 v) :=
      tendsto_id.mono_left inf_le_left
    have hconst : Tendsto (fun _ : ℝ => v) (𝓝[<] v) (𝓝 v) := tendsto_const_nhds
    simpa only [sub_self, mul_zero, zero_div] using
      ((hconst.sub hid).const_mul K).div_const 2
  exact squeeze_zero' hlower hupper hzero

/-- The incoming mass density is nonpositive at each development point. -/
theorem massInDensity_nonpos
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (hc : 0 < c)
    (hnu : ∀ p ∈ U, S.nu p.1 p.2 ≤ -c)
    (hmu : ∀ p ∈ U, 0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1)
    {s v : ℝ} (hsv : (s, v) ∈ U) : massInDensity S s v ≤ 0 := by
  have hnu : S.nu s v < 0 := lt_of_le_of_lt (hnu _ hsv) (neg_lt_zero.mpr hc)
  have hgap : 0 ≤ 1 - 2 * S.m s v / S.r s v := by
    have := (hmu _ hsv).2
    linarith
  unfold massInDensity
  exact div_nonpos_of_nonneg_of_nonpos
    (mul_nonneg hgap (sq_nonneg _)) (by linarith)

/-- The incoming mass density is integrable up to the missing diagonal
endpoint on a complete half-open incoming ray. -/
theorem massInDensity_integrable_of_half_open_access
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (h : IsSolution U S)
    (hc : 0 < c)
    (hnu : ∀ p ∈ U, S.nu p.1 p.2 ≤ -c)
    (hmu : ∀ p ∈ U, 0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1)
    {u v : ℝ} (huv : u < v)
    (haccess : ∀ s ∈ Ico u v, (s, v) ∈ U) :
    IntegrableOn (fun s => massInDensity S s v) (Ioc u v) := by
  let b : ℕ → ℝ := fun n => v - (v - u) * (1 / ((n : ℝ) + 1))
  have hbu (n : ℕ) : u ≤ b n := by
    dsimp [b]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hp : 1 ≤ ((n : ℝ) + 1) := by linarith
    have hone : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_iff₀ (by positivity)).2 (by linarith)
    nlinarith [mul_nonneg (sub_pos.mpr huv).le (sub_nonneg.mpr hone)]
  have hbv (n : ℕ) : b n < v := by
    dsimp [b]
    have hp : 0 < ((n : ℝ) + 1) := by positivity
    have hd : 0 < (v - u) * (1 / ((n : ℝ) + 1)) :=
      mul_pos (sub_pos.mpr huv) (one_div_pos.mpr hp)
    linarith
  have hb : Tendsto b atTop (𝓝 v) := by
    have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hconstv : Tendsto (fun _ : ℕ => v) atTop (𝓝 v) := tendsto_const_nhds
    have hconstd : Tendsto (fun _ : ℕ => v - u) atTop (𝓝 (v - u)) :=
      tendsto_const_nhds
    simpa only [b, mul_zero, sub_zero] using hconstv.sub (hconstd.mul hzero)
  have hprim (n : ℕ) : IntervalPrimitive
      (fun s => S.m s v) (fun s => massInDensity S s v) u (b n) := by
    change IntervalPrimitive (fun s => S.m s v)
      (fun s => (1 - 2 * S.m s v / S.r s v) * S.zeta s v ^ 2 /
        (2 * S.nu s v)) u (b n)
    exact h.mass_in v u (b n) (hbu n)
      (incoming_seg_subset_of_half_open_access (hbv n) haccess)
  have hInt (n : ℕ) : IntegrableOn
      (fun s => massInDensity S s v) (Ioc u (b n)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (hbu n)).1 (hprim n).1
  have hBound (n : ℕ) :
      (∫ s in Ioc u (b n), ‖massInDensity S s v‖) ≤ S.m u v := by
    have hnorm : (∫ s in Ioc u (b n), ‖massInDensity S s v‖) =
        -(∫ s in u..b n, massInDensity S s v) := by
      rw [intervalIntegral.integral_of_le (hbu n)]
      calc
        (∫ s in Ioc u (b n), ‖massInDensity S s v‖) =
            ∫ s in Ioc u (b n), -massInDensity S s v := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro s hs
          have hsv := haccess s ⟨hs.1.le, hs.2.trans_lt (hbv n)⟩
          simp only [Real.norm_eq_abs, abs_of_nonpos ((massInDensity_nonpos hc hnu hmu) hsv)]
        _ = _ := by rw [integral_neg]
    have hm := (mass_nonneg h hmu) (haccess (b n) ⟨hbu n, hbv n⟩)
    rw [hnorm, ← (hprim n).2]
    linarith
  exact integrableOn_Ioc_of_intervalIntegral_norm_bounded_right hInt hb
    (Filter.Eventually.of_forall hBound)

/-- The incoming mass at the initial point is the negative integral of its
nonpositive density all the way to the excluded diagonal endpoint. -/
theorem mass_eq_incoming_axis_integral_of_half_open_access
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (h : IsSolution U S)
    (hc : 0 < c)
    (hnu : ∀ p ∈ U, S.nu p.1 p.2 ≤ -c)
    (hR : ∃ K : ℝ, ∀ u v, (u, v) ∈ U → S.r u v ≤ K * (v - u))
    (hmu : ∀ p ∈ U, 0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1)
    {u v : ℝ} (huv : u < v)
    (haccess : ∀ s ∈ Ico u v, (s, v) ∈ U) :
    S.m u v = -(∫ s in u..v, massInDensity S s v) := by
  have hint : IntervalIntegrable (fun s => massInDensity S s v) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.le).2
      ((massInDensity_integrable_of_half_open_access h hc hnu hmu) huv haccess)
  let F : ℝ → ℝ := fun b => ∫ s in u..b, massInDensity S s v
  have hFAC : AbsolutelyContinuousOnInterval F u v :=
    hint.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hleft : Tendsto (fun b : ℝ => b) (𝓝[<] v) (𝓝[Icc u v] v) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left inf_le_left,
      mem_of_superset (Ioo_mem_nhdsLT huv)
        (fun b hb => ⟨hb.1.le, hb.2.le⟩)⟩
  have hF : Tendsto F (𝓝[<] v)
      (𝓝 (∫ s in u..v, massInDensity S s v)) := by
    have hcont : ContinuousOn F (Icc u v) := by
      simpa only [uIcc_of_le huv.le] using hFAC.continuousOn
    have hh := (hcont.continuousWithinAt
      (show v ∈ Icc u v from ⟨huv.le, le_rfl⟩)).tendsto.comp hleft
    simpa only [F, Function.comp_def] using hh
  have hEq : ∀ᶠ b in 𝓝[<] v,
      S.m b v - S.m u v = F b := by
    filter_upwards [Ioo_mem_nhdsLT huv] with b hb
    have hp := h.mass_in v u b hb.1.le
      (incoming_seg_subset_of_half_open_access hb.2 haccess)
    have heq := hp.2
    change S.m b v - S.m u v = F b at heq
    exact heq
  have hmass : Tendsto (fun b => S.m b v - S.m u v)
      (𝓝[<] v) (𝓝 (-S.m u v)) := by
    simpa using ((mass_tendsto_axis_in_of_half_open_access h hR hmu) huv haccess).sub_const
      (S.m u v)
  have heq : -S.m u v = ∫ s in u..v, massInDensity S s v :=
    tendsto_nhds_unique hmass (hF.congr' (hEq.mono fun _ he => he.symm))
  linarith only [heq]

/-- Incoming BV variation supplies a finite left trace of `ζ` when the
whole approaching half-open characteristic belongs to the domain. -/
theorem exists_zeta_axis_limit_in_of_half_open_access
    {U : Set (ℝ × ℝ)} {S : Fields}
    (hZetaBV : ∀ v, BoundedVariationOn (fun u => S.zeta u v) {u | (u, v) ∈ U})
    {u v : ℝ} (huv : u < v)
    (haccess : ∀ s ∈ Ico u v, (s, v) ∈ U) :
    ∃ L : ℝ, Tendsto (fun s => S.zeta s v) (𝓝[<] v) (𝓝 L) := by
  have hBV : BoundedVariationOn (fun s => S.zeta s v) {s | (s, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_of_eq (ENNReal.ofReal_toReal (hZetaBV v)).symm)
  obtain ⟨L, hL⟩ := hBV.exists_tendsto_left v
  refine ⟨L, ?_⟩
  have hcarrier : {s | (s, v) ∈ U} ∈ 𝓝[<] v :=
    mem_of_superset (Ioo_mem_nhdsLT huv)
      (fun s hs => haccess s ⟨hs.1.le, hs.2⟩)
  have hfilter : 𝓝[{s | (s, v) ∈ U} ∩ Iio v] v = 𝓝[<] v := by
    calc
      𝓝[{s | (s, v) ∈ U} ∩ Iio v] v =
          𝓝[<] v ⊓ 𝓟 {s | (s, v) ∈ U} := by
            simp only [nhdsWithin, ← Filter.inf_principal]
            ac_rfl
      _ = 𝓝[<] v := by simp [hcarrier]
  simpa only [hfilter] using hL

/-- The derivative of the scalar field is integrable up to an accessible
incoming diagonal endpoint. Its absolute integral is bounded by the global
incoming section variation. -/
theorem scalar_deriv_integrable_on_incoming_axis_slice
    {U : Set (ℝ × ℝ)} {S : Fields}
    (hACIn : ∀ v a b, a ≤ b → inSeg v a b ⊆ U →
      AbsolutelyContinuousOnInterval (fun u => S.phi u v) a b)
    (hPhiBVIn : ∀ v, BoundedVariationOn (fun u => S.phi u v) {u | (u, v) ∈ U})
    {u v : ℝ} (huv : u < v)
    (haccess : ∀ s ∈ Ico u v, (s, v) ∈ U) :
    IntegrableOn (deriv (fun s => S.phi s v)) (Ioc u v) := by
  let C : ℝ := (eVariationOn (fun s => S.phi s v) {s | (s, v) ∈ U}).toReal
  have hvarIn (x : ℝ) := le_of_eq (ENNReal.ofReal_toReal (hPhiBVIn x)).symm
  let B : ℝ := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have hvarB : eVariationOn (fun s => S.phi s v) {s | (s, v) ∈ U} ≤
      ENNReal.ofReal B :=
    (hvarIn v).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  let b : ℕ → ℝ := fun n => v - (v - u) * (1 / ((n : ℝ) + 1))
  have hbu (n : ℕ) : u ≤ b n := by
    dsimp [b]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hp : 1 ≤ ((n : ℝ) + 1) := by linarith
    have hone : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_iff₀ (by positivity)).2 (by linarith)
    nlinarith [mul_nonneg (sub_pos.mpr huv).le (sub_nonneg.mpr hone)]
  have hbv (n : ℕ) : b n < v := by
    dsimp [b]
    have hp : 0 < ((n : ℝ) + 1) := by positivity
    have hd : 0 < (v - u) * (1 / ((n : ℝ) + 1)) :=
      mul_pos (sub_pos.mpr huv) (one_div_pos.mpr hp)
    linarith
  have hb : Tendsto b atTop (𝓝 v) := by
    have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hconstv : Tendsto (fun _ : ℕ => v) atTop (𝓝 v) := tendsto_const_nhds
    have hconstd : Tendsto (fun _ : ℕ => v - u) atTop (𝓝 (v - u)) :=
      tendsto_const_nhds
    simpa only [b, mul_zero, sub_zero] using hconstv.sub (hconstd.mul hzero)
  have hInt (n : ℕ) : IntegrableOn
      (deriv (fun s => S.phi s v)) (Ioc u (b n)) := by
    have hseg := incoming_seg_subset_of_half_open_access (hbv n) haccess
    have hAC := hACIn v u (b n) (hbu n) hseg
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (hbu n)).1
      hAC.intervalIntegrable_deriv
  have hbound (n : ℕ) :
      ∫ s in Ioc u (b n), ‖deriv (fun t => S.phi t v) s‖ ≤ B := by
    have hsubset : Icc u (b n) ⊆ {s | (s, v) ∈ U} := by
      intro s hs
      exact haccess s ⟨hs.1, hs.2.trans_lt (hbv n)⟩
    have hBV : BoundedVariationOn (fun s => S.phi s v) (Icc u (b n)) :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        ((eVariationOn.mono (fun s => S.phi s v) hsubset).trans hvarB)
    have hbound' := hBV.integral_abs_deriv_le_eVariationOn (hbu n)
    have hvar' : (eVariationOn (fun s => S.phi s v) (Icc u (b n))).toReal ≤ B :=
      ENNReal.toReal_le_of_le_ofReal hB
        ((eVariationOn.mono (fun s => S.phi s v) hsubset).trans hvarB)
    rw [intervalIntegral.integral_of_le (hbu n)] at hbound'
    simpa only [Real.norm_eq_abs] using hbound'.trans hvar'
  exact integrableOn_Ioc_of_intervalIntegral_norm_bounded_right hInt hb
    (Filter.Eventually.of_forall hbound)

/-- The incoming BV amplitude tends to zero at an accessible diagonal.
A nonzero trace would force a nonintegrable reciprocal-distance lower bound
for the scalar derivative. -/
theorem zeta_tendsto_zero_axis_in_of_half_open_access
    {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsSolution U S)
    (hR : ∃ K : ℝ, ∀ u v, (u, v) ∈ U → S.r u v ≤ K * (v - u))
    (hACIn : ∀ v a b, a ≤ b → inSeg v a b ⊆ U →
      AbsolutelyContinuousOnInterval (fun u => S.phi u v) a b)
    (hPhiBVIn : ∀ v, BoundedVariationOn (fun u => S.phi u v) {u | (u, v) ∈ U})
    (hZetaBV : ∀ v, BoundedVariationOn (fun u => S.zeta u v) {u | (u, v) ∈ U})
    {u v : ℝ} (huv : u < v)
    (haccess : ∀ s ∈ Ico u v, (s, v) ∈ U) :
    Tendsto (fun s => S.zeta s v) (𝓝[<] v) (𝓝 (0 : ℝ)) := by
  obtain ⟨L, hL⟩ := (exists_zeta_axis_limit_in_of_half_open_access hZetaBV) huv haccess
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
  have hev : {s : ℝ | k < |S.zeta s v|} ∈ 𝓝[<] v :=
    hL.abs.eventually (eventually_gt_nhds hcL)
  obtain ⟨d, hdv, hd⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hev
  let a : ℝ := (max d u + v) / 2
  have huamax : u ≤ max d u := le_max_right _ _
  have hdamax : d ≤ max d u := le_max_left _ _
  have hmaxv : max d u < v := max_lt hdv huv
  have hua : u < a := by dsimp [a]; linarith
  have hda : d < a := by dsimp [a]; linarith
  have hav : a < v := by dsimp [a]; linarith
  obtain ⟨K, hrad⟩ := hR
  have haU : (a, v) ∈ U := haccess a ⟨hua.le, hav⟩
  have hKpos : 0 < K := by
    have hr := hrad a v haU
    have hrpos := h.radius_pos (a, v) haU
    nlinarith [sub_pos.mpr hav]
  have hderiv : IntegrableOn (deriv (fun s => S.phi s v)) (Ioc a v) :=
    ((scalar_deriv_integrable_on_incoming_axis_slice hACIn hPhiBVIn) huv haccess).mono_set
      (Ioc_subset_Ioc_left hua.le)
  have hscaled : IntegrableOn
      (fun s => (K / k) * deriv (fun t => S.phi t v) s) (Ioc a v) :=
    hderiv.const_mul (K / k)
  have hinv : IntegrableOn (fun s => (v - s)⁻¹) (Ioc a v) := by
    apply Integrable.mono hscaled
    · exact ((measurable_const.sub measurable_id).inv).aestronglyMeasurable
    · rw [← restrict_Ioo_eq_restrict_Ioc, ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [(scalar_ae_deriv_in_on_half_open_access h hACIn) huv haccess]
        with s hφ hs
      have hsvMem : s ∈ Ico u v := ⟨hua.le.trans hs.1.le, hs.2⟩
      have hsv := haccess s hsvMem
      have hrpos := h.radius_pos (s, v) hsv
      have hrle := hrad s v hsv
      have hζ : k < |S.zeta s v| := hd ⟨hda.trans hs.1, hs.2⟩
      have hx : 0 < v - s := sub_pos.mpr hs.2
      have hcross₁ : k * S.r s v ≤ k * (K * (v - s)) :=
        mul_le_mul_of_nonneg_left hrle hk.le
      have hcross₂ : (K * (v - s)) * k ≤
          (K * (v - s)) * |S.zeta s v| :=
        mul_le_mul_of_nonneg_left hζ.le
          (mul_nonneg hKpos.le hx.le)
      rw [hφ hsvMem]
      simp only [Real.norm_eq_abs, abs_inv, abs_of_pos hx,
        abs_mul, abs_of_pos (div_pos hKpos hk), abs_div, abs_of_pos hrpos]
      rw [inv_eq_one_div]
      have hrewrite : K / k * (|S.zeta s v| / S.r s v) =
          K * |S.zeta s v| / (k * S.r s v) := by ring
      rw [hrewrite]
      apply (div_le_div_iff₀ hx (mul_pos hk hrpos)).2
      nlinarith [hcross₁, hcross₂]
  have hi : IntervalIntegrable (fun s => (v - s)⁻¹) volume a v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hav.le).2 hinv
  have hi' : IntervalIntegrable (fun s => (s - v)⁻¹) volume a v := by
    have hfun : (fun s => (s - v)⁻¹) = (fun s => -((v - s)⁻¹)) := by
      funext s
      rw [show s - v = -(v - s) by ring, inv_neg]
    rw [hfun]
    have hfun2 : (fun s => -((v - s)⁻¹)) = -(fun s => (v - s)⁻¹) := by
      funext s
      rfl
    rw [hfun2]
    exact hi.neg
  rcases intervalIntegrable_sub_inv_iff.mp hi' with heq | hnot
  · exact (ne_of_lt hav heq).elim
  · rw [uIcc_of_le hav.le] at hnot
    exact (hnot ⟨hav.le, le_rfl⟩).elim

/-- The absolute incoming mass density is bounded by the squared incoming
amplitude divided by the uniform expansion lower bound. -/
theorem neg_massInDensity_le_zeta_sq
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (hc : 0 < c)
    (hnu : ∀ p ∈ U, S.nu p.1 p.2 ≤ -c)
    (hmu : ∀ p ∈ U, 0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1)
    {s v : ℝ}
    (hsv : (s, v) ∈ U) :
    -massInDensity S s v ≤ S.zeta s v ^ 2 / (2 * c) := by
  have hratio := hmu _ hsv
  have hgap0 : 0 ≤ 1 - 2 * S.m s v / S.r s v := by linarith
  have hgap1 : 1 - 2 * S.m s v / S.r s v ≤ 1 := by linarith
  have hnu : S.nu s v ≤ -c := hnu _ hsv
  have hden : 0 < -2 * S.nu s v := by linarith
  have hnum :
      (1 - 2 * S.m s v / S.r s v) * S.zeta s v ^ 2 * c ≤
        S.zeta s v ^ 2 * (-S.nu s v) := by
    have h₁ : (1 - 2 * S.m s v / S.r s v) * S.zeta s v ^ 2 * c ≤
        S.zeta s v ^ 2 * c := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hgap1)
        (mul_nonneg (sq_nonneg (S.zeta s v)) hc.le)]
    have h₂ : S.zeta s v ^ 2 * c ≤ S.zeta s v ^ 2 * (-S.nu s v) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    exact h₁.trans h₂
  have hform : -massInDensity S s v =
      ((1 - 2 * S.m s v / S.r s v) * S.zeta s v ^ 2) /
        (-2 * S.nu s v) := by
    unfold massInDensity
    ring
  rw [hform]
  apply (div_le_div_iff₀ hden (by positivity : 0 < 2 * c)).2
  nlinarith only [hnum]

/-- A small squared incoming amplitude on a complete terminal ray bounds the
mass-to-radius ratio there. -/
theorem mass_ratio_le_of_zeta_sq_le_on_incoming_ray
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (h : IsSolution U S)
    (hc : 0 < c)
    (hlam : ∀ p ∈ U, c ≤ S.lam p.1 p.2)
    (hnu : ∀ p ∈ U, S.nu p.1 p.2 ≤ -c)
    (hR : ∃ K : ℝ, ∀ u v, (u, v) ∈ U → S.r u v ≤ K * (v - u))
    (hmu : ∀ p ∈ U, 0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1)
    {w v η : ℝ}
    (hwv : w < v) (hη : 0 ≤ η)
    (haccess : ∀ s ∈ Ico w v, (s, v) ∈ U)
    (hsmall : ∀ s ∈ Ioo w v, S.zeta s v ^ 2 ≤ η * c ^ 2) :
    2 * S.m w v / S.r w v ≤ η := by
  have hMass := (mass_eq_incoming_axis_integral_of_half_open_access h hc hnu hR hmu) hwv haccess
  have hDensityInt : IntervalIntegrable
      (fun s => -massInDensity S s v) volume w v :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hwv.le).2
      ((massInDensity_integrable_of_half_open_access h hc hnu hmu) hwv haccess)).neg
  have hConstInt : IntervalIntegrable (fun _ : ℝ => η * c / 2) volume w v :=
    intervalIntegrable_const
  have hae : ∀ᵐ s ∂volume.restrict (Icc w v),
      -massInDensity S s v ≤ η * c / 2 := by
    rw [← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall (fun s hs => by
      have hsv := haccess s ⟨hs.1.le, hs.2⟩
      have hden := (neg_massInDensity_le_zeta_sq hc hnu hmu) hsv
      have hsq := hsmall s hs
      have hquot : S.zeta s v ^ 2 / (2 * c) ≤ η * c / 2 := by
        apply (div_le_div_iff₀ (by positivity : 0 < 2 * c)
          (by norm_num : (0 : ℝ) < 2)).2
        nlinarith only [hsq]
      exact hden.trans hquot)
  have hle := intervalIntegral.integral_mono_ae_restrict hwv.le hDensityInt
    hConstInt hae
  have hmassInt : S.m w v = ∫ s in w..v, -massInDensity S s v := by
    rw [intervalIntegral.integral_neg]
    exact hMass
  rw [← hmassInt, intervalIntegral.integral_const] at hle
  have hwvU := haccess w ⟨le_rfl, hwv⟩
  have hrpos := h.radius_pos (w, v) hwvU
  have hrLower := (radius_lower h hlam) hwvU
  have hmul := mul_le_mul_of_nonneg_left hrLower hη
  apply (div_le_iff₀ hrpos).2
  simp only [smul_eq_mul] at hle
  nlinarith only [hle, hmul]

/-- The mass ratio tends to zero on a complete incoming half-open ray.
The incoming mass identity and zero `ζ` trace give the requisite
mass-to-radius estimate. -/
theorem mass_ratio_tendsto_zero_axis_in_of_half_open_access
    {U : Set (ℝ × ℝ)} {S : Fields} {c : ℝ}
    (h : IsSolution U S)
    (hc : 0 < c)
    (hlam : ∀ p ∈ U, c ≤ S.lam p.1 p.2)
    (hnu : ∀ p ∈ U, S.nu p.1 p.2 ≤ -c)
    (hR : ∃ K : ℝ, ∀ u v, (u, v) ∈ U → S.r u v ≤ K * (v - u))
    (hmu : ∀ p ∈ U, 0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1)
    (hACIn : ∀ v a b, a ≤ b → inSeg v a b ⊆ U →
      AbsolutelyContinuousOnInterval (fun u => S.phi u v) a b)
    (hPhiBVIn : ∀ v, BoundedVariationOn (fun u => S.phi u v) {u | (u, v) ∈ U})
    (hZetaBV : ∀ v, BoundedVariationOn (fun u => S.zeta u v) {u | (u, v) ∈ U})
    {u v : ℝ} (huv : u < v)
    (haccess : ∀ s ∈ Ico u v, (s, v) ∈ U) :
    Tendsto (fun w => 2 * S.m w v / S.r w v)
      (𝓝[<] v) (𝓝 (0 : ℝ)) := by
  have hζ := (zeta_tendsto_zero_axis_in_of_half_open_access h hR hACIn hPhiBVIn hZetaBV) huv haccess
  have hζsq : Tendsto (fun s => S.zeta s v ^ 2)
      (𝓝[<] v) (𝓝 (0 : ℝ)) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0)] using hζ.pow 2
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have hcη : 0 < η * c ^ 2 := mul_pos hη (sq_pos_of_pos hc)
  have hev : {s : ℝ | S.zeta s v ^ 2 < η * c ^ 2} ∈ 𝓝[<] v :=
    hζsq.eventually (eventually_lt_nhds hcη)
  obtain ⟨d, hdv, hd⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hev
  have hmaxv : max u d < v := max_lt huv hdv
  filter_upwards [Ioo_mem_nhdsLT hmaxv] with w hw
  have huw : u ≤ w := (le_max_left _ _).trans hw.1.le
  have hdw : d ≤ w := (le_max_right _ _).trans hw.1.le
  have hwU := haccess w ⟨huw, hw.2⟩
  have hμnonneg := (hmu _ hwU).1
  have hμle : 2 * S.m w v / S.r w v ≤ η :=
    (mass_ratio_le_of_zeta_sq_le_on_incoming_ray h hc hlam hnu hR hmu) hw.2 hη.le
      (fun s hs => haccess s ⟨huw.trans hs.1, hs.2⟩)
      (fun s hs => (hd ⟨hdw.trans_lt hs.1, hs.2⟩).le)
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg hμnonneg]
  dsimp [η] at hμle
  linarith

end ChristodoulouBV.SourceInputsWeak

end
