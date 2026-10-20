module

public import ChristodoulouBV.BVSolution.AxisIntegrals
public import ChristodoulouBV.BVSolution.IncomingLogCoefficient
public import ChristodoulouBV.BVSolution.PrimitiveCalculus

/-!
# Conditional coefficient closure on comparison triangles

The preliminary constants are chosen from the fixed pair before local
variation thresholds and compact tops. Incoming integrals retain the sign
needed by the Volterra estimates.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.IsBVSolution

/-- The source mass ratio `μ=2m/r`, used only as a transparent abbreviation. -/
@[expose] noncomputable def mu (S : Fields) (u v : ℝ) : ℝ :=
  2 * S.m u v / S.r u v

/-- The incoming coefficient of the radius transport equation is nonpositive
at every BV development point. -/
theorem incoming_radius_coefficient_nonpos
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    mu S u v * S.nu u v /
      ((1 - mu S u v) * S.r u v) ≤ 0 := by
  have hmu := h.mass_ratio_bounds huv
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  have hnu : S.nu u v < 0 :=
    (h.nu_le_neg_lower hc hlam huv).trans_lt (neg_lt_zero.mpr hc)
  have hr := h.solution.radius_pos (u, v) huv
  have hgap : 0 < 1 - mu S u v := by
    dsimp [mu]
    linarith [hmu.2]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by simpa only [mu] using hmu.1) hnu.le)
    (mul_pos hgap hr).le

/-- With fixed positive lower expansion and upper scalar-amplitude bounds,
the incoming quotient needed in (3.1b) has a fixed upper bound. -/
private theorem zeta_div_nu_le_of_field_bounds
    {S : Fields} {c C₀ u v : ℝ} (hc : 0 < c) (hC : 0 ≤ C₀)
    (hnu : c ≤ |S.nu u v|) (hzeta : |S.zeta u v| ≤ C₀) :
    |S.zeta u v / S.nu u v| ≤ C₀ / c := by
  have hnuPos : 0 < |S.nu u v| := hc.trans_le hnu
  rw [abs_div]
  apply (div_le_div_iff₀ hnuPos hc).2
  calc
    |S.zeta u v| * c ≤ C₀ * c :=
      mul_le_mul_of_nonneg_right hzeta hc.le
    _ ≤ C₀ * |S.nu u v| :=
      mul_le_mul_of_nonneg_left hnu hC

/-- The usable incoming estimate has a negative integral and a constant
chosen before the local scalar variation threshold. It is uniform for both
members of the fixed pair and for every full comparison triangle. -/
theorem eq3_12_usable
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {w : ℝ} (href : (0, w) ∈ U₁ ∩ U₂)
    (hdata : S₁.phi 0 w = S₂.phi 0 w) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ε : ℝ, 0 ≤ ε →
        ∀ a b u v, Uniqueness.triangle a b ⊆ U₁ ∩ U₂ →
          (u, v) ∈ Uniqueness.triangle a b →
          ∀ S : Fields, (S = S₁ ∨ S = S₂) →
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε →
            -(∫ s in u..v,
              mu S s v * S.nu s v /
                ((1 - mu S s v) * S.r s v)) ≤ C * ε := by
  obtain ⟨c, C₀, hc, hC₀, hfield⟩ :=
    h₁.preloc_coefficient_bounds h₂ href hdata
  let C := C₀ / c
  have hC : 0 ≤ C := div_nonneg hC₀ hc.le
  refine ⟨C, hC, ?_⟩
  intro ε hε a b u v hT huv S hS hY
  have hquery : ∀ s ∈ Ico u v, |S.zeta s v / S.nu s v| ≤ C := by
    intro s hs
    have hsv : (s, v) ∈ Uniqueness.triangle a b :=
      (Uniqueness.mem_triangle).2
        ⟨huv.1.trans hs.1, hs.2, huv.2.2⟩
    have hb := hfield a b s v hT hsv S hS
    exact zeta_div_nu_le_of_field_bounds hc hC₀ hb.2.2.1 hb.2.2.2.2.2.2
  have haccess : ∀ s ∈ Ico u v,
      (s, v) ∈ U₁ ∩ U₂ := by
    intro s hs
    exact hT ((Uniqueness.mem_triangle).2
      ⟨huv.1.trans hs.1, hs.2, huv.2.2⟩)
  rcases hS with rfl | rfl
  · have hineq := h₁.eq3_1b huv.2.1
      (fun s hs => (haccess s hs).1) hquery
    simpa only [mu] using
      hineq.trans (mul_le_mul_of_nonneg_left hY hC)
  · have hineq := h₂.eq3_1b huv.2.1
      (fun s hs => (haccess s hs).2) hquery
    simpa only [mu] using
      hineq.trans (mul_le_mul_of_nonneg_left hY hC)

/-- On a compact accessible incoming segment, `λ/(1−μ)` is absolutely
continuous and obeys the a.e. form of (1.21a). -/
theorem quotient_transport_in
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {v a b : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hseg : inSeg v a b ⊆ U) :
    AbsolutelyContinuousOnInterval
      (fun s => S.lam s v / (1 - mu S s v)) a b ∧
      ∀ᵐ s ∂volume, s ∈ Icc a b →
        deriv (fun t => S.lam t v / (1 - mu S t v)) s =
          S.zeta s v ^ 2 / (S.r s v * S.nu s v) *
            (S.lam s v / (1 - mu S s v)) := by
  have hlam := h.solution.lam_in_ac_ae hab hseg
  have hratio := h.mass_div_radius_ac_in hab hbv hseg
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  have hgap : AbsolutelyContinuousOnInterval
      (fun s => 1 - mu S s v) a b := by
    convert hconst.sub (hratio.const_mul 2) using 1
    funext s
    simp only [Pi.sub_apply, mu]
    ring
  obtain ⟨δ, hδ, hlow⟩ := h.exists_mass_gap_ratio_lower_in hab hbv hseg
  have hbound : ∀ s ∈ uIcc a b, δ ≤ |1 - mu S s v| := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    have hδs := hlow s hs
    have hpos : 0 < 1 - mu S s v := by
      dsimp [mu]
      linarith
    rw [abs_of_pos hpos]
    simpa only [mu] using hδs
  have hquot := hlam.1.div_and_ae_deriv hgap hδ hbound
  have hmass := h.mass_ratio_ae_deriv_in hab hbv hseg
  refine ⟨hquot.1, ?_⟩
  filter_upwards [hquot.2, hlam.2, hmass] with s hq hl hm hs
  have hsU : (s, v) ∈ U := hseg (by
    change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨hs, rfl⟩)
  have hr : S.r s v ≠ 0 := ne_of_gt (h.solution.radius_pos (s, v) hsU)
  obtain ⟨c, hc, hlamLower⟩ := h.lam_bounded_below
  have hn : S.nu s v ≠ 0 := ne_of_lt
    ((h.nu_le_neg_lower hc hlamLower hsU).trans_lt (neg_lt_zero.mpr hc))
  have hg : 1 - mu S s v ≠ 0 := by
    have hmu := (h.mass_ratio_bounds hsU).2
    dsimp [mu]
    linarith
  have hg' : S.r s v - 2 * S.m s v ≠ 0 := by
    intro he
    apply hg
    have hratio : 2 * S.m s v / S.r s v = 1 := by
      apply (div_eq_iff hr).2
      linarith
    dsimp [mu]
    linarith
  have hDer : deriv (fun t => 1 - mu S t v) s =
      -2 * deriv (fun t => S.m t v / S.r t v) s := by
    have hfun : (fun t => 1 - mu S t v) =
        (fun t => 1 - 2 * (S.m t v / S.r t v)) := by
      funext t
      dsimp [mu]
      ring
    rw [hfun, deriv_const_sub, deriv_const_mul_field]
    ring
  rw [uIcc_of_le hab] at hq
  rw [hq hs, hl hs, hDer, hm hs]
  unfold radiusCoeff massInDensity mu
  field_simp [hr, hn, hg']
  ring

/-- On a compact outgoing segment, `ν/(1−μ)` is absolutely continuous and
obeys the a.e. form of (1.21b). -/
theorem quotient_transport_out
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v a b : ℝ} (huv : (u, v) ∈ U) (hua : u < a)
    (hab : a ≤ b) (hbv : b ≤ v) :
    AbsolutelyContinuousOnInterval
      (fun t => S.nu u t / (1 - mu S u t)) a b ∧
      ∀ᵐ t ∂volume, t ∈ Icc a b →
        deriv (fun s => S.nu u s / (1 - mu S u s)) t =
          S.theta u t ^ 2 / (S.r u t * S.lam u t) *
            (S.nu u t / (1 - mu S u t)) := by
  have hseg := h.solution.development.out_seg_subset huv hua hab hbv
  have hnu := h.solution.nu_out_ac_ae hab hseg
  have hratio := h.mass_div_radius_ac_out huv hua hab hbv
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  have hgap : AbsolutelyContinuousOnInterval
      (fun t => 1 - mu S u t) a b := by
    convert hconst.sub (hratio.const_mul 2) using 1
    funext t
    simp only [Pi.sub_apply, mu]
    ring
  obtain ⟨δ, hδ, hlow⟩ := h.exists_mass_gap_ratio_lower_out huv hua hab hbv
  have hbound : ∀ t ∈ uIcc a b, δ ≤ |1 - mu S u t| := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have hδt := hlow t ht
    have hpos : 0 < 1 - mu S u t := by
      dsimp [mu]
      linarith
    rw [abs_of_pos hpos]
    simpa only [mu] using hδt
  have hquot := hnu.1.div_and_ae_deriv hgap hδ hbound
  have hmass := h.mass_ratio_ae_deriv_out huv hua hab hbv
  refine ⟨hquot.1, ?_⟩
  filter_upwards [hquot.2, hnu.2, hmass] with t hq hn hm ht
  have htU : (u, t) ∈ U := h.solution.development.outgoing_mem huv
    (hua.trans_le ht.1) (ht.2.trans hbv)
  have hr : S.r u t ≠ 0 := ne_of_gt (h.solution.radius_pos (u, t) htU)
  have hl : S.lam u t ≠ 0 := ne_of_gt (h.solution.lam_pos (u, t) htU)
  have hg : 1 - mu S u t ≠ 0 := by
    have hmu := (h.mass_ratio_bounds htU).2
    dsimp [mu]
    linarith
  have hg' : S.r u t - 2 * S.m u t ≠ 0 := by
    intro he
    apply hg
    have hratio : 2 * S.m u t / S.r u t = 1 := by
      apply (div_eq_iff hr).2
      linarith
    dsimp [mu]
    linarith
  have hDer : deriv (fun s => 1 - mu S u s) t =
      -2 * deriv (fun s => S.m u s / S.r u s) t := by
    have hfun : (fun s => 1 - mu S u s) =
        (fun s => 1 - 2 * (S.m u s / S.r u s)) := by
      funext s
      dsimp [mu]
      ring
    rw [hfun, deriv_const_sub, deriv_const_mul_field]
    ring
  rw [uIcc_of_le hab] at hq
  rw [hq ht, hn ht, hDer, hm ht]
  unfold radiusCoeff massV mu
  field_simp [hr, hl, hg']
  ring

/-- The positive incoming quotient has an absolutely continuous logarithm;
its a.e. derivative is the logarithmic form of (1.21a). -/
theorem log_transport_in
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {v a b : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hseg : inSeg v a b ⊆ U) :
    AbsolutelyContinuousOnInterval
      (fun s => Real.log (S.lam s v / (1 - mu S s v))) a b ∧
      ∀ᵐ s ∂volume, s ∈ Icc a b →
        deriv (fun t => Real.log (S.lam t v / (1 - mu S t v))) s =
          S.zeta s v ^ 2 / (S.r s v * S.nu s v) := by
  have hquot := h.quotient_transport_in hab hbv hseg
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  have hbound : ∀ s ∈ uIcc a b,
      c ≤ S.lam s v / (1 - mu S s v) := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    have hsU : (s, v) ∈ U := hseg (by
      change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
      exact ⟨hs, rfl⟩)
    have hmu := h.mass_ratio_bounds hsU
    have hgapPos : 0 < 1 - mu S s v := by
      dsimp [mu]
      linarith [hmu.2]
    have hgapLe : 1 - mu S s v ≤ 1 := by
      dsimp [mu]
      linarith [hmu.1]
    apply (le_div_iff₀ hgapPos).2
    calc
      c * (1 - mu S s v) ≤ c * 1 :=
        mul_le_mul_of_nonneg_left hgapLe hc.le
      _ = c := mul_one c
      _ ≤ S.lam s v := hlam (s, v) hsU
  have hlog := hquot.1.log_and_ae_deriv hc hbound
  refine ⟨hlog.1, ?_⟩
  filter_upwards [hlog.2, hquot.2] with s hlog' hq hs
  have hsU : (s, v) ∈ U := hseg (by
    change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨hs, rfl⟩)
  have hl : S.lam s v ≠ 0 := ne_of_gt (hc.trans_le (hlam (s, v) hsU))
  have hg : 1 - mu S s v ≠ 0 := by
    have hmu := (h.mass_ratio_bounds hsU).2
    dsimp [mu]
    linarith
  rw [uIcc_of_le hab] at hlog'
  rw [hlog' hs, hq hs]
  field_simp [hl, hg]

/-- The negative outgoing quotient has an absolutely continuous positive
logarithm; its a.e. derivative is the logarithmic form of (1.21b). -/
theorem log_transport_out
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v a b : ℝ} (huv : (u, v) ∈ U) (hua : u < a)
    (hab : a ≤ b) (hbv : b ≤ v) :
    AbsolutelyContinuousOnInterval
      (fun t => Real.log (-(S.nu u t / (1 - mu S u t)))) a b ∧
      ∀ᵐ t ∂volume, t ∈ Icc a b →
        deriv (fun s => Real.log (-(S.nu u s / (1 - mu S u s)))) t =
          S.theta u t ^ 2 / (S.r u t * S.lam u t) := by
  have hquot := h.quotient_transport_out huv hua hab hbv
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  have hnegAC : AbsolutelyContinuousOnInterval
      (fun t => -(S.nu u t / (1 - mu S u t))) a b :=
    hquot.1.neg
  have hbound : ∀ t ∈ uIcc a b,
      c ≤ -(S.nu u t / (1 - mu S u t)) := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have htU : (u, t) ∈ U := h.solution.development.outgoing_mem huv
      (hua.trans_le ht.1) (ht.2.trans hbv)
    have hmu := h.mass_ratio_bounds htU
    have hgapPos : 0 < 1 - mu S u t := by
      dsimp [mu]
      linarith [hmu.2]
    have hgapLe : 1 - mu S u t ≤ 1 := by
      dsimp [mu]
      linarith [hmu.1]
    have hnuLo : c ≤ -S.nu u t := by
      linarith [h.nu_le_neg_lower hc hlam htU]
    have hdiv : c ≤ (-S.nu u t) / (1 - mu S u t) := by
      apply (le_div_iff₀ hgapPos).2
      calc
        c * (1 - mu S u t) ≤ c * 1 :=
          mul_le_mul_of_nonneg_left hgapLe hc.le
        _ = c := mul_one c
        _ ≤ -S.nu u t := hnuLo
    simpa only [neg_div] using hdiv
  have hlog := hnegAC.log_and_ae_deriv hc hbound
  refine ⟨hlog.1, ?_⟩
  filter_upwards [hlog.2, hquot.2] with t hlog' hq ht
  have htU : (u, t) ∈ U := h.solution.development.outgoing_mem huv
    (hua.trans_le ht.1) (ht.2.trans hbv)
  have hn : S.nu u t ≠ 0 := ne_of_lt
    ((h.nu_le_neg_lower hc hlam htU).trans_lt (neg_lt_zero.mpr hc))
  have hg : 1 - mu S u t ≠ 0 := by
    have hmu := (h.mass_ratio_bounds htU).2
    dsimp [mu]
    linarith
  have hDer : deriv (fun s => -(S.nu u s / (1 - mu S u s))) t =
      -deriv (fun s => S.nu u s / (1 - mu S u s)) t := by
    change deriv (-(fun s => S.nu u s / (1 - mu S u s))) t =
      -deriv (fun s => S.nu u s / (1 - mu S u s)) t
    exact deriv.neg
  rw [uIcc_of_le hab] at hlog'
  rw [hlog' ht, hDer, hq ht]
  field_simp [hn, hg]

/-- Preliminary outgoing scalar variation bounds the mass gap uniformly,
using (3.1a) with its logarithmic boundary term. -/
theorem gap_ge_half_of_small_outgoing_variation
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v M ε₀ : ℝ} (huv : (u, v) ∈ U) (hM : 0 ≤ M)
    (hquot : ∀ t ∈ Ioc u v, |S.theta u t / S.lam u t| ≤ M)
    (hX : (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀)
    (hsmall : M * ε₀ ≤ 1 / 2) :
    1 / 2 ≤ 1 - mu S u v := by
  have huvlt := (h.solution.development.wedge huv).2
  have hvarFinite : eVariationOn (S.phi u) (Ioc u v) ≠ ⊤ := by
    have hsubset : Ioc u v ⊆ {t | (u, t) ∈ U} := by
      intro t ht
      exact h.solution.development.outgoing_mem huv ht.1 ht.2
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((eVariationOn.mono (S.phi u) hsubset).trans
        (h.item3_variation.choose_spec.1 u))
  have hlogAxis : Tendsto
      (fun a => Real.log (1 - mu S u a))
      (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    have hgap : Tendsto (fun a => 1 - mu S u a)
        (𝓝[>] u) (𝓝 (1 : ℝ)) := by
      simpa only [mu, sub_zero] using
        (tendsto_const_nhds.sub (h.mass_ratio_tendsto_zero_axis_out huv))
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hgap
  have hbound : ∀ᶠ a in 𝓝[>] u,
      Real.log (1 - mu S u a) - M * ε₀ ≤
        Real.log (1 - mu S u v) := by
    filter_upwards [Ioo_mem_nhdsGT huvlt] with a ha
    have hcomp := h.eq3_1a_compact huv ha.1 ha.2.le le_rfl
      (fun t ht => hquot t ⟨ha.1.trans_le ht.1.le, ht.2⟩)
    have hvar : (eVariationOn (S.phi u) (Ioc a v)).toReal ≤ ε₀ :=
      (ENNReal.toReal_mono hvarFinite
        (eVariationOn.mono (S.phi u) (by
          intro t ht
          exact ⟨ha.1.trans_le ht.1.le, ht.2⟩))).trans hX
    have hmul := mul_le_mul_of_nonneg_left hvar hM
    have hcoeff : 0 ≤ ∫ t in a..v, nuCoeff S u t := by
      apply intervalIntegral.integral_nonneg ha.2.le
      intro t ht
      exact nu_coeff_nonneg h.solution.development h
        (h.solution.development.outgoing_mem huv
          (ha.1.trans_le ht.1) ht.2)
    have hgapA : 1 - mu S u a = 1 - 2 * S.m u a / S.r u a := rfl
    have hgapV : 1 - mu S u v = 1 - 2 * S.m u v / S.r u v := rfl
    rw [← hgapA, ← hgapV] at hcomp
    linarith
  have hlim : Tendsto (fun a => Real.log (1 - mu S u a) - M * ε₀)
      (𝓝[>] u) (𝓝 (-M * ε₀)) := by
    simpa using hlogAxis.sub_const (M * ε₀)
  have hlogBound : -M * ε₀ ≤ Real.log (1 - mu S u v) :=
    le_of_tendsto hlim hbound
  have hgapPos : 0 < 1 - mu S u v := by
    have hmu := (h.mass_ratio_bounds huv).2
    dsimp [mu]
    linarith
  have hexp : Real.exp (-M * ε₀) ≤ 1 - mu S u v := by
    rw [← Real.exp_log hgapPos]
    exact Real.exp_le_exp.mpr hlogBound
  have hlinear : 1 - M * ε₀ ≤ Real.exp (-M * ε₀) := by
    linarith [Real.add_one_le_exp (-M * ε₀)]
  linarith

/-- Algebraic closure of the field ratios after the preliminary mass-gap
bound. The hypotheses are supplied by the pairwise baseline theorem in the
source-facing coefficient theorem below. -/
theorem field_ratio_bounds
    {S : Fields} {u v c C₀ : ℝ} (hc : 0 < c) (hC₀ : 0 ≤ C₀)
    (hlamLo : c ≤ S.lam u v) (hlamHi : S.lam u v ≤ C₀)
    (hnuLo : c ≤ |S.nu u v|) (hnuHi : |S.nu u v| ≤ C₀)
    (hphi : |S.phi u v| ≤ C₀) (htheta : |S.theta u v| ≤ C₀)
    (hzeta : |S.zeta u v| ≤ C₀)
    (hgap : 1 / 2 ≤ 1 - mu S u v) :
    let B := 2 * (C₀ + C₀ / c + 1)
    |S.theta u v / S.lam u v| ≤ B ∧
    |S.zeta u v / S.nu u v| ≤ B ∧
    |S.alpha u v / S.lam u v| ≤ B ∧
    |S.beta u v / S.nu u v| ≤ B ∧
    |S.lam u v / (1 - mu S u v)| ≤ B ∧
    |S.nu u v / (1 - mu S u v)| ≤ B ∧
    (1 - mu S u v)⁻¹ ≤ B := by
  dsimp
  have hlamPos : 0 < S.lam u v := hc.trans_le hlamLo
  have hnuPos : 0 < |S.nu u v| := hc.trans_le hnuLo
  have hgapPos : 0 < 1 - mu S u v := by linarith
  have hM : 0 ≤ C₀ / c := div_nonneg hC₀ hc.le
  have hθ : |S.theta u v / S.lam u v| ≤ C₀ / c := by
    rw [abs_div, abs_of_pos hlamPos]
    apply (div_le_div_iff₀ hlamPos hc).2
    calc
      |S.theta u v| * c ≤ C₀ * c :=
        mul_le_mul_of_nonneg_right htheta hc.le
      _ ≤ C₀ * S.lam u v :=
        mul_le_mul_of_nonneg_left hlamLo hC₀
  have hζ : |S.zeta u v / S.nu u v| ≤ C₀ / c :=
    zeta_div_nu_le_of_field_bounds hc hC₀ hnuLo hzeta
  have hαid : S.alpha u v / S.lam u v =
      S.theta u v / S.lam u v + S.phi u v := by
    dsimp [Fields.theta]
    field_simp [ne_of_gt hlamPos]
    ring
  have hβid : S.beta u v / S.nu u v =
      S.zeta u v / S.nu u v + S.phi u v := by
    dsimp [Fields.zeta]
    have hnuNe : S.nu u v ≠ 0 := by
      intro hn
      simp only [hn, abs_zero] at hnuPos
      exact (lt_irrefl _ hnuPos)
    field_simp [hnuNe]
    ring
  have hα : |S.alpha u v / S.lam u v| ≤ C₀ / c + C₀ := by
    rw [hαid]
    exact (abs_add_le _ _).trans (add_le_add hθ hphi)
  have hβ : |S.beta u v / S.nu u v| ≤ C₀ / c + C₀ := by
    rw [hβid]
    exact (abs_add_le _ _).trans (add_le_add hζ hphi)
  have hlamGap : |S.lam u v / (1 - mu S u v)| ≤ 2 * C₀ := by
    rw [abs_div, abs_of_pos hlamPos, abs_of_pos hgapPos]
    apply (div_le_iff₀ hgapPos).2
    nlinarith [mul_nonneg hC₀ (sub_nonneg.mpr hgap)]
  have hnuGap : |S.nu u v / (1 - mu S u v)| ≤ 2 * C₀ := by
    rw [abs_div, abs_of_pos hgapPos]
    apply (div_le_iff₀ hgapPos).2
    nlinarith [mul_nonneg hC₀ (sub_nonneg.mpr hgap)]
  have hinv : (1 - mu S u v)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hgapPos).2 (by nlinarith [hgap])
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- A numerator bounded by `C` and a denominator separated by `1/C` have
a quotient bounded by `C²`. -/
private theorem abs_div_le_sq_of_bounds
    {x y C : ℝ} (hC : 0 < C) (hx : |x| ≤ C)
    (hy : 1 / C ≤ |y|) : |x / y| ≤ C ^ 2 := by
  have hyPos : 0 < |y| := (one_div_pos.mpr hC).trans_le hy
  rw [abs_div]
  apply (div_le_iff₀ hyPos).2
  have hmul := mul_le_mul_of_nonneg_left hy (sq_nonneg C)
  have heq : C ^ 2 * (1 / C) = C := by
    field_simp [ne_of_gt hC]
  calc
    |x| ≤ C := hx
    _ = C ^ 2 * (1 / C) := heq.symm
    _ ≤ C ^ 2 * |y| := hmul

private theorem radius_cross_ratio_le
    {C₀ C₁ K d δ rS rT : ℝ}
    (hC₀pos : 0 < C₀) (hK₀ : K ≤ C₀) (hdLow : 1 / C₀ ≤ d)
    (hM₁ : C₀ ^ 2 ≤ C₁) (hδ : 0 < δ)
    (hrS : rS ≤ K * δ) (hrT : d * δ ≤ rT) :
    rS / rT ≤ C₁ := by
  have hd : 0 < d := (one_div_pos.mpr hC₀pos).trans_le hdLow
  have hTpos : 0 < rT := (mul_pos hd hδ).trans_le hrT
  have hMd : C₀ ≤ C₀ ^ 2 * d := by
    have hm := mul_le_mul_of_nonneg_left hdLow (sq_nonneg C₀)
    have heq : C₀ ^ 2 * (1 / C₀) = C₀ := by
      field_simp [ne_of_gt hC₀pos]
    linarith
  have hraw : rS / rT ≤ C₀ ^ 2 := by
    apply (div_le_iff₀ hTpos).2
    calc
      rS ≤ K * δ := hrS
      _ ≤ (C₀ ^ 2 * d) * δ :=
        mul_le_mul_of_nonneg_right (hK₀.trans hMd) hδ.le
      _ = C₀ ^ 2 * (d * δ) := by ring
      _ ≤ C₀ ^ 2 * rT := mul_le_mul_of_nonneg_left hrT (sq_nonneg C₀)
  exact hraw.trans hM₁

/-- Preliminary scalar variation closes all comparison coefficients with
constants fixed in the order `C₀`, `ε₀`, `C₁`. The hypothesis is conditional
on a full augmented comparison triangle, and the same constants work as its
compact top varies. -/
theorem coefficient_bounds
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {w : ℝ} (href : (0, w) ∈ U₁ ∩ U₂)
    (hdata : S₁.phi 0 w = S₂.phi 0 w) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧
        ∃ C₁ : ℝ, 4 ≤ C₁ ∧
          ∀ a b, Uniqueness.triangle a b ⊆ U₁ ∩ U₂ →
            (∀ u v, (u, v) ∈ Uniqueness.triangle a b →
              ∀ S : Fields, (S = S₁ ∨ S = S₂) →
                (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀ ∧
                (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε₀) →
            ∀ u v, (u, v) ∈ Uniqueness.triangle a b →
              ∀ S : Fields, (S = S₁ ∨ S = S₂) →
                1 / C₁ ≤ S.lam u v ∧ S.lam u v ≤ C₁ ∧
                1 / C₁ ≤ |S.nu u v| ∧ |S.nu u v| ≤ C₁ ∧
                |S.phi u v| ≤ C₁ ∧ |S.theta u v| ≤ C₁ ∧
                |S.zeta u v| ≤ C₁ ∧
                1 / C₁ ≤ S.r u v / (v - u) ∧
                S.r u v / (v - u) ≤ C₁ ∧
                1 / 2 ≤ 1 - mu S u v ∧
                (1 - mu S u v)⁻¹ ≤ C₁ ∧
                |S.theta u v / S.lam u v| ≤ C₁ ∧
                |S.zeta u v / S.nu u v| ≤ C₁ ∧
                |S.alpha u v / S.lam u v| ≤ C₁ ∧
                |S.beta u v / S.nu u v| ≤ C₁ ∧
                |S.lam u v / (1 - mu S u v)| ≤ C₁ ∧
                |S.nu u v / (1 - mu S u v)| ≤ C₁ ∧
                |S.lam u v / S.nu u v| ≤ C₁ ∧
                |S.nu u v / S.lam u v| ≤ C₁ ∧
                ∀ T : Fields, (T = S₁ ∨ T = S₂) →
                  |S.lam u v / T.nu u v| ≤ C₁ ∧
                  |S.nu u v / T.lam u v| ≤ C₁ ∧
                  S.r u v / T.r u v ≤ C₁ := by
  obtain ⟨c, B, hc, hB, hfield⟩ :=
    h₁.preloc_coefficient_bounds h₂ href hdata
  obtain ⟨d₁, K₁, hd₁, hrad₁⟩ := h₁.exists_uniform_radius_bounds
  obtain ⟨d₂, K₂, hd₂, hrad₂⟩ := h₂.exists_uniform_radius_bounds
  let d := min d₁ d₂
  let K := max K₁ K₂
  have hd : 0 < d := lt_min hd₁ hd₂
  let C₀ := 1 + B + 1 / c + 1 / d + max K 0
  have hC₀ : 1 ≤ C₀ := by
    dsimp [C₀]
    have hcInv : 0 ≤ 1 / c := by positivity
    have hdInv : 0 ≤ 1 / d := by positivity
    have hK : 0 ≤ max K 0 := le_max_right _ _
    linarith
  have hB₀ : B ≤ C₀ := by
    dsimp [C₀]
    have hcInv : 0 ≤ 1 / c := by positivity
    have hdInv : 0 ≤ 1 / d := by positivity
    have hK : 0 ≤ max K 0 := le_max_right _ _
    linarith
  have hcInv₀ : 1 / c ≤ C₀ := by
    dsimp [C₀]
    have hdInv : 0 ≤ 1 / d := by positivity
    have hK : 0 ≤ max K 0 := le_max_right _ _
    linarith
  have hdInv₀ : 1 / d ≤ C₀ := by
    dsimp [C₀]
    have hcInv : 0 ≤ 1 / c := by positivity
    have hK : 0 ≤ max K 0 := le_max_right _ _
    linarith
  have hK₀ : K ≤ C₀ := by
    dsimp [C₀]
    have hcInv : 0 ≤ 1 / c := by positivity
    have hdInv : 0 ≤ 1 / d := by positivity
    have hK : K ≤ max K 0 := le_max_left _ _
    linarith
  have hC₀pos : 0 < C₀ := by linarith
  have hcLow : 1 / C₀ ≤ c := by
    have hprod := (div_le_iff₀ hc).1 hcInv₀
    apply (div_le_iff₀ hC₀pos).2
    nlinarith
  have hdLow : 1 / C₀ ≤ d := by
    have hprod := (div_le_iff₀ hd).1 hdInv₀
    apply (div_le_iff₀ hC₀pos).2
    nlinarith
  let M := C₀ ^ 2
  have hM : 0 ≤ M := sq_nonneg C₀
  let ε₀ := 1 / (2 * (M + 1))
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  have hsmall : M * ε₀ ≤ 1 / 2 := by
    have hrec : 2 * (M + 1) * ε₀ = 1 := by
      dsimp [ε₀]
      field_simp
    nlinarith [hrec, hε₀.le]
  let C₁ := 2 * (C₀ + M + 1)
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hC₁four : (4 : ℝ) ≤ C₁ := by
    dsimp [C₁]
    nlinarith [hC₀, hM]
  have hC₀₁ : C₀ ≤ C₁ := by dsimp [C₁]; linarith
  have hM₁ : M ≤ C₁ := by dsimp [C₁]; linarith
  have hB₁ : B ≤ C₁ := hB₀.trans hC₀₁
  have hK₁ : K ≤ C₁ := hK₀.trans hC₀₁
  have hcLow₁ : 1 / C₁ ≤ c := by
    have hprod := (div_le_iff₀ hc).1 (hcInv₀.trans hC₀₁)
    apply (div_le_iff₀ hC₁).2
    nlinarith
  have hdLow₁ : 1 / C₁ ≤ d := by
    have hprod := (div_le_iff₀ hd).1 (hdInv₀.trans hC₀₁)
    apply (div_le_iff₀ hC₁).2
    nlinarith
  refine ⟨C₀, hC₀, ε₀, hε₀, C₁, hC₁four, ?_⟩
  intro a b hT hXY u v huv S hS
  have hfields := hfield a b u v hT huv S hS
  obtain ⟨hlamLo, hlamHi, hnuLo, hnuHi, hphi, htheta, hzeta⟩ := hfields
  have hbase :
      1 / C₀ ≤ S.lam u v ∧ S.lam u v ≤ C₀ ∧
      1 / C₀ ≤ |S.nu u v| ∧ |S.nu u v| ≤ C₀ ∧
      |S.phi u v| ≤ C₀ ∧ |S.theta u v| ≤ C₀ ∧
      |S.zeta u v| ≤ C₀ :=
    ⟨hcLow.trans hlamLo, hlamHi.trans hB₀,
      hcLow.trans hnuLo, hnuHi.trans hB₀,
      hphi.trans hB₀, htheta.trans hB₀, hzeta.trans hB₀⟩
  have hquot : ∀ t ∈ Ioc u v,
      |S.theta u t / S.lam u t| ≤ M := by
    intro t ht
    have htT : (u, t) ∈ Uniqueness.triangle a b :=
      (Uniqueness.mem_triangle).2 ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩
    obtain ⟨htlamLo, _, _, _, _, httheta, _⟩ :=
      hfield a b u t hT htT S hS
    have htlamPos : 0 < S.lam u t := hc.trans_le htlamLo
    rw [abs_div, abs_of_pos htlamPos]
    have hraw : |S.theta u t| / S.lam u t ≤ B / c := by
      apply (div_le_div_iff₀ htlamPos hc).2
      calc
        |S.theta u t| * c ≤ B * c :=
          mul_le_mul_of_nonneg_right httheta hc.le
        _ ≤ B * S.lam u t := mul_le_mul_of_nonneg_left htlamLo hB
    have hrawLe : B / c ≤ M := by
      have hcinv : (1 / c) ≤ C₀ := hcInv₀
      have hmul := mul_le_mul hB₀ hcinv (by positivity : 0 ≤ 1 / c)
        (by linarith : 0 ≤ C₀)
      dsimp [M]
      simpa only [div_eq_mul_inv, one_div, one_mul, pow_two] using hmul
    exact hraw.trans hrawLe
  have hgap : 1 / 2 ≤ 1 - mu S u v := by
    rcases hS with rfl | rfl
    · exact h₁.gap_ge_half_of_small_outgoing_variation
        (hT huv).1 hM hquot (hXY u v huv _ (Or.inl rfl)).1 hsmall
    · exact h₂.gap_ge_half_of_small_outgoing_variation
        (hT huv).2 hM hquot (hXY u v huv _ (Or.inr rfl)).1 hsmall
  have hratio := field_ratio_bounds (by positivity : 0 < 1 / C₀)
    (by linarith : 0 ≤ C₀)
    hbase.1 hbase.2.1 hbase.2.2.1 hbase.2.2.2.1
    hbase.2.2.2.2.1 hbase.2.2.2.2.2.1 hbase.2.2.2.2.2.2 hgap
  have hBexpr : 2 * (C₀ + C₀ / (1 / C₀) + 1) = C₁ := by
    dsimp [C₁, M]
    field_simp [ne_of_gt hC₀pos]
  rw [hBexpr] at hratio
  have hrad : d * (v - u) ≤ S.r u v ∧ S.r u v ≤ K * (v - u) := by
    rcases hS with rfl | rfl
    · have hr := hrad₁ u v (hT huv).1
      exact ⟨(mul_le_mul_of_nonneg_right (min_le_left d₁ d₂)
        (sub_pos.mpr huv.2.1).le).trans hr.1,
        hr.2.trans (mul_le_mul_of_nonneg_right (le_max_left K₁ K₂)
          (sub_pos.mpr huv.2.1).le)⟩
    · have hr := hrad₂ u v (hT huv).2
      exact ⟨(mul_le_mul_of_nonneg_right (min_le_right d₁ d₂)
        (sub_pos.mpr huv.2.1).le).trans hr.1,
        hr.2.trans (mul_le_mul_of_nonneg_right (le_max_right K₁ K₂)
          (sub_pos.mpr huv.2.1).le)⟩
  have hdist : 0 < v - u := sub_pos.mpr huv.2.1
  have hrlo : 1 / C₁ ≤ S.r u v / (v - u) :=
    (hdLow₁.trans ((le_div_iff₀ hdist).2 hrad.1))
  have hrhi : S.r u v / (v - u) ≤ C₁ :=
    (div_le_iff₀ hdist).2
      (hrad.2.trans (mul_le_mul_of_nonneg_right hK₁ hdist.le))
  have hlamNu : |S.lam u v / S.nu u v| ≤ C₁ := by
    have hh := abs_div_le_sq_of_bounds (x := S.lam u v) (y := S.nu u v) hC₀pos
      (by simpa only [abs_of_pos ((one_div_pos.mpr hC₀pos).trans_le hbase.1)]
        using hbase.2.1)
      hbase.2.2.1
    exact hh.trans hM₁
  have hnuLam : |S.nu u v / S.lam u v| ≤ C₁ := by
    have hh := abs_div_le_sq_of_bounds (x := S.nu u v) (y := S.lam u v) hC₀pos
      hbase.2.2.2.1
      (by simpa only [abs_of_pos ((one_div_pos.mpr hC₀pos).trans_le hbase.1)]
        using hbase.1)
    exact hh.trans hM₁
  have hcross : ∀ T : Fields, (T = S₁ ∨ T = S₂) →
      |S.lam u v / T.nu u v| ≤ C₁ ∧
      |S.nu u v / T.lam u v| ≤ C₁ ∧
      S.r u v / T.r u v ≤ C₁ := by
    intro T hTfield
    obtain ⟨htlamLo, _, htnuLo, _, _, _, _⟩ :=
      hfield a b u v hT huv T hTfield
    have hlamT : 1 / C₀ ≤ T.lam u v := hcLow.trans htlamLo
    have hnuT : 1 / C₀ ≤ |T.nu u v| := hcLow.trans htnuLo
    have hcrossLam : |S.lam u v / T.nu u v| ≤ C₁ :=
      (abs_div_le_sq_of_bounds hC₀pos
        (by simpa only [abs_of_pos ((one_div_pos.mpr hC₀pos).trans_le hbase.1)]
          using hbase.2.1) hnuT).trans hM₁
    have hcrossNu : |S.nu u v / T.lam u v| ≤ C₁ :=
      (abs_div_le_sq_of_bounds hC₀pos hbase.2.2.2.1
        (by simpa only [abs_of_pos ((one_div_pos.mpr hC₀pos).trans_le hlamT)]
          using hlamT)).trans hM₁
    have hradT : d * (v - u) ≤ T.r u v := by
      rcases hTfield with rfl | rfl
      · exact (mul_le_mul_of_nonneg_right (min_le_left d₁ d₂) hdist.le).trans
          (hrad₁ u v (hT huv).1).1
      · exact (mul_le_mul_of_nonneg_right (min_le_right d₁ d₂) hdist.le).trans
          (hrad₂ u v (hT huv).2).1
    have hcrossR : S.r u v / T.r u v ≤ C₁ :=
      radius_cross_ratio_le hC₀pos hK₀ hdLow hM₁ hdist hrad.2 hradT
    exact ⟨hcrossLam, hcrossNu, hcrossR⟩
  exact ⟨hcLow₁.trans hlamLo, hlamHi.trans hB₁,
    hcLow₁.trans hnuLo, hnuHi.trans hB₁,
    hphi.trans hB₁, htheta.trans hB₁, hzeta.trans hB₁,
    hrlo, hrhi, hgap, hratio.2.2.2.2.2.2,
    hratio.1, hratio.2.1, hratio.2.2.1,
    hratio.2.2.2.1, hratio.2.2.2.2.1,
    hratio.2.2.2.2.2.1, hlamNu, hnuLam, hcross⟩

/-- The two mass-gap bounds exported by `coefficient_bounds` control the
product denominator occurring in the difference equations with the same
chosen `C₁`. -/
theorem cross_gap_inverse_le
    {S T : Fields} {u v C₁ : ℝ}
    (hS : 1 / 2 ≤ 1 - mu S u v)
    (hT : 1 / 2 ≤ 1 - mu T u v)
    (hC₁ : 4 ≤ C₁) :
    ((1 - mu S u v) * (1 - mu T u v))⁻¹ ≤ C₁ := by
  have hprod : 1 / 4 ≤
      (1 - mu S u v) * (1 - mu T u v) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hS)
      (sub_nonneg.mpr hT)]
  have hpos : 0 < (1 - mu S u v) * (1 - mu T u v) := by
    linarith
  have hinv : ((1 - mu S u v) * (1 - mu T u v))⁻¹ ≤ 4 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hpos).2 (by nlinarith [hprod])
  exact hinv.trans hC₁
end ChristodoulouBV.IsBVSolution

end
