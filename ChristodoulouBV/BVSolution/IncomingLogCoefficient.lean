module

public import ChristodoulouBV.BVSolution.IncomingAxis
public import ChristodoulouBV.BVSolution.LogCoefficient
import ChristodoulouBV.ForMathlib.BoundedVariation.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Incoming logarithmic coefficient calculus

The compact incoming mass-ratio and logarithmic derivative identities use
only complete characteristic subsegments. The endpoint estimates below use
an explicit half-open incoming ray.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.IsBVSolution

/-- The incoming mass-radius quotient is absolutely continuous on an
accessible compact segment strictly below its diagonal endpoint. -/
theorem mass_div_radius_ac_in
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {v a b : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hseg : inSeg v a b ⊆ U) :
    AbsolutelyContinuousOnInterval (fun s => S.m s v / S.r s v) a b := by
  have hsub (t : ℝ) (ht : t ∈ Icc a b) : inSeg v a t ⊆ U := by
    apply Set.Subset.trans _ hseg
    intro p hp
    have ⟨hpa, hpv⟩ : p.1 ∈ Icc a t ∧ p.2 = v := by
      simpa [inSeg] using hp
    have hpb : p.1 ∈ Icc a b := ⟨hpa.1, hpa.2.trans ht.2⟩
    simpa [inSeg] using And.intro hpb hpv
  have hrPrim (t : ℝ) (ht : t ∈ Icc a b) :
      IntervalPrimitive (fun s => S.r s v) (fun s => S.nu s v) a t :=
    h.solution.radius_in v a t ht.1 (hsub t ht)
  have hmPrim (t : ℝ) (ht : t ∈ Icc a b) :
      IntervalPrimitive (fun s => S.m s v) (fun s => massInDensity S s v) a t := by
    change IntervalPrimitive (fun s => S.m s v)
      (fun s => (1 - 2 * S.m s v / S.r s v) * S.zeta s v ^ 2 /
        (2 * S.nu s v)) a t
    exact h.solution.mass_in v a t ht.1 (hsub t ht)
  have hrAC : AbsolutelyContinuousOnInterval (fun s => S.r s v) a b :=
    absolutely_continuous_on_interval_of_primitive hab hrPrim
  have hmAC : AbsolutelyContinuousOnInterval (fun s => S.m s v) a b :=
    absolutely_continuous_on_interval_of_primitive hab hmPrim
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  have hcb : 0 < c * (v - b) := mul_pos hc (sub_pos.mpr hbv)
  have hrbound : ∀ s ∈ uIcc a b, c * (v - b) ≤ |S.r s v| := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    have hsU : (s, v) ∈ U := hseg (by
      change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
      exact ⟨hs, rfl⟩)
    have hr := h.radius_lower hlam hsU
    have hcb' : c * (v - b) ≤ c * (v - s) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hs.2 v) hc.le
    rw [abs_of_pos (h.solution.radius_pos (s, v) hsU)]
    exact hcb'.trans hr
  exact (hmAC.div_and_ae_deriv hrAC hcb hrbound).1

/-- The incoming mass-radius quotient has the quotient-rule derivative almost
everywhere on each accessible compact off-axis segment. -/
theorem mass_ratio_ae_deriv_in
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {v a b : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hseg : inSeg v a b ⊆ U) :
    ∀ᵐ s ∂volume, s ∈ Icc a b →
      deriv (fun t => S.m t v / S.r t v) s =
        (massInDensity S s v * S.r s v - S.m s v * S.nu s v) /
          S.r s v ^ 2 := by
  have hsub (t : ℝ) (ht : t ∈ Icc a b) : inSeg v a t ⊆ U := by
    apply Set.Subset.trans _ hseg
    intro p hp
    have ⟨hpa, hpv⟩ : p.1 ∈ Icc a t ∧ p.2 = v := by
      simpa [inSeg] using hp
    have hpb : p.1 ∈ Icc a b := ⟨hpa.1, hpa.2.trans ht.2⟩
    simpa [inSeg] using And.intro hpb hpv
  have hrPrim (t : ℝ) (ht : t ∈ Icc a b) :
      IntervalPrimitive (fun s => S.r s v) (fun s => S.nu s v) a t :=
    h.solution.radius_in v a t ht.1 (hsub t ht)
  have hmPrim (t : ℝ) (ht : t ∈ Icc a b) :
      IntervalPrimitive (fun s => S.m s v) (fun s => massInDensity S s v) a t := by
    change IntervalPrimitive (fun s => S.m s v)
      (fun s => (1 - 2 * S.m s v / S.r s v) * S.zeta s v ^ 2 /
        (2 * S.nu s v)) a t
    exact h.solution.mass_in v a t ht.1 (hsub t ht)
  have hrAC : AbsolutelyContinuousOnInterval (fun s => S.r s v) a b :=
    absolutely_continuous_on_interval_of_primitive hab hrPrim
  have hmAC : AbsolutelyContinuousOnInterval (fun s => S.m s v) a b :=
    absolutely_continuous_on_interval_of_primitive hab hmPrim
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  have hcb : 0 < c * (v - b) := mul_pos hc (sub_pos.mpr hbv)
  have hrbound : ∀ s ∈ uIcc a b, c * (v - b) ≤ |S.r s v| := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    have hsU : (s, v) ∈ U := hseg (by
      change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
      exact ⟨hs, rfl⟩)
    have hr := h.radius_lower hlam hsU
    have hcb' : c * (v - b) ≤ c * (v - s) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hs.2 v) hc.le
    rw [abs_of_pos (h.solution.radius_pos (s, v) hsU)]
    exact hcb'.trans hr
  have hquot := hmAC.div_and_ae_deriv hrAC hcb hrbound
  have hrDeriv : ∀ᵐ s ∂volume, s ∈ Icc a b →
      deriv (fun t => S.r t v) s = S.nu s v := by
    have hh := AbsolutelyContinuousOnInterval.ae_deriv_eq_of_integral_eq_sub
      (hrPrim b ⟨hab, le_rfl⟩).1 (fun t ht => by
        rw [uIcc_of_le hab] at ht
        exact (hrPrim t ht).2)
    simpa only [uIcc_of_le hab] using hh
  have hmDeriv : ∀ᵐ s ∂volume, s ∈ Icc a b →
      deriv (fun t => S.m t v) s = massInDensity S s v := by
    have hh := AbsolutelyContinuousOnInterval.ae_deriv_eq_of_integral_eq_sub
      (hmPrim b ⟨hab, le_rfl⟩).1 (fun t ht => by
        rw [uIcc_of_le hab] at ht
        exact (hmPrim t ht).2)
    simpa only [uIcc_of_le hab] using hh
  filter_upwards [hquot.2, hrDeriv, hmDeriv] with s hq hr hm hs
  rw [hq (by simpa only [uIcc_of_le hab] using hs), hr hs, hm hs]

/-- The incoming mass gap has a positive minimum on each accessible compact
segment below the diagonal. -/
theorem exists_mass_gap_ratio_lower_in
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {v a b : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hseg : inSeg v a b ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc a b,
      δ ≤ 1 - 2 * S.m s v / S.r s v := by
  have hq := h.mass_div_radius_ac_in hab hbv hseg
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  have hgap : AbsolutelyContinuousOnInterval
      (fun s => 1 - 2 * S.m s v / S.r s v) a b := by
    convert hconst.sub (hq.const_mul 2) using 1
    funext s
    simp only [Pi.sub_apply]
    ring
  have hcont : ContinuousOn (fun s => 1 - 2 * S.m s v / S.r s v)
      (Icc a b) := by
    simpa only [uIcc_of_le hab] using hgap.continuousOn
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    ⟨a, ⟨le_rfl, hab⟩⟩ hcont
  have hs₀U : (s₀, v) ∈ U := hseg (by
    change s₀ ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨hs₀, rfl⟩)
  have hδ : 0 < 1 - 2 * S.m s₀ v / S.r s₀ v := by
    have := (h.mass_ratio_bounds hs₀U).2
    linarith
  exact ⟨_, hδ, fun s hs => hmin hs⟩

/-- The incoming logarithmic mass gap is absolutely continuous on each
accessible compact subsegment. -/
theorem log_mass_gap_ac_in
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {v a b : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hseg : inSeg v a b ⊆ U) :
    AbsolutelyContinuousOnInterval
      (fun s => Real.log (1 - 2 * S.m s v / S.r s v)) a b := by
  have hq := h.mass_div_radius_ac_in hab hbv hseg
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  have hgap : AbsolutelyContinuousOnInterval
      (fun s => 1 - 2 * S.m s v / S.r s v) a b := by
    convert hconst.sub (hq.const_mul 2) using 1
    funext s
    simp only [Pi.sub_apply]
    ring
  obtain ⟨δ, hδ, hlow⟩ := h.exists_mass_gap_ratio_lower_in hab hbv hseg
  exact (hgap.log_and_ae_deriv hδ (by
    simpa only [uIcc_of_le hab] using hlow)).1

/-- The incoming logarithmic gap derivative is the negative radial transport
coefficient minus the incoming scalar-square contribution, almost everywhere
on a compact accessible segment. -/
theorem log_mass_gap_ae_deriv_in
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {v a b : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hseg : inSeg v a b ⊆ U) :
    ∀ᵐ s ∂volume, s ∈ Icc a b →
      deriv (fun t => Real.log (1 - 2 * S.m t v / S.r t v)) s =
        (2 * S.m s v / S.r s v) * S.nu s v /
            ((1 - 2 * S.m s v / S.r s v) * S.r s v) -
          S.zeta s v ^ 2 / (S.nu s v * S.r s v) := by
  have hq := h.mass_div_radius_ac_in hab hbv hseg
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  have hgap : AbsolutelyContinuousOnInterval
      (fun s => 1 - 2 * S.m s v / S.r s v) a b := by
    convert hconst.sub (hq.const_mul 2) using 1
    funext s
    simp only [Pi.sub_apply]
    ring
  obtain ⟨δ, hδ, hlow⟩ := h.exists_mass_gap_ratio_lower_in hab hbv hseg
  have hlog := (hgap.log_and_ae_deriv hδ (by
    simpa only [uIcc_of_le hab] using hlow)).2
  filter_upwards [hlog, h.mass_ratio_ae_deriv_in hab hbv hseg]
    with s hlog' hq' hs
  have hsU : (s, v) ∈ U := hseg (by
    change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨hs, rfl⟩)
  have hr : S.r s v ≠ 0 := ne_of_gt (h.solution.radius_pos (s, v) hsU)
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  have hnu : S.nu s v ≠ 0 := ne_of_lt
    (lt_of_le_of_lt (h.nu_le_neg_lower hc hlam hsU) (neg_lt_zero.mpr hc))
  have hg : 1 - 2 * S.m s v / S.r s v ≠ 0 := by
    have := (h.mass_ratio_bounds hsU).2
    linarith
  have hg' : S.r s v - 2 * S.m s v ≠ 0 := by
    intro hzero
    apply hg
    have hratio : 2 * S.m s v / S.r s v = 1 := by
      apply (div_eq_iff hr).2
      linarith
    linarith
  have hDer : deriv (fun t => 1 - 2 * S.m t v / S.r t v) s =
      -2 * deriv (fun t => S.m t v / S.r t v) s := by
    have hfun : (fun t => 1 - 2 * S.m t v / S.r t v) =
        (fun t => 1 - 2 * (S.m t v / S.r t v)) := by
      funext t
      ring
    rw [hfun, deriv_const_sub, deriv_const_mul_field]
    ring
  rw [uIcc_of_le hab] at hlog'
  rw [hlog' hs, hDer, hq' hs]
  unfold massInDensity
  field_simp [hr, hnu, hg, hg']
  ring

/-- The incoming radial transport coefficient in (3.1b). -/
@[expose] noncomputable def incomingCoeff (S : Fields) (s v : ℝ) : ℝ :=
  (2 * S.m s v / S.r s v) * S.nu s v /
    ((1 - 2 * S.m s v / S.r s v) * S.r s v)

/-- The incoming coefficient is integrable on every accessible compact
segment, using the incoming `λ` primitive and the positive lower bound for
`λ`. -/
theorem incomingCoeff_integrable
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {v a b : ℝ} (hab : a ≤ b) (_hbv : b < v)
    (hseg : inSeg v a b ⊆ U) :
    IntervalIntegrable (fun s => incomingCoeff S s v) volume a b := by
  let f : ℝ → ℝ := fun s =>
    (2 * S.m s v / S.r s v) * S.lam s v * S.nu s v /
      ((1 - 2 * S.m s v / S.r s v) * S.r s v)
  have hsub (t : ℝ) (ht : t ∈ Icc a b) : inSeg v a t ⊆ U := by
    apply Set.Subset.trans _ hseg
    intro p hp
    have ⟨hpa, hpv⟩ : p.1 ∈ Icc a t ∧ p.2 = v := by
      simpa [inSeg] using hp
    have hpb : p.1 ∈ Icc a b := ⟨hpa.1, hpa.2.trans ht.2⟩
    simpa [inSeg] using And.intro hpb hpv
  have hprim (t : ℝ) (ht : t ∈ Icc a b) :
      IntervalPrimitive (fun s => S.lam s v) f a t := by
    change IntervalPrimitive (fun s => S.lam s v)
      (fun s => (2 * S.m s v / S.r s v) * S.lam s v * S.nu s v /
        ((1 - 2 * S.m s v / S.r s v) * S.r s v)) a t
    exact h.solution.lam_in v a t ht.1 (hsub t ht)
  have hlamAC : AbsolutelyContinuousOnInterval (fun s => S.lam s v) a b :=
    absolutely_continuous_on_interval_of_primitive hab hprim
  have hlamCont : ContinuousOn (fun s => S.lam s v) (Icc a b) := by
    simpa only [uIcc_of_le hab] using hlamAC.continuousOn
  have hlamInv : ContinuousOn (fun s => (S.lam s v)⁻¹) (Icc a b) :=
    hlamCont.inv₀ (by
      intro s hs
      have hsU : (s, v) ∈ U := hseg (by
        change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
        exact ⟨hs, rfl⟩)
      exact ne_of_gt (h.solution.lam_pos (s, v) hsU))
  have hInt : IntervalIntegrable (fun s => f s * (S.lam s v)⁻¹) volume a b :=
    (hprim b ⟨hab, le_rfl⟩).1.mul_continuousOn (by
      simpa only [uIcc_of_le hab] using hlamInv)
  apply hInt.congr_uIoo
  intro s hs
  rw [uIoo_of_le hab] at hs
  have hsU : (s, v) ∈ U := hseg (by
    change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨⟨hs.1.le, hs.2.le⟩, rfl⟩)
  have hlam : S.lam s v ≠ 0 := ne_of_gt (h.solution.lam_pos (s, v) hsU)
  unfold f incomingCoeff
  simp only [div_eq_mul_inv]
  field_simp [hlam]

/-- On a compact incoming segment, the negative coefficient integral is
bounded by the logarithmic endpoint term and scalar variation. -/
theorem eq3_1b_compact
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {v a b M : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hseg : inSeg v a b ⊆ U)
    (hM : ∀ s ∈ Ioc a b, |S.zeta s v / S.nu s v| ≤ M) :
    -(∫ s in a..b, incomingCoeff S s v) ≤
      Real.log (1 - 2 * S.m a v / S.r a v) -
        Real.log (1 - 2 * S.m b v / S.r b v) +
        M * (eVariationOn (fun s => S.phi s v) (Ioc a b)).toReal := by
  have hφAC := h.item3_ac_in v a b hab hseg
  have hlogAC := h.log_mass_gap_ac_in hab hbv hseg
  have hcoeffInt := h.incomingCoeff_integrable hab hbv hseg
  have hlogInt := hlogAC.intervalIntegrable_deriv
  have hφInt := hφAC.intervalIntegrable_deriv.abs
  have hupperInt := hlogInt.neg.add (hφInt.const_mul M)
  have hae : ∀ᵐ s ∂volume.restrict (Icc a b),
      -incomingCoeff S s v ≤
        -(deriv (fun t => Real.log (1 - 2 * S.m t v / S.r t v)) s) +
          M * |deriv (fun t => S.phi t v) s| := by
    rw [← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [h.log_mass_gap_ae_deriv_in hab hbv hseg,
      h.scalar_ae_deriv_in hab hseg] with s hlog hφ hs
    have hs' : s ∈ Icc a b := ⟨hs.1.le, hs.2.le⟩
    have hsU : (s, v) ∈ U := hseg (by
      change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
      exact ⟨hs', rfl⟩)
    have hnu : S.nu s v < 0 := by
      obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
      exact lt_of_le_of_lt (h.nu_le_neg_lower hc hlam hsU) (neg_lt_zero.mpr hc)
    have hr : 0 < S.r s v := h.solution.radius_pos (s, v) hsU
    have hsquare : -(S.zeta s v ^ 2 / (S.nu s v * S.r s v)) =
        |S.zeta s v / S.nu s v| * |S.zeta s v / S.r s v| := by
      rw [abs_div, abs_div, abs_of_neg hnu, abs_of_pos hr]
      rw [← sq_abs (S.zeta s v)]
      field_simp
    have hbound := hM s ⟨hs.1, hs.2.le⟩
    have hmul := mul_le_mul_of_nonneg_right hbound
      (abs_nonneg (S.zeta s v / S.r s v))
    rw [hlog hs', hφ hs']
    change -incomingCoeff S s v ≤
      -(incomingCoeff S s v -
        S.zeta s v ^ 2 / (S.nu s v * S.r s v)) +
        M * |S.zeta s v / S.r s v|
    rw [← hsquare] at hmul
    linarith only [hmul]
  have hle := intervalIntegral.integral_mono_ae_restrict hab hcoeffInt.neg
    hupperInt hae
  have hvar := hφAC.eVariationOn_Ioc_eq_integral_abs_deriv hab
  have hvarReal : (eVariationOn (fun s => S.phi s v) (Ioc a b)).toReal =
      ∫ s in a..b, |deriv (fun t => S.phi t v) s| := by
    rw [hvar, ENNReal.toReal_ofReal]
    exact intervalIntegral.integral_nonneg_of_forall hab (fun s => abs_nonneg _)
  have hnegCoeff :
      (∫ s in a..b, (-fun t => incomingCoeff S t v) s) =
        -(∫ s in a..b, incomingCoeff S s v) :=
    intervalIntegral.integral_neg
  have hnegLog :
      (∫ s in a..b,
        (-(deriv fun t => Real.log (1 - 2 * S.m t v / S.r t v))) s) =
        -(∫ s in a..b,
          deriv (fun t => Real.log (1 - 2 * S.m t v / S.r t v)) s) :=
    intervalIntegral.integral_neg
  rw [intervalIntegral.integral_add hlogInt.neg (hφInt.const_mul M),
    hnegCoeff, hnegLog, hlogAC.integral_deriv_eq_sub,
    intervalIntegral.integral_const_mul] at hle
  rw [← hvarReal] at hle
  linarith only [hle]

/-- The incoming radial coefficient has the sign of the incoming expansion. -/
theorem incomingCoeff_nonpos
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {s v : ℝ} (hsv : (s, v) ∈ U) :
    incomingCoeff S s v ≤ 0 := by
  have hμ := h.mass_ratio_bounds hsv
  have hr := h.solution.radius_pos (s, v) hsv
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  have hnu : S.nu s v ≤ 0 :=
    (h.nu_le_neg_lower hc hlam hsv).trans (by linarith)
  unfold incomingCoeff
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos hμ.1 hnu)
    (mul_nonneg (by linarith) hr.le)

/-- The incoming coefficient is integrable on a complete half-open
characteristic when its scalar quotient has a finite bound. -/
theorem incomingCoeff_integrable_axis
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v M : ℝ} (huv : u < v)
    (haccess : ∀ s ∈ Ico u v, (s, v) ∈ U)
    (hM : ∀ s ∈ Ico u v, |S.zeta s v / S.nu s v| ≤ M) :
    IntegrableOn (fun s => incomingCoeff S s v) (Ioc u v) := by
  have hMnonneg : 0 ≤ M :=
    (abs_nonneg _).trans (hM u ⟨le_rfl, huv⟩)
  have haxis := h.mass_ratio_tendsto_zero_axis_in_of_half_open_access huv haccess
  have hlogAxis : Tendsto
      (fun b => Real.log (1 - 2 * S.m b v / S.r b v))
      (𝓝[<] v) (𝓝 (0 : ℝ)) := by
    have hgap : Tendsto (fun b => 1 - 2 * S.m b v / S.r b v)
        (𝓝[<] v) (𝓝 (1 : ℝ)) := by
      simpa using (tendsto_const_nhds.sub haxis)
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hgap
  obtain ⟨C, _, hvarIn⟩ := h.item3_variation
  have hslice : Ico u v ⊆ {s | (s, v) ∈ U} := by
    intro s hs
    exact haccess s hs
  have hvarFinite : eVariationOn (fun s => S.phi s v) (Ico u v) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((eVariationOn.mono (fun s => S.phi s v) hslice).trans (hvarIn v))
  let V : ℝ := (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal
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
  have hbLeft : Tendsto b atTop (𝓝[<] v) :=
    tendsto_nhdsWithin_iff.mpr ⟨hb,
      Filter.Eventually.of_forall (fun n => hbv n)⟩
  have hlogEventually : ∀ᶠ n : ℕ in atTop,
      -(Real.log (1 - 2 * S.m (b n) v / S.r (b n) v)) ≤ 1 := by
    have hh := hlogAxis.comp hbLeft
    have hev := hh.eventually (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 0))
    exact hev.mono (fun _ hn => by dsimp only [Function.comp_def] at hn; linarith)
  have hlogU : Real.log (1 - 2 * S.m u v / S.r u v) ≤ 0 := by
    have hm := h.mass_ratio_bounds (haccess u ⟨le_rfl, huv⟩)
    exact Real.log_nonpos (by linarith) (by linarith)
  have hInt (n : ℕ) : IntegrableOn
      (fun s => incomingCoeff S s v) (Ioc u (b n)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (hbu n)).1
      (h.incomingCoeff_integrable (hbu n) (hbv n)
        (incoming_seg_subset_of_half_open_access (hbv n) haccess))
  have hBound : ∀ᶠ n : ℕ in atTop,
      (∫ s in Ioc u (b n), ‖incomingCoeff S s v‖) ≤ M * V + 1 := by
    filter_upwards [hlogEventually] with n hlogN
    have hvarN : (eVariationOn (fun s => S.phi s v) (Ioc u (b n))).toReal ≤ V :=
      ENNReal.toReal_mono hvarFinite
        (eVariationOn.mono (fun s => S.phi s v) (by
          intro s hs
          exact ⟨hs.1.le, hs.2.trans_lt (hbv n)⟩))
    have hcomp := h.eq3_1b_compact (hbu n) (hbv n)
      (incoming_seg_subset_of_half_open_access (hbv n) haccess)
      (fun s hs => hM s ⟨hs.1.le, hs.2.trans_lt (hbv n)⟩)
    have hnorm : (∫ s in Ioc u (b n), ‖incomingCoeff S s v‖) =
        -(∫ s in u..b n, incomingCoeff S s v) := by
      rw [intervalIntegral.integral_of_le (hbu n)]
      calc
        (∫ s in Ioc u (b n), ‖incomingCoeff S s v‖) =
            ∫ s in Ioc u (b n), -incomingCoeff S s v := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro s hs
          have hsv := haccess s ⟨hs.1.le, hs.2.trans_lt (hbv n)⟩
          simp only [Real.norm_eq_abs, abs_of_nonpos (h.incomingCoeff_nonpos hsv)]
        _ = _ := by rw [integral_neg]
    rw [hnorm]
    have hmul := mul_le_mul_of_nonneg_left hvarN hMnonneg
    linarith only [hcomp, hmul, hlogN, hlogU]
  exact integrableOn_Ioc_of_intervalIntegral_norm_bounded_right hInt hb hBound

/-- Christodoulou's incoming coefficient bound (3.1b) on a complete
half-open incoming characteristic. The full-ray access is explicit. -/
theorem eq3_1b
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v M : ℝ} (huv : u < v)
    (haccess : ∀ s ∈ Ico u v, (s, v) ∈ U)
    (hM : ∀ s ∈ Ico u v, |S.zeta s v / S.nu s v| ≤ M) :
    -(∫ s in u..v,
      (2 * S.m s v / S.r s v) * S.nu s v /
        ((1 - 2 * S.m s v / S.r s v) * S.r s v)) ≤
      M * (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal := by
  have hMnonneg : 0 ≤ M :=
    (abs_nonneg _).trans (hM u ⟨le_rfl, huv⟩)
  have hfull : IntervalIntegrable (fun s => incomingCoeff S s v) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.le).2
      (h.incomingCoeff_integrable_axis huv haccess hM)
  let F : ℝ → ℝ := fun b => ∫ s in u..b, incomingCoeff S s v
  have hFAC : AbsolutelyContinuousOnInterval F u v :=
    hfull.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hleft : Tendsto (fun b : ℝ => b) (𝓝[<] v) (𝓝[Icc u v] v) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left inf_le_left,
      mem_of_superset (Ioo_mem_nhdsLT huv)
        (fun b hb => ⟨hb.1.le, hb.2.le⟩)⟩
  have hF : Tendsto F (𝓝[<] v)
      (𝓝 (∫ s in u..v, incomingCoeff S s v)) := by
    have hcont : ContinuousOn F (Icc u v) := by
      simpa only [uIcc_of_le huv.le] using hFAC.continuousOn
    have hh := (hcont.continuousWithinAt
      (show v ∈ Icc u v from ⟨huv.le, le_rfl⟩)).tendsto.comp hleft
    simpa only [F, Function.comp_def] using hh
  have hlogAxis : Tendsto
      (fun b => Real.log (1 - 2 * S.m b v / S.r b v))
      (𝓝[<] v) (𝓝 (0 : ℝ)) := by
    have hgap : Tendsto (fun b => 1 - 2 * S.m b v / S.r b v)
        (𝓝[<] v) (𝓝 (1 : ℝ)) := by
      simpa using (tendsto_const_nhds.sub
        (h.mass_ratio_tendsto_zero_axis_in_of_half_open_access huv haccess))
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hgap
  have hlogU : Real.log (1 - 2 * S.m u v / S.r u v) ≤ 0 := by
    have hm := h.mass_ratio_bounds (haccess u ⟨le_rfl, huv⟩)
    exact Real.log_nonpos (by linarith) (by linarith)
  obtain ⟨C, _, hvarIn⟩ := h.item3_variation
  have hslice : Ico u v ⊆ {s | (s, v) ∈ U} := by
    intro s hs
    exact haccess s hs
  have hvarFinite : eVariationOn (fun s => S.phi s v) (Ico u v) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((eVariationOn.mono (fun s => S.phi s v) hslice).trans (hvarIn v))
  let V : ℝ := (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal
  have hupper : ∀ᶠ b in 𝓝[<] v,
      -F b ≤ Real.log (1 - 2 * S.m u v / S.r u v) -
        Real.log (1 - 2 * S.m b v / S.r b v) + M * V := by
    filter_upwards [Ioo_mem_nhdsLT huv] with b hb
    have hcomp := h.eq3_1b_compact hb.1.le hb.2
      (incoming_seg_subset_of_half_open_access hb.2 haccess)
      (fun s hs => hM s ⟨hs.1.le, hs.2.trans_lt hb.2⟩)
    have hvarB : (eVariationOn (fun s => S.phi s v) (Ioc u b)).toReal ≤ V :=
      ENNReal.toReal_mono hvarFinite
        (eVariationOn.mono (fun s => S.phi s v) (by
          intro s hs
          exact ⟨hs.1.le, hs.2.trans_lt hb.2⟩))
    have hmul := mul_le_mul_of_nonneg_left hvarB hMnonneg
    dsimp [F]
    linarith only [hcomp, hmul]
  have hlimLeft : Tendsto (fun b => -F b) (𝓝[<] v)
      (𝓝 (-(∫ s in u..v, incomingCoeff S s v))) :=
    hF.neg
  have hlimRight : Tendsto
      (fun b => Real.log (1 - 2 * S.m u v / S.r u v) -
        Real.log (1 - 2 * S.m b v / S.r b v) + M * V)
      (𝓝[<] v)
      (𝓝 (Real.log (1 - 2 * S.m u v / S.r u v) + M * V)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub hlogAxis).add
        (tendsto_const_nhds (x := M * V))
  have hle := le_of_tendsto_of_tendsto hlimLeft hlimRight hupper
  dsimp [V] at hle ⊢
  change -(∫ s in u..v, incomingCoeff S s v) ≤
    M * (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal
  linarith only [hle, hlogU]

end ChristodoulouBV.IsBVSolution

end
