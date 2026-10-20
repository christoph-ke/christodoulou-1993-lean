module

public import ChristodoulouBV.Existence.BVStieltjesDerivative
public import ChristodoulouBV.Existence.BVStieltjesLogResidual
import Mathlib.Tactic

/-!
# Logarithmic coefficient bounds with explicit mass-ratio inputs

The only conditional inputs below are the precise axis-to-point
mass-ratio integrability and majorant inequalities supplied by the source estimates.
The source corner theorems are not declared with these extra premises.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- An integrable scalar majorant and a nonnegative mass-ratio term
control the absolute logarithmic error in either null direction. -/
theorem bv_integral_abs_error_le
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f p A : X → ℝ} {M : ℝ}
    (hp : Integrable p μ) (hA : Integrable A μ) (hf : AEStronglyMeasurable f μ)
    (hbound : ∀ᵐ t ∂μ, |f t| ≤ M * |p t|) (hA0 : ∀ᵐ t ∂μ, 0 ≤ A t) :
    Integrable (fun t => f t - A t) μ ∧
      (∫ t, |f t - A t| ∂μ) ≤ M * (∫ t, |p t| ∂μ) + ∫ t, A t ∂μ := by
  have hfi : Integrable f μ := (hp.abs.const_mul M).mono' hf (by
    simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hfi.sub hA, ?_⟩
  calc
    (∫ t, |f t - A t| ∂μ) ≤ ∫ t, M * |p t| + A t ∂μ := by
      apply integral_mono_ae (hfi.sub hA).abs ((hp.abs.const_mul M).add hA)
      filter_upwards [hbound, hA0] with t ht hAt
      exact (abs_sub _ _).trans (add_le_add ht (le_of_eq (abs_of_nonneg hAt)))
    _ = _ := by rw [integral_add (hp.abs.const_mul M) hA, integral_const_mul]

/-- The two quadratic corrections have the same universal pointwise
majorant, with the appropriate scalar density in each direction. -/
theorem bv_log_correction_bounds
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {p : ℝ × ℝ} (hp : p ∈ globalDomain) :
    |sourceLogCorrection d.scalarRightFields p.1 p.2| ≤
      (39 * D.toReal) * |d.scalarRightFields.theta p.1 p.2 / d.scalarRightFields.r p.1 p.2| ∧
    |sourceLogCorrectionStar d.scalarRightFields p.1 p.2| ≤
      (39 * D.toReal) * |d.scalarRightFields.zeta p.1 p.2 / d.scalarRightFields.r p.1 p.2| := by
  let S := d.scalarRightFields
  obtain ⟨hθ, hζ⟩ := bv_weighted_ratio_bounds h hD d p hp
  have hb : |S.theta p.1 p.2 / S.lam p.1 p.2 - S.zeta p.1 p.2 / S.nu p.1 p.2| ≤
      39 * D.toReal := (abs_sub _ _).trans (by linarith only [hθ, hζ])
  constructor
  · dsimp only [sourceLogCorrection]
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  · dsimp only [sourceLogCorrectionStar]
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)

private theorem correction_aestronglyMeasurable
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a b : ℝ} (k : AreaSectionPair) (z : ℝ)
    (hs : MapsTo (areaPhysicalPoint k z) (Ioo a b) globalDomain) :
    AEStronglyMeasurable
      (fun t => sourceLogCorrection d.scalarRightFields
        (areaPhysicalPoint k z t).1 (areaPhysicalPoint k z t).2)
      (volume.restrict (Ioo a b)) ∧
    AEStronglyMeasurable
      (fun t => sourceLogCorrectionStar d.scalarRightFields
        (areaPhysicalPoint k z t).1 (areaPhysicalPoint k z t).2)
      (volume.restrict (Ioo a b)) := by
  let q : (Fin 9 → ℝ) → ℝ := fun c => (c 4 - c 1 * c 3) * c 0 *
    ((c 4 - c 1 * c 3) * c 7 - (c 5 - c 2 * c 3) * c 8)
  let qStar : (Fin 9 → ℝ) → ℝ := fun c => (c 5 - c 2 * c 3) * c 0 *
    ((c 4 - c 1 * c 3) * c 7 - (c 5 - c 2 * c 3) * c 8)
  have hq : Continuous q := by fun_prop
  have hqStar : Continuous qStar := by fun_prop
  have hpath : Continuous (areaPhysicalPoint k z) :=
    (area_physical_point_continuous k).comp (continuous_const.prodMk continuous_id)
  constructor
  · have hm := bv_area_algebra_aestronglyMeasurable h hD d (μ := volume) measurableSet_Ioo
      hpath.continuousOn hs hq
    change AEStronglyMeasurable (fun t =>
      d.scalarRightFields.theta (areaPhysicalPoint k z t).1 (areaPhysicalPoint k z t).2 *
      (d.scalarRightFields.r (areaPhysicalPoint k z t).1 (areaPhysicalPoint k z t).2)⁻¹ *
      (d.scalarRightFields.theta (areaPhysicalPoint k z t).1 (areaPhysicalPoint k z t).2 *
        (d.scalarRightFields.lam (areaPhysicalPoint k z t).1 (areaPhysicalPoint k z t).2)⁻¹ -
      d.scalarRightFields.zeta (areaPhysicalPoint k z t).1 (areaPhysicalPoint k z t).2 *
        (d.scalarRightFields.nu (areaPhysicalPoint k z t).1 (areaPhysicalPoint k z t).2)⁻¹))
      (volume.restrict (Ioo a b)) at hm
    simpa only [sourceLogCorrection, div_eq_mul_inv] using hm
  · have hm := bv_area_algebra_aestronglyMeasurable h hD d (μ := volume) measurableSet_Ioo
      hpath.continuousOn hs hqStar
    change AEStronglyMeasurable (fun t =>
      d.scalarRightFields.zeta (areaPhysicalPoint k z t).1 (areaPhysicalPoint k z t).2 *
      (d.scalarRightFields.r (areaPhysicalPoint k z t).1 (areaPhysicalPoint k z t).2)⁻¹ *
      (d.scalarRightFields.theta (areaPhysicalPoint k z t).1 (areaPhysicalPoint k z t).2 *
        (d.scalarRightFields.lam (areaPhysicalPoint k z t).1 (areaPhysicalPoint k z t).2)⁻¹ -
      d.scalarRightFields.zeta (areaPhysicalPoint k z t).1 (areaPhysicalPoint k z t).2 *
        (d.scalarRightFields.nu (areaPhysicalPoint k z t).1 (areaPhysicalPoint k z t).2)⁻¹))
      (volume.restrict (Ioo a b)) at hm
    simpa only [sourceLogCorrectionStar, div_eq_mul_inv] using hm

/-- The outgoing coefficient estimate with exactly the explicit mass-ratio
input. This is an internal ingredient, not a conditional export of (6.9). -/
theorem bv_outgoing_g_bound_of_mass_ratio_majorant
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u a : ℝ} (hu : 0 ≤ u) (hua : u < a)
    (hA : IntervalIntegrable (fun t =>
      (2 * d.scalarRightFields.m u t / d.scalarRightFields.r u t) *
        d.scalarRightFields.lam u t /
        ((1 - 2 * d.scalarRightFields.m u t / d.scalarRightFields.r u t) *
          d.scalarRightFields.r u t)) volume u a ∧
      (∫ t in u..a, (2 * d.scalarRightFields.m u t / d.scalarRightFields.r u t) *
        d.scalarRightFields.lam u t /
        ((1 - 2 * d.scalarRightFields.m u t / d.scalarRightFields.r u t) *
          d.scalarRightFields.r u t)) ≤
        (15 * D.toReal) * (eVariationOn (d.scalarRightFields.phi u) (Ioo u a)).toReal) :
    IntervalIntegrable (bvOutgoingLogCoefficient d.scalarRightFields u) volume u a ∧
      (∫ t in u..a, |bvOutgoingLogCoefficient d.scalarRightFields u t|) ≤
        (54 * D.toReal) * (eVariationOn (d.scalarRightFields.phi u) (Ioo u a)).toReal := by
  let S := d.scalarRightFields
  let A := fun t => (2 * S.m u t / S.r u t) * S.lam u t /
    ((1 - 2 * S.m u t / S.r u t) * S.r u t)
  have hφ : BoundedVariationOn (S.phi u) (Ioo u a) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((eVariationOn.mono _ Ioo_subset_Ioi_self).trans ((bv_scalar_variation h hD d).1 u hu))
  have hp := bv_density_integrable_and_bound hua.le hφ (bv_ae_deriv_phi_out_open h hD d hu)
  have hpi := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hua.le).mp hp.1).mono_set
    Ioo_subset_Ioc_self
  have hAi : IntegrableOn A (Ioo u a) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hua.le).mp hA.1).mono_set Ioo_subset_Ioc_self
  have hm := (correction_aestronglyMeasurable h hD d (a := u) (b := a) .lamPhi u
    (fun t ht => show (u, t) ∈ globalDomain from ⟨hu, ht.1⟩)).1
  change AEStronglyMeasurable (sourceLogCorrection S u)
    (volume.restrict (Ioo u a)) at hm
  have hb : ∀ᵐ t ∂volume.restrict (Ioo u a), |sourceLogCorrection S u t| ≤
      (39 * D.toReal) * |S.theta u t / S.r u t| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (bv_log_correction_bounds h hD d (show (u, t) ∈ globalDomain from ⟨hu, ht.1⟩)).1
  have hA0 : ∀ᵐ t ∂volume.restrict (Ioo u a), 0 ≤ A t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hg := mass_limit_geometry h d (u, t) ⟨hu, ht.1⟩
    have hl := (limit_signs_conformal h hD d (u, t) ⟨hu, ht.1⟩).2.1
    exact div_nonneg (mul_nonneg hg.2.2.2.1 hl.le)
      (mul_nonneg (by linarith only [hg.2.2.2.2.2.1]) hg.1.le)
  have he := bv_integral_abs_error_le hpi hAi hm hb hA0
  have hgi : IntegrableOn (bvOutgoingLogCoefficient S u) (Ioo u a) := he.1
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hua.le).mpr
    ((integrableOn_Ioc_iff_integrableOn_Ioo (f := bvOutgoingLogCoefficient S u)).mpr hgi), ?_⟩
  have hAb := hA.2
  have hpb := hp.2
  rw [intervalIntegral.integral_of_le hua.le, integral_Ioc_eq_integral_Ioo] at hAb hpb ⊢
  have hmul := mul_le_mul_of_nonneg_left hpb (show 0 ≤ 39 * D.toReal by positivity)
  change (∫ t in Ioo u a, |sourceLogCorrection S u t - A t|) ≤ _
  dsimp only [S, A] at he hAb hmul ⊢
  linarith only [he.2, hAb, hmul]

/-- The incoming coefficient estimate with exactly the explicit incoming
mass-ratio input. The corrected incoming sign is used throughout. -/
theorem bv_incoming_g_bound_of_mass_ratio_majorant
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a v : ℝ} (ha : 0 ≤ a) (hav : a < v)
    (hB : IntervalIntegrable (fun t =>
      (2 * d.scalarRightFields.m t v / d.scalarRightFields.r t v) *
        d.scalarRightFields.nu t v /
        ((1 - 2 * d.scalarRightFields.m t v / d.scalarRightFields.r t v) *
          d.scalarRightFields.r t v)) volume a v ∧
      -(∫ t in a..v, (2 * d.scalarRightFields.m t v / d.scalarRightFields.r t v) *
        d.scalarRightFields.nu t v /
        ((1 - 2 * d.scalarRightFields.m t v / d.scalarRightFields.r t v) *
          d.scalarRightFields.r t v)) ≤
        (24 * D.toReal) * (eVariationOn (fun t => d.scalarRightFields.phi t v)
          (Ioo a v)).toReal) :
    IntervalIntegrable (fun t => bvIncomingLogCoefficient d.scalarRightFields t v) volume a v ∧
      (∫ t in a..v, |bvIncomingLogCoefficient d.scalarRightFields t v|) ≤
        (63 * D.toReal) * (eVariationOn (fun t => d.scalarRightFields.phi t v)
          (Ioo a v)).toReal := by
  let S := d.scalarRightFields
  let A := fun t => -((2 * S.m t v / S.r t v) * S.nu t v /
    ((1 - 2 * S.m t v / S.r t v) * S.r t v))
  have hφ : BoundedVariationOn (fun t => S.phi t v) (Ioo a v) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((eVariationOn.mono _ (fun t ht => show t ∈ Ico 0 v from
        ⟨ha.trans ht.1.le, ht.2⟩)).trans
        ((bv_scalar_variation h hD d).2 v (ha.trans_lt hav)))
  have hp := bv_density_integrable_and_bound hav.le hφ (bv_ae_deriv_phi_in_open h hD d ha)
  have hpi := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hav.le).mp hp.1).mono_set
    Ioo_subset_Ioc_self
  have hAi : IntegrableOn A (Ioo a v) :=
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le hav.le).mp hB.1).mono_set
      Ioo_subset_Ioc_self).neg
  have hm := (correction_aestronglyMeasurable h hD d (a := a) (b := v) .nuPhi v
    (fun t ht => show (t, v) ∈ globalDomain from ⟨ha.trans ht.1.le, ht.2⟩)).2
  change AEStronglyMeasurable (fun t => sourceLogCorrectionStar S t v)
    (volume.restrict (Ioo a v)) at hm
  have hb : ∀ᵐ t ∂volume.restrict (Ioo a v), |sourceLogCorrectionStar S t v| ≤
      (39 * D.toReal) * |S.zeta t v / S.r t v| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (bv_log_correction_bounds h hD d
      (show (t, v) ∈ globalDomain from ⟨ha.trans ht.1.le, ht.2⟩)).2
  have hA0 : ∀ᵐ t ∂volume.restrict (Ioo a v), 0 ≤ A t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hpt : (t, v) ∈ globalDomain := ⟨ha.trans ht.1.le, ht.2⟩
    have hg := mass_limit_geometry h d (t, v) hpt
    have hn := (limit_signs_conformal h hD d (t, v) hpt).2.2.1
    apply neg_nonneg.mpr
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hg.2.2.2.1 hn.le)
      (mul_nonneg (by linarith only [hg.2.2.2.2.2.1]) hg.1.le)
  have he := bv_integral_abs_error_le hpi hAi hm hb hA0
  have heq (t : ℝ) : bvIncomingLogCoefficient S t v =
      -(sourceLogCorrectionStar S t v - A t) := by
    dsimp only [bvIncomingLogCoefficient, A]
    ring
  have hgi : IntegrableOn (fun t => bvIncomingLogCoefficient S t v) (Ioo a v) := by
    simp_rw [heq]
    exact he.1.neg
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hav.le).mpr
    ((integrableOn_Ioc_iff_integrableOn_Ioo
      (f := fun t => bvIncomingLogCoefficient S t v)).mpr hgi), ?_⟩
  have hAb : (∫ t in a..v, A t) ≤
      (24 * D.toReal) * (eVariationOn (fun t => S.phi t v) (Ioo a v)).toReal := by
    simpa only [A, intervalIntegral.integral_neg] using hB.2
  have hpb := hp.2
  rw [intervalIntegral.integral_of_le hav.le, integral_Ioc_eq_integral_Ioo] at hAb hpb ⊢
  have hmul := mul_le_mul_of_nonneg_left hpb (show 0 ≤ 39 * D.toReal by positivity)
  change (∫ t in Ioo a v, |bvIncomingLogCoefficient S t v|) ≤ _
  simp_rw [heq, abs_neg]
  dsimp only [S] at he hAb hmul ⊢
  linarith only [he.2, hAb, hmul]

end ChristodoulouBV

end
