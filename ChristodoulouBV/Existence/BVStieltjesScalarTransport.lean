module

public import ChristodoulouBV.Existence.BVStieltjesKernel
public import ChristodoulouBV.Existence.BVStieltjesTransverse
import Mathlib.Tactic

/-!
# Scalar BV transport against the analytic carrier

The residual primitives represent `dβ - φ dν` and `dα - φ dλ` by
integration by parts. Rectangular increments are summed before taking
the supremum over partitions. The area term is the actual variation-measure carrier.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- An incoming pointwise primitive of the scalar Stieltjes residual. -/
@[expose] noncomputable def bvIncomingScalarResidual (S : Fields) (v a x : ℝ) : ℝ :=
  S.zeta x v + ∫ s in a..x, S.nu s v * (S.zeta s v / S.r s v)

/-- An outgoing pointwise primitive of the scalar Stieltjes residual. -/
@[expose] noncomputable def bvOutgoingScalarResidual (S : Fields) (u b x : ℝ) : ℝ :=
  S.theta u x + ∫ t in b..x, S.lam u t * (S.theta u t / S.r u t)

/-- The incoming scalar correction is integrable on compact off-axis sections. -/
theorem bv_incoming_scalar_flux_integrable
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a b v : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbv : b < v) :
    IntervalIntegrable (fun s => d.scalarRightFields.nu s v *
      (d.scalarRightFields.zeta s v / d.scalarRightFields.r s v)) volume a b := by
  let q := fun c : Fin 9 → ℝ => c 2 * ((c 5 - c 2 * c 3) * c 0)
  have hq : Continuous q := by fun_prop
  have hi := bv_area_algebra_intervalIntegrable h hD d .nuPhi hab (sub_pos.mpr hbv)
    (fun s hs => show (s, v) ∈ globalDomain from ⟨ha.trans hs.1, hs.2.trans_lt hbv⟩)
    (fun s hs => show v - b ≤ v - s from sub_le_sub_left hs.2 v) hq
  change IntervalIntegrable (fun s => d.scalarRightFields.nu s v *
    ((d.scalarRightFields.beta s v - d.scalarRightFields.nu s v *
      d.scalarRightFields.phi s v) * (d.scalarRightFields.r s v)⁻¹)) volume a b at hi
  simpa only [Fields.zeta, div_eq_mul_inv] using hi

/-- Canonical incoming scalar residual increments retain every endpoint value. -/
theorem bv_incoming_scalar_residual_increment
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a x y v : ℝ} (ha : 0 ≤ a)
    (hax : a ≤ x) (hxy : x ≤ y) (hyv : y < v) :
    bvIncomingScalarResidual d.scalarRightFields v a y -
      bvIncomingScalarResidual d.scalarRightFields v a x =
      d.scalarRightFields.zeta y v - d.scalarRightFields.zeta x v +
        ∫ s in x..y, d.scalarRightFields.nu s v *
          (d.scalarRightFields.zeta s v / d.scalarRightFields.r s v) := by
  have hi := intervalIntegral.integral_interval_sub_left
    (bv_incoming_scalar_flux_integrable h hD d ha (hax.trans hxy) hyv)
    (bv_incoming_scalar_flux_integrable h hD d ha hax (hxy.trans_lt hyv))
  dsimp only [bvIncomingScalarResidual]
  linarith only [hi]

private theorem incoming_area_primitive_integrable
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a x v b : ℝ} (ha : 0 ≤ a)
    (hax : a ≤ x) (hxv : x < v) (hvb : v ≤ b) :
    IntervalIntegrable (fun w => areaPhysicalPrimitive .nuPhi d.scalarRightFields w a x)
      volume v b := by
  apply bv_area_primitive_integrable_transverse h hD d .nuPhi hvb hax
    (A := a) (B := x) ⟨le_rfl, hax⟩ ⟨hax, le_rfl⟩ (sub_pos.mpr hxv)
  · intro p hp
    exact ⟨ha.trans hp.2.1, hp.2.2.trans_lt (hxv.trans_le hp.1.1)⟩
  · intro p hp
    change v - x ≤ p.1 - p.2
    exact sub_le_sub hp.1.1 hp.2.2

/-- The source incoming scalar Stieltjes inequality (6.10a), for the
canonical representatives and the actual ν--φ analytic carrier. -/
theorem eq6_10a
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a v b : ℝ} (ha : 0 < a) (hav : a < v) (hvb : v < b) :
    eVariationOn (bvIncomingScalarResidual d.scalarRightFields v a) (Ioo a v) ≤
      eVariationOn (bvIncomingScalarResidual d.scalarRightFields b a) (Ioo a v) +
        bvAnalyticArea h hD d .nuPhi (Ioo a v ×ˢ Ioo v b) := by
  let S := d.scalarRightFields
  let P := fun w => areaPhysicalPrimitive .nuPhi S w a
  have hP (x : ℝ) (hx : x ∈ Ioo a v) : Integrable (fun w => P w x)
      (volume.restrict (Ioo v b)) := by
    have hi := incoming_area_primitive_integrable h hD d ha.le hx.1.le hx.2 hvb.le
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hvb.le).mp hi).mono_set
      Ioo_subset_Ioc_self
  have hfg (x : ℝ) (hx : x ∈ Ioo a v) (y : ℝ) (hy : y ∈ Ioo a v) (hxy : x ≤ y) :
      (bvIncomingScalarResidual S v a y - bvIncomingScalarResidual S v a x) -
        (bvIncomingScalarResidual S b a y - bvIncomingScalarResidual S b a x) =
          ∫ w in Ioo v b, P w y - P w x := by
    rw [bv_incoming_scalar_residual_increment h hD d ha.le hx.1.le hxy hy.2,
      bv_incoming_scalar_residual_increment h hD d ha.le hx.1.le hxy (hy.2.trans hvb),
      bv_beta_rectangle_increment h hD d (ha.le.trans hx.1.le) hxy hy.2 hvb.le,
      intervalIntegral.integral_of_le hvb.le, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro w hw
    have hs : MapsTo (areaPhysicalPoint .nuPhi w) (Icc a y) globalDomain := by
      intro t ht
      exact ⟨ha.le.trans ht.1, ht.2.trans_lt (hy.2.trans hw.1)⟩
    have hgap (t : ℝ) (ht : t ∈ Icc a y) :
        v - y ≤ (areaPhysicalPoint .nuPhi w t).2 - (areaPhysicalPoint .nuPhi w t).1 := by
      change v - y ≤ w - t
      exact sub_le_sub hw.1.le ht.2
    have he := bv_area_physical_primitive_change_base h hD d .nuPhi
      hy.1.le (sub_pos.mpr hy.2) hs hgap ⟨le_rfl, hy.1.le⟩
      ⟨hx.1.le, hxy⟩ ⟨hy.1.le, le_rfl⟩
    change areaPhysicalPrimitive .nuPhi S w x y =
      areaPhysicalPrimitive .nuPhi S w a y - areaPhysicalPrimitive .nuPhi S w a x
    linarith only [he]
  have hv := stieltjes_variation_transport
    (μ := volume.restrict (Ioo v b))
    (fun x hx y hy => ((hP y hy).sub (hP x hx)).aestronglyMeasurable) hfg
  have harea : (∫⁻ w in Ioo v b, eVariationOn (P w) (Ioo a v)) ≤
      bvAnalyticArea h hD d .nuPhi (Ioo a v ×ˢ Ioo v b) := by
    have heArea : bvAnalyticArea h hD d .nuPhi (Ioo a v ×ˢ Ioo v b) =
        ∫⁻ w in Ioo v b, areaBVGlobalSectionKernel h hD d .nuPhi w (Ioo a v) := by
      simpa only [AreaSectionPair.incoming, ite_true] using
        bv_area_section_rectangle h hD d .nuPhi v b a v
    rw [heArea]
    apply lintegral_mono_ae
    filter_upwards [(bv_area_canonical_variation_le_global_kernel h hD d .nuPhi).filter_mono
      (ae_mono Measure.restrict_le_self), ae_restrict_mem measurableSet_Ioo] with w hw hwI
    exact hw a v a hav.le ⟨le_rfl, hav.le⟩
      (fun t ht => show (t, w) ∈ areaSmoothDomain from
        ⟨ha.trans_le ht.1, ht.2.trans_lt hwI.1⟩)
  exact hv.trans (add_le_add le_rfl harea)

end ChristodoulouBV

end
