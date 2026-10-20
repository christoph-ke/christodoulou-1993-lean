module

public import ChristodoulouBV.Existence.BVStieltjesScalarTransport
import Mathlib.Tactic

/-!
# Outgoing scalar transport against the analytic carrier

The scalar rectangle formula retains every canonical endpoint value.
Its outgoing specialization includes an arbitrary shifted initial edge.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The outgoing scalar correction is integrable on every compact off-axis section. -/
theorem bv_outgoing_scalar_flux_integrable
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u a b : ℝ} (hu : 0 ≤ u) (hua : u < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => d.scalarRightFields.lam u t *
      (d.scalarRightFields.theta u t / d.scalarRightFields.r u t)) volume a b := by
  let q := fun c : Fin 9 → ℝ => c 1 * ((c 4 - c 1 * c 3) * c 0)
  have hq : Continuous q := by fun_prop
  have hi := bv_area_algebra_intervalIntegrable h hD d .lamPhi hab (sub_pos.mpr hua)
    (fun t ht => show (u, t) ∈ globalDomain from ⟨hu, hua.trans_le ht.1⟩)
    (fun t ht => show a - u ≤ t - u from sub_le_sub_right ht.1 u) hq
  change IntervalIntegrable (fun t => d.scalarRightFields.lam u t *
    ((d.scalarRightFields.alpha u t - d.scalarRightFields.lam u t *
      d.scalarRightFields.phi u t) * (d.scalarRightFields.r u t)⁻¹)) volume a b at hi
  simpa only [Fields.theta, div_eq_mul_inv] using hi

/-- Increments of the outgoing pointwise residual have the scalar-flux form. -/
theorem bv_outgoing_scalar_residual_increment
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u a x y : ℝ} (hu : 0 ≤ u) (hua : u < a)
    (hax : a ≤ x) (hxy : x ≤ y) :
    bvOutgoingScalarResidual d.scalarRightFields u a y -
      bvOutgoingScalarResidual d.scalarRightFields u a x =
      d.scalarRightFields.theta u y - d.scalarRightFields.theta u x +
        ∫ t in x..y, d.scalarRightFields.lam u t *
          (d.scalarRightFields.theta u t / d.scalarRightFields.r u t) := by
  have hi := intervalIntegral.integral_interval_sub_left
    (bv_outgoing_scalar_flux_integrable h hD d hu hua (hax.trans hxy))
    (bv_outgoing_scalar_flux_integrable h hD d hu hua hax)
  dsimp only [bvOutgoingScalarResidual]
  linarith only [hi]

/-- Reversing an area primitive changes its sign, for every field record. -/
theorem bv_area_physical_primitive_swap (S : Fields) (k : AreaSectionPair)
    (z a b : ℝ) :
    areaPhysicalPrimitive k S z a b = -areaPhysicalPrimitive k S z b a := by
  simp only [areaPhysicalPrimitive, intervalIntegral.integral_symm b a]
  ring

/-- Residual increments with a basepoint to the right of both endpoints. -/
theorem bv_outgoing_scalar_residual_increment_right
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u a x y : ℝ} (hu : 0 ≤ u) (hux : u < x)
    (hxy : x ≤ y) (hya : y ≤ a) :
    bvOutgoingScalarResidual d.scalarRightFields u a y -
      bvOutgoingScalarResidual d.scalarRightFields u a x =
      d.scalarRightFields.theta u y - d.scalarRightFields.theta u x +
        ∫ t in x..y, d.scalarRightFields.lam u t *
          (d.scalarRightFields.theta u t / d.scalarRightFields.r u t) := by
  have hi := intervalIntegral.integral_interval_sub_left
    (bv_outgoing_scalar_flux_integrable h hD d hu (hux.trans_le hxy) hya).symm
    (bv_outgoing_scalar_flux_integrable h hD d hu hux (hxy.trans hya)).symm
  dsimp only [bvOutgoingScalarResidual]
  linarith only [hi]

private theorem outgoing_area_primitive_integrable
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u₀ u a x : ℝ} (hu₀ : 0 ≤ u₀)
    (huu : u₀ ≤ u) (hua : u < a) (hax : a ≤ x) :
    IntervalIntegrable (fun w => areaPhysicalPrimitive .lamPhi d.scalarRightFields w a x)
      volume u₀ u := by
  apply bv_area_primitive_integrable_transverse h hD d .lamPhi huu hax
    (A := a) (B := x) ⟨le_rfl, hax⟩ ⟨hax, le_rfl⟩ (sub_pos.mpr hua)
  · intro p hp
    exact ⟨hu₀.trans hp.1.1, hp.1.2.trans_lt (hua.trans_le hp.2.1)⟩
  · intro p hp
    change a - u ≤ p.2 - p.1
    exact sub_le_sub hp.2.1 hp.1.2

/-- Outgoing scalar residual transport, allowing a shifted initial edge.
The error is measured by the actual λ--φ carrier on the open rectangle. -/
theorem bv_outgoing_scalar_transport
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u₀ u a : ℝ} (hu₀ : 0 ≤ u₀)
    (huu : u₀ ≤ u) (hua : u < a) :
    eVariationOn (bvOutgoingScalarResidual d.scalarRightFields u a) (Ioo u a) ≤
      eVariationOn (bvOutgoingScalarResidual d.scalarRightFields u₀ a) (Ioo u a) +
        bvAnalyticArea h hD d .lamPhi (Ioo u₀ u ×ˢ Ioo u a) := by
  let S := d.scalarRightFields
  let P := fun w => -areaPhysicalPrimitive .lamPhi S w a
  have hP (x : ℝ) (hx : x ∈ Ioo u a) : Integrable (fun w => P w x)
      (volume.restrict (Ioo u₀ u)) := by
    have hi := outgoing_area_primitive_integrable h hD d hu₀ huu hx.1 hx.2.le
    have he (w : ℝ) : P w x = areaPhysicalPrimitive .lamPhi S w x a := by
      dsimp only [P, Pi.neg_apply]
      rw [bv_area_physical_primitive_swap S .lamPhi w a x, neg_neg]
    simp_rw [he]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le huu).mp hi).mono_set
      Ioo_subset_Ioc_self
  have hfg (x : ℝ) (hx : x ∈ Ioo u a) (y : ℝ) (hy : y ∈ Ioo u a) (hxy : x ≤ y) :
      (bvOutgoingScalarResidual S u a y - bvOutgoingScalarResidual S u a x) -
        (bvOutgoingScalarResidual S u₀ a y - bvOutgoingScalarResidual S u₀ a x) =
          ∫ w in Ioo u₀ u, P w y - P w x := by
    have hi := bv_alpha_rectangle_increment h hD d hu₀ huu hx.1 hxy
    dsimp only at hi
    have hu := hu₀.trans huu
    rw [bv_outgoing_scalar_residual_increment_right h hD d hu hx.1 hxy hy.2.le,
      bv_outgoing_scalar_residual_increment_right h hD d hu₀
        (huu.trans_lt hx.1) hxy hy.2.le]
    rw [intervalIntegral.integral_of_le huu, integral_Ioc_eq_integral_Ioo] at hi
    rw [show (fun w => P w y - P w x) =
        fun w => -(areaPhysicalPrimitive .lamPhi S w a y -
          areaPhysicalPrimitive .lamPhi S w a x) by
        funext w
        dsimp only [P, Pi.neg_apply]
        ring,
      integral_neg]
    have he : (∫ w in Ioo u₀ u, areaPhysicalPrimitive .lamPhi S w a y -
        areaPhysicalPrimitive .lamPhi S w a x) =
        ∫ w in Ioo u₀ u, areaPhysicalPrimitive .lamPhi S w x y := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro w hw
      have hs : MapsTo (areaPhysicalPoint .lamPhi w) (Icc x a) globalDomain := by
        intro t ht
        exact ⟨hu₀.trans hw.1.le, hw.2.trans (hx.1.trans_le ht.1)⟩
      have hg (t : ℝ) (ht : t ∈ Icc x a) :
          x - u ≤ (areaPhysicalPoint .lamPhi w t).2 -
            (areaPhysicalPoint .lamPhi w t).1 := sub_le_sub ht.1 hw.2.le
      have hb := bv_area_physical_primitive_change_base h hD d .lamPhi hx.2.le
        (sub_pos.mpr hx.1) hs hg ⟨hx.2.le, le_rfl⟩ ⟨le_rfl, hx.2.le⟩
        ⟨hxy, hy.2.le⟩
      linarith only [hb]
    rw [he]
    linarith only [hi]
  have hv := stieltjes_variation_transport
    (μ := volume.restrict (Ioo u₀ u))
    (fun x hx y hy => ((hP y hy).sub (hP x hx)).aestronglyMeasurable) hfg
  have harea : (∫⁻ w in Ioo u₀ u, eVariationOn (P w) (Ioo u a)) ≤
      bvAnalyticArea h hD d .lamPhi (Ioo u₀ u ×ˢ Ioo u a) := by
    have heArea : bvAnalyticArea h hD d .lamPhi (Ioo u₀ u ×ˢ Ioo u a) =
        ∫⁻ w in Ioo u₀ u, areaBVGlobalSectionKernel h hD d .lamPhi w (Ioo u a) := by
      simpa only [AreaSectionPair.incoming, Bool.false_eq_true, ite_false] using
        bv_area_section_rectangle h hD d .lamPhi u₀ u u a
    rw [heArea]
    apply lintegral_mono_ae
    filter_upwards [(bv_area_canonical_variation_le_global_kernel h hD d .lamPhi).filter_mono
      (ae_mono Measure.restrict_le_self), ae_restrict_mem measurableSet_Ioo] with w hw hwI
    dsimp only [P]
    rw [eVariationOn.neg]
    exact hw u a a hua.le ⟨hua.le, le_rfl⟩
      (fun t ht => show (w, t) ∈ areaSmoothDomain from
        ⟨hu₀.trans_lt hwI.1, hwI.2.trans_le ht.1⟩)
  exact hv.trans (add_le_add le_rfl harea)

end ChristodoulouBV

end
