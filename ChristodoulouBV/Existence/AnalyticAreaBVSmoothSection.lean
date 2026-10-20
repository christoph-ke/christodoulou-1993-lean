module

public import ChristodoulouBV.Existence.AnalyticAreaBVSmoothDensity
public import ChristodoulouBV.Existence.AnalyticAreaBVSmoothPrimitive
public import ChristodoulouBV.Existence.AnalyticAreaBVSmoothMeasure
import Mathlib.Tactic

/-!
# Identification of smooth section areas

On every admissible compact section, the pointwise variation and the
variation measure of the physical primitive both have the smooth
absolute Jacobian density. The open-section formulation is independent
of constant extensions at cutoff endpoints.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The absolute derivative of a smooth physical primitive is the
absolute Jacobian of the corresponding ordered planar map. -/
theorem SmoothSolutionBounds.area_physical_primitive_abs_deriv
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) (k : AreaSectionPair) {z b A B : ℝ}
    (hab : A ≤ B) (hb : b ∈ Icc A B)
    (hs : MapsTo (areaPhysicalPoint k z) (Icc A B) globalDomain)
    (hsI : MapsTo (areaPhysicalPoint k z) (Ioo A B) areaSmoothDomain) :
    AbsolutelyContinuousOnInterval (areaPhysicalPrimitive k S z b) A B ∧
      ∀ᵐ t ∂volume, t ∈ Ioo A B →
        |deriv (areaPhysicalPrimitive k S z b) t| =
          |(fderiv ℝ (areaPairMap k S) (areaPhysicalPoint k z t)).det| := by
  obtain ⟨hP, hd⟩ := h.area_physical_primitive_ac_ae k hab hb hs
  refine ⟨hP, ?_⟩
  filter_upwards [hd] with t hdt ht
  have hp := hsI ht
  have hG : globalDomain ∈ 𝓝 (areaPhysicalPoint k z t) :=
    mem_of_superset (isOpen_areaSmoothDomain.mem_nhds hp)
      (fun p hp => ⟨hp.1.le, hp.2⟩)
  have hgd := ((h.area_pair_contDiffOn k).2.differentiableOn (by norm_num)
    (areaPhysicalPoint k z t) (hs (Ioo_subset_Icc_self ht))).differentiableAt hG
  have hline : HasDerivAt (areaPhysicalPoint k z) (areaInnerDirection k) t := by
    change HasDerivAt (fun x => areaPhysicalPoint k z x) _ t
    cases hki : k.incoming with
    | false =>
      simpa only [areaPhysicalPoint, areaInnerDirection, hki, Bool.false_eq_true, ite_false]
        using (hasDerivAt_const t z).prodMk (hasDerivAt_id' t)
    | true =>
      simpa only [areaPhysicalPoint, areaInnerDirection, hki, ite_true]
        using (hasDerivAt_id' t).prodMk (hasDerivAt_const t z)
  have hc := hgd.hasFDerivAt.comp_hasDerivAt t hline
  change HasDerivAt (fun x => areaSectionG k
    (areaSectionCoefficients S (areaPhysicalPoint k z x))) _ t at hc
  rw [hdt (Ioo_subset_Icc_self ht), hc.deriv]
  exact (h.area_jacobian_density k hp.1 hp.2).symm

/-- Pointwise closed-section variation of a smooth primitive is its
absolute Jacobian integral on the open section. -/
theorem SmoothSolutionBounds.area_physical_variation_eq_jacobian_integral
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) (k : AreaSectionPair) {z b A B : ℝ}
    (hab : A ≤ B) (hb : b ∈ Icc A B)
    (hs : MapsTo (areaPhysicalPoint k z) (Icc A B) globalDomain)
    (hsI : MapsTo (areaPhysicalPoint k z) (Ioo A B) areaSmoothDomain) :
    eVariationOn (areaPhysicalPrimitive k S z b) (Icc A B) =
      ∫⁻ t in Ioo A B,
        ENNReal.ofReal |(fderiv ℝ (areaPairMap k S) (areaPhysicalPoint k z t)).det| := by
  obtain ⟨hP, hd⟩ := h.area_physical_primitive_abs_deriv k hab hb hs hsI
  have hc : ContinuousOn (areaPhysicalPrimitive k S z b) (Icc A B) := by
    simpa only [uIcc_of_le hab] using hP.continuousOn
  have hv := (null_lintegral_eq_scalar_variation hab hP (fun _ _ => rfl)).symm
  rw [eVariationOn.Ioo_eq_Icc_of_continuousOn hab hc] at hv
  rw [hv]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Ioo] with t hdt ht
  exact congrArg ENNReal.ofReal (hdt ht)

/-- A BV extension of a smooth physical primitive has the smooth
Jacobian variation measure on the open section. -/
theorem SmoothSolutionBounds.area_section_variation_measure_eq_jacobian
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) (k : AreaSectionPair) {z b A B : ℝ}
    (hab : A ≤ B) (hb : b ∈ Icc A B)
    (hs : MapsTo (areaPhysicalPoint k z) (Icc A B) globalDomain)
    (hsI : MapsTo (areaPhysicalPoint k z) (Ioo A B) areaSmoothDomain)
    {F : ℝ → ℝ} (hF : BoundedVariationOn F univ)
    (he : EqOn F (areaPhysicalPrimitive k S z b) (Ioo A B)) :
    hF.vectorMeasure.variation.restrict (Ioo A B) =
      ((volume : Measure ℝ).withDensity
        (fun t => ENNReal.ofReal
          |(fderiv ℝ (areaPairMap k S) (areaPhysicalPoint k z t)).det|)).restrict (Ioo A B) := by
  obtain ⟨hP, hd⟩ := h.area_physical_primitive_abs_deriv k hab hb hs hsI
  rw [variation_measure_restrict_eq_withDensity_of_ac hab hF hP he]
  apply Measure.ext
  intro E hE
  rw [Measure.restrict_apply hE, Measure.restrict_apply hE,
    withDensity_apply _ (hE.inter measurableSet_Ioo),
    withDensity_apply _ (hE.inter measurableSet_Ioo)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hd,
    ae_restrict_mem (hE.inter measurableSet_Ioo)] with t hdt ht
  exact congrArg ENNReal.ofReal (hdt ht.2)

end ChristodoulouBV

end
