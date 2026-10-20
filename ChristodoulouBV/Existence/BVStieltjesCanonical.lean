module

public import ChristodoulouBV.Existence.BVStieltjesMeasurable
import Mathlib.Tactic

/-!
# Canonical values of the area primitives

The scalar density in each section is absolutely continuous. The other
factor is a canonical right-continuous BV field. The resulting primitive
is right-continuous, so its actual increments are controlled by the raw
carrier's section variation measures.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The continuous factor of every canonical area section is absolutely
continuous, with the orientation selected by the ordered pair. -/
theorem bv_area_section_f_ac
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {z A B : ℝ} (hab : A ≤ B)
    (hs : MapsTo (areaPhysicalPoint k z) (Icc A B) globalDomain) :
    AbsolutelyContinuousOnInterval (fun t => areaSectionF k
      (areaSectionCoefficients d.scalarRightFields (areaPhysicalPoint k z t))) A B := by
  cases hki : k.incoming with
  | false =>
    have hsout : outSeg z A B ⊆ globalDomain := by
      rintro ⟨u, v⟩ ⟨rfl, hv⟩
      simpa only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false] using hs hv
    have hf := (bv_outgoing_mixed_scalar_density h hD d hab hsout).1
    simp only [areaSectionF, areaPhysicalPoint, hki, Bool.false_eq_true, ite_false]
    change AbsolutelyContinuousOnInterval (fun t =>
      (d.scalarRightFields.beta z t - d.scalarRightFields.nu z t * d.scalarRightFields.phi z t) *
        (d.scalarRightFields.r z t)⁻¹) A B
    simpa only [Fields.zeta, div_eq_mul_inv] using hf
  | true =>
    have hsin : inSeg z A B ⊆ globalDomain := by
      rintro ⟨u, v⟩ ⟨hu, rfl⟩
      simpa only [areaPhysicalPoint, hki, ite_true] using hs hu
    have hf := (bv_incoming_mixed_scalar_density h hD d hab hsin).1
    simp only [areaSectionF, areaPhysicalPoint, hki, ite_true]
    change AbsolutelyContinuousOnInterval (fun t =>
      (d.scalarRightFields.alpha t z - d.scalarRightFields.lam t z * d.scalarRightFields.phi t z) *
        (d.scalarRightFields.r t z)⁻¹) A B
    simpa only [Fields.theta, div_eq_mul_inv] using hf

/-- The BV factor of each canonical area primitive is right-continuous
at every admissible point of its physical section. -/
theorem bv_area_section_g_right_continuous
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {z t : ℝ}
    (hp : areaPhysicalPoint k z t ∈ globalDomain) :
    ContinuousWithinAt (fun x => areaSectionG k
      (areaSectionCoefficients d.scalarRightFields (areaPhysicalPoint k z x))) (Ici t) t := by
  cases k with
  | phiAlphaLam =>
    have hp' : (z, t) ∈ globalDomain := hp
    have hl := (right_expansions_continuous h hD d _ hp').1
    have hα := (right_scalar_derivatives_continuous h hD d _ hp').1
    have hpos := (scalar_right_fields_geometry h hD d _ hp').1
    have hne : d.rightLam z t ≠ 0 := by
      change d.scalarRightFields.lam z t ≠ 0
      linarith only [hpos]
    change ContinuousWithinAt (fun x => d.rightAlpha z x * (d.rightLam z x)⁻¹) (Ici t) t
    convert hα.div hl hne using 1
    funext x
    exact (div_eq_mul_inv _ _).symm
  | lamPhi => exact (right_expansions_continuous h hD d _ hp).1
  | phiBetaNu =>
    have hp' : (t, z) ∈ globalDomain := hp
    have hn := (right_expansions_continuous h hD d _ hp').2
    have hβ := (right_scalar_derivatives_continuous h hD d _ hp').2
    have hpos := (scalar_right_fields_geometry h hD d _ hp').2.2.1
    have hne : d.rightNu t z ≠ 0 := by
      change d.scalarRightFields.nu t z ≠ 0
      linarith only [hpos]
    change ContinuousWithinAt (fun x => d.rightBeta x z * (d.rightNu x z)⁻¹) (Ici t) t
    convert hβ.div hn hne using 1
    funext x
    exact (div_eq_mul_inv _ _).symm
  | nuPhi => exact (right_expansions_continuous h hD d _ hp).2

/-- Every canonical Stieltjes area primitive is right-continuous on
the interior of an admissible compact physical section. -/
theorem bv_area_primitive_right_continuous
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {z A B b δ : ℝ}
    (hab : A ≤ B) (hb : b ∈ Icc A B) (hδ : 0 < δ)
    (hs : MapsTo (areaPhysicalPoint k z) (Icc A B) globalDomain)
    (hgap : ∀ t ∈ Icc A B,
      δ ≤ (areaPhysicalPoint k z t).2 - (areaPhysicalPoint k z t).1) :
    ∀ t ∈ Ioo A B,
      ContinuousWithinAt (areaPhysicalPrimitive k d.scalarRightFields z b) (Ici t) t := by
  let f := fun t => areaSectionF k
    (areaSectionCoefficients d.scalarRightFields (areaPhysicalPoint k z t))
  let g := fun t => areaSectionG k
    (areaSectionCoefficients d.scalarRightFields (areaPhysicalPoint k z t))
  let q := fun t => areaSectionQ k
    (areaSectionCoefficients d.scalarRightFields (areaPhysicalPoint k z t))
  have hf : AbsolutelyContinuousOnInterval f A B := bv_area_section_f_ac h hD d k hab hs
  have hq : IntervalIntegrable q volume A B :=
    bv_area_algebra_intervalIntegrable h hD d k hab hδ hs hgap (area_section_q_continuous k)
  have hi := hq.absolutelyContinuousOnInterval_intervalIntegral
    (by simpa only [uIcc_of_le hab] using hb)
  intro t ht
  have hfc : ContinuousAt f t :=
    hf.continuousOn.continuousAt (by simpa only [uIcc_of_le hab] using Icc_mem_nhds ht.1 ht.2)
  have hic : ContinuousAt (fun x => ∫ s in b..x, q s) t :=
    hi.continuousOn.continuousAt (by simpa only [uIcc_of_le hab] using Icc_mem_nhds ht.1 ht.2)
  have hgc : ContinuousWithinAt g (Ici t) t :=
    bv_area_section_g_right_continuous h hD d k (hs ⟨ht.1.le, ht.2.le⟩)
  exact ((hfc.continuousWithinAt.mul hgc).sub continuousWithinAt_const).sub
    hic.continuousWithinAt

/-- Canonical area primitives are right-continuous also at the left
endpoint of a compact off-axis section, including the initial edge. -/
theorem bv_area_primitive_right_continuous_Ico
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {z A B b δ : ℝ}
    (hab : A ≤ B) (hb : b ∈ Icc A B) (hδ : 0 < δ)
    (hs : MapsTo (areaPhysicalPoint k z) (Icc A B) globalDomain)
    (hgap : ∀ t ∈ Icc A B,
      δ ≤ (areaPhysicalPoint k z t).2 - (areaPhysicalPoint k z t).1) :
    ∀ t ∈ Ico A B,
      ContinuousWithinAt (areaPhysicalPrimitive k d.scalarRightFields z b) (Ici t) t := by
  let f := fun t => areaSectionF k
    (areaSectionCoefficients d.scalarRightFields (areaPhysicalPoint k z t))
  let g := fun t => areaSectionG k
    (areaSectionCoefficients d.scalarRightFields (areaPhysicalPoint k z t))
  let q := fun t => areaSectionQ k
    (areaSectionCoefficients d.scalarRightFields (areaPhysicalPoint k z t))
  have hf : AbsolutelyContinuousOnInterval f A B := bv_area_section_f_ac h hD d k hab hs
  have hq : IntervalIntegrable q volume A B :=
    bv_area_algebra_intervalIntegrable h hD d k hab hδ hs hgap (area_section_q_continuous k)
  have hi := hq.absolutelyContinuousOnInterval_intervalIntegral
    (by simpa only [uIcc_of_le hab] using hb)
  intro t ht
  have hmem : uIcc A B ∈ 𝓝[Ici t] t := by
    rw [uIcc_of_le hab]
    exact mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc ht.1 le_rfl)
  have htc : t ∈ uIcc A B := by rw [uIcc_of_le hab]; exact ⟨ht.1, ht.2.le⟩
  have hfc := (hf.continuousOn.continuousWithinAt htc).mono_of_mem_nhdsWithin hmem
  have hic := (hi.continuousOn.continuousWithinAt htc).mono_of_mem_nhdsWithin hmem
  have hgc : ContinuousWithinAt g (Ici t) t :=
    bv_area_section_g_right_continuous h hD d k (hs ⟨ht.1, ht.2.le⟩)
  exact ((hfc.mul hgc).sub continuousWithinAt_const).sub hic

/-- The actual canonical primitive is the right-limit representative of
the raw carrier primitive, up to its irrelevant anchoring constant.
The transverse exception is independent of the longitudinal endpoints. -/
theorem bv_area_canonical_section_eq_rightLim
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    ∀ᵐ z : ℝ, z ∈ areaTransverseInterval k a δ →
      ∃ hb : BoundedVariationOn (areaPhysicalClampedPrimitive k d.rawFields a δ z) univ,
        ∃ c : ℝ,
          EqOn (areaPhysicalPrimitive k d.scalarRightFields z (areaSectionBase k a))
            (fun t => (areaPhysicalClampedPrimitive k d.rawFields a δ z).rightLim t + c)
            (areaPhysicalOpenSection k a δ z) ∧
          areaBVPhysicalKernel h hD d k hδ hδa z = hb.vectorMeasure.variation := by
  filter_upwards [bv_area_primitives_ae_eq_add_const h hD d k] with z hz hzI
  obtain ⟨hAB, hbase, hs, hsopen⟩ := area_section_geometry k hδ hzI
  obtain ⟨hb, hkernel⟩ := areaBVPhysicalKernel_eq_variation h hD d k hδ hδa hzI
  obtain ⟨c, he⟩ := hz _ _ _ hbase hsopen
  have he' : areaPhysicalPrimitive k d.scalarRightFields z (areaSectionBase k a)
      =ᵐ[volume.restrict (Ioo (areaSectionLower k δ z) (areaSectionUpper k a δ z))]
      fun t => areaPhysicalClampedPrimitive k d.rawFields a δ z t + c := by
    filter_upwards [he, ae_restrict_mem measurableSet_Ioo] with t ht htI
    rw [ht, area_physical_clamped_eq_on_section k d.rawFields a δ z
      ⟨htI.1.le, htI.2.le⟩]
  have hgap (t : ℝ)
      (ht : t ∈ Icc (areaSectionLower k δ z) (areaSectionUpper k a δ z)) :
      δ ≤ (areaPhysicalPoint k z t).2 - (areaPhysicalPoint k z t).1 := by
    cases hki : k.incoming <;>
      simp only [areaSectionLower, areaSectionUpper, areaPhysicalPoint, hki,
        Bool.false_eq_true, ite_false, ite_true, mem_Icc] at ht ⊢ <;>
      linarith only [ht.1, ht.2]
  have hc := bv_area_primitive_right_continuous h hD d k hAB.le hbase hδ hs hgap
  refine ⟨hb, c, ?_, hkernel⟩
  rw [areaPhysicalOpenSection_eq_Ioo]
  exact bv_eqOn_rightLim_of_ae_eq_add_const hb hc he'

/-- Canonical primitive increments are bounded by the actual variation-measure
section kernel on half-open intervals, with the endpoint mass retained. -/
theorem bv_area_primitive_increment_le_kernel
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    ∀ᵐ z : ℝ, z ∈ areaTransverseInterval k a δ →
      ∀ x ∈ areaPhysicalOpenSection k a δ z,
      ∀ y ∈ areaPhysicalOpenSection k a δ z, x ≤ y →
        edist (areaPhysicalPrimitive k d.scalarRightFields z (areaSectionBase k a) y)
          (areaPhysicalPrimitive k d.scalarRightFields z (areaSectionBase k a) x) ≤
            areaBVPhysicalKernel h hD d k hδ hδa z (Ioc x y) := by
  filter_upwards [bv_area_canonical_section_eq_rightLim h hD d k hδ hδa]
    with z hz hzI x hx y hy hxy
  obtain ⟨hb, c, he, hk⟩ := hz hzI
  rw [he hx, he hy, edist_add_right, edist_eq_enorm_sub, hk,
    ← hb.vectorMeasure_Ioc hxy]
  exact VectorMeasure.enorm_measure_le_variation _ _

/-- The pointwise open-section variation of the canonical primitive is
exactly the mass of the raw variation-measure section kernel. -/
theorem bv_area_canonical_variation_eq_kernel
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    ∀ᵐ z : ℝ, z ∈ areaTransverseInterval k a δ →
      eVariationOn (areaPhysicalPrimitive k d.scalarRightFields z (areaSectionBase k a))
        (areaPhysicalOpenSection k a δ z) =
      areaBVPhysicalKernel h hD d k hδ hδa z (areaPhysicalOpenSection k a δ z) := by
  filter_upwards [bv_area_canonical_section_eq_rightLim h hD d k hδ hδa] with z hz hzI
  obtain ⟨hb, c, he, hk⟩ := hz hzI
  rw [eVariationOn.eq_of_eqOn he, eVariationOn.add_const, hk,
    areaPhysicalOpenSection_eq_Ioo, hb.variation_vectorMeasure_Ioo_right]

end ChristodoulouBV

end
