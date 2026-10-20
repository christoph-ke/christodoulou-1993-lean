module

public import ChristodoulouBV.Existence.BVStieltjesScalarRectangle
import Mathlib.Tactic

/-!
# Transverse integrability of the canonical area primitives

Endpoint products are bounded measurable algebraic kernels. Fubini
controls the ordinary correction integral. This gives the measurability
needed when summing Stieltjes increments over a partition.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Canonical area primitives are interval-integrable in the transverse
variable on every compact off-axis rectangle. -/
theorem bv_area_primitive_integrable_transverse
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {Z W A B c t δ : ℝ}
    (hZW : Z ≤ W) (hct : c ≤ t)
    (hc : c ∈ Icc A B) (ht : t ∈ Icc A B) (hδ : 0 < δ)
    (hs : MapsTo (fun p : ℝ × ℝ => areaPhysicalPoint k p.1 p.2)
      (Icc Z W ×ˢ Icc A B) globalDomain)
    (hgap : ∀ p ∈ Icc Z W ×ˢ Icc A B,
      δ ≤ (areaPhysicalPoint k p.1 p.2).2 - (areaPhysicalPoint k p.1 p.2).1) :
    IntervalIntegrable (fun w => areaPhysicalPrimitive k d.scalarRightFields w c t)
      volume Z W := by
  let fg := fun z : Fin 9 → ℝ => areaSectionF k z * areaSectionG k z
  have hfg : Continuous fg :=
    (area_section_formulas_continuous k).1.mul (area_section_formulas_continuous k).2.1
  have hpoint (x : ℝ) (hx : x ∈ Icc A B) : IntervalIntegrable
      (fun w => fg (areaSectionCoefficients d.scalarRightFields (areaPhysicalPoint k w x)))
      volume Z W := by
    cases hki : k.incoming with
    | false =>
      have hs' : MapsTo (areaPhysicalPoint .nuPhi x) (Icc Z W) globalDomain := by
        intro w hw
        change (w, x) ∈ globalDomain
        simpa only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false] using
          hs (show (w, x) ∈ _ from ⟨hw, hx⟩)
      have hg' (w : ℝ) (hw : w ∈ Icc Z W) :
          δ ≤ (areaPhysicalPoint .nuPhi x w).2 - (areaPhysicalPoint .nuPhi x w).1 := by
        change δ ≤ x - w
        simpa only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false] using
          hgap (w, x) ⟨hw, hx⟩
      have hi := bv_area_algebra_intervalIntegrable h hD d .nuPhi hZW hδ hs' hg' hfg
      change IntervalIntegrable
        (fun w => fg (areaSectionCoefficients d.scalarRightFields (w, x))) volume Z W at hi
      simpa only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false] using hi
    | true =>
      have hs' : MapsTo (areaPhysicalPoint .lamPhi x) (Icc Z W) globalDomain := by
        intro w hw
        change (x, w) ∈ globalDomain
        simpa only [areaPhysicalPoint, hki, ite_true] using
          hs (show (w, x) ∈ _ from ⟨hw, hx⟩)
      have hg' (w : ℝ) (hw : w ∈ Icc Z W) :
          δ ≤ (areaPhysicalPoint .lamPhi x w).2 - (areaPhysicalPoint .lamPhi x w).1 := by
        change δ ≤ w - x
        simpa only [areaPhysicalPoint, hki, ite_true] using hgap (w, x) ⟨hw, hx⟩
      have hi := bv_area_algebra_intervalIntegrable h hD d .lamPhi hZW hδ hs' hg' hfg
      change IntervalIntegrable
        (fun w => fg (areaSectionCoefficients d.scalarRightFields (x, w))) volume Z W at hi
      simpa only [areaPhysicalPoint, hki, ite_true] using hi
  have hsub : Icc c t ⊆ Icc A B := Icc_subset_Icc hc.1 ht.2
  have hQ := bv_area_algebra_integrable_rectangle h hD d k hδ
    (fun p hp => hs ⟨hp.1, hsub hp.2⟩)
    (fun p hp => hgap p ⟨hp.1, hsub hp.2⟩) (area_section_q_continuous k)
  have hQi : IntervalIntegrable (fun w => ∫ x in c..t,
      areaSectionQ k (areaSectionCoefficients d.scalarRightFields (areaPhysicalPoint k w x)))
      volume Z W := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hZW]
    simpa only [intervalIntegral.integral_of_le hct, Function.uncurry, IntegrableOn]
      using hQ.integral_prod_left
  have hprod := (hpoint t ht).sub (hpoint c hc)
  have hall := hprod.sub hQi
  change IntervalIntegrable (fun w =>
    fg (areaSectionCoefficients d.scalarRightFields (areaPhysicalPoint k w t)) -
      fg (areaSectionCoefficients d.scalarRightFields (areaPhysicalPoint k w c)) -
        ∫ x in c..t, areaSectionQ k
          (areaSectionCoefficients d.scalarRightFields (areaPhysicalPoint k w x))) volume Z W
  exact hall

/-- The global carrier of a physical rectangle is the transverse
integral of its global section kernels. -/
theorem bv_area_section_rectangle
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) (Z W A B : ℝ) :
    bvAnalyticArea h hD d k
      (if k.incoming then Ioo A B ×ˢ Ioo Z W else Ioo Z W ×ˢ Ioo A B) =
        ∫⁻ z in Ioo Z W, areaBVGlobalSectionKernel h hD d k z (Ioo A B) := by
  have hm : MeasurableSet
      (if k.incoming then Ioo A B ×ˢ Ioo Z W else Ioo Z W ×ˢ Ioo A B) := by
    split_ifs <;> exact measurableSet_Ioo.prod measurableSet_Ioo
  rw [bv_analytic_area_eq_section_integral h hD d k hm,
    ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ Ioo Z W
  · rw [indicator_of_mem hz]
    apply congrArg (areaBVGlobalSectionKernel h hD d k z)
    ext x
    cases hki : k.incoming <;>
      simp only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false, ite_true,
        mem_preimage, mem_prod, hz, and_true, true_and]
  · rw [indicator_of_notMem hz]
    have he : areaPhysicalPoint k z ⁻¹'
        (if k.incoming then Ioo A B ×ˢ Ioo Z W else Ioo Z W ×ˢ Ioo A B) = ∅ := by
      ext x
      cases hki : k.incoming <;>
        simp only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false, ite_true,
          mem_preimage, mem_prod, hz, and_false, false_and, mem_empty_iff_false]
    rw [he, measure_empty]

/-- The carrier rectangle formula for arbitrary measurable transverse
and section sets, including the closed edges of logarithmic transports. -/
theorem bv_area_section_rectangle_sets
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {Z X : Set ℝ}
    (hZ : MeasurableSet Z) (hX : MeasurableSet X) :
    bvAnalyticArea h hD d k (if k.incoming then X ×ˢ Z else Z ×ˢ X) =
      ∫⁻ z in Z, areaBVGlobalSectionKernel h hD d k z X := by
  have hm : MeasurableSet (if k.incoming then X ×ˢ Z else Z ×ˢ X) := by
    split_ifs
    · exact hX.prod hZ
    · exact hZ.prod hX
  rw [bv_analytic_area_eq_section_integral h hD d k hm, ← lintegral_indicator hZ]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ Z
  · rw [indicator_of_mem hz]
    apply congrArg (areaBVGlobalSectionKernel h hD d k z)
    ext x
    cases hki : k.incoming <;>
      simp only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false, ite_true,
        mem_preimage, mem_prod, hz, and_true, true_and]
  · rw [indicator_of_notMem hz]
    have he : areaPhysicalPoint k z ⁻¹' (if k.incoming then X ×ˢ Z else Z ×ˢ X) = ∅ := by
      ext x
      cases hki : k.incoming <;>
        simp only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false, ite_true,
          mem_preimage, mem_prod, hz, and_false, false_and, mem_empty_iff_false]
    rw [he, measure_empty]

end ChristodoulouBV

end
