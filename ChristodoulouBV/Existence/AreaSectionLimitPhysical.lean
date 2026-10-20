module

public import ChristodoulouBV.Existence.AreaSectionLimitMeasureCore
import Mathlib.Tactic

/-!
# Lower semicontinuity on the physical area sections

The actual Stieltjes primitives converge at every physical section
point. Their variation therefore satisfies the liminf inequality before
any transverse integration. No new subsequence is selected.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Dominated convergence of the concrete physical primitives on an
arbitrary admissible compact null section. -/
theorem area_physical_primitive_limit
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    (k : AreaSectionPair) {z b t A B δ : ℝ} (hδ : 0 < δ)
    (hs : MapsTo (areaPhysicalPoint k z) (Icc A B) globalDomain)
    (hgap : ∀ s ∈ Icc A B,
      δ ≤ (areaPhysicalPoint k z s).2 - (areaPhysicalPoint k z s).1)
    (hb : b ∈ Icc A B) (ht : t ∈ Icc A B) :
    Tendsto (fun n => areaPhysicalPrimitive k (T (d.subsequence n)) z b t)
      atTop (𝓝 (areaPhysicalPrimitive k d.rawFields z b t)) := by
  let c := fun n s => areaSectionCoefficients (T (d.subsequence n)) (areaPhysicalPoint k z s)
  let c₀ := fun s => areaSectionCoefficients d.rawFields (areaPhysicalPoint k z s)
  have hclim (s : ℝ) (hs' : s ∈ Icc A B) :
      Tendsto (fun n => c n s) atTop (𝓝 (c₀ s)) :=
    d.area_section_coefficients_limit h (hs hs')
  have hq := area_section_q_continuous k
  obtain ⟨M, hM⟩ := area_section_uniform_bound_of_continuous h hδ hq
  have hsub : uIoc b t ⊆ Icc A B := uIoc_subset_uIcc.trans (uIcc_subset_Icc hb ht)
  have hpoint : Continuous (areaPhysicalPoint k z) :=
    (area_physical_point_continuous k).comp (continuous_const.prodMk continuous_id)
  have hi : Tendsto (fun n => ∫ s in b..t, areaSectionQ k (c n s)) atTop
      (𝓝 (∫ s in b..t, areaSectionQ k (c₀ s))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (bound := fun _ => M)
    · exact Eventually.of_forall fun n =>
        ((hq.continuousOn.comp
          ((h (d.subsequence n)).area_section_coefficients_continuousOn.comp
            hpoint.continuousOn hs) (fun _ _ => mem_univ _)).aestronglyMeasurable
              measurableSet_Icc).mono_set hsub
    · refine Eventually.of_forall fun n => Eventually.of_forall fun s hs' => ?_
      simpa only [Real.norm_eq_abs] using
        hM (d.subsequence n) _ (hs (hsub hs')) (hgap s (hsub hs'))
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun s hs' => (hq.tendsto _).comp (hclim s (hsub hs'))
  obtain ⟨hf, hg, _, _⟩ := area_section_formulas_continuous k
  exact ((((hf.tendsto _).comp (hclim t ht)).mul ((hg.tendsto _).comp (hclim t ht))).sub
    (((hf.tendsto _).comp (hclim b hb)).mul ((hg.tendsto _).comp (hclim b hb)))).sub hi

/-- Variation lower semicontinuity of each actual physical primitive
on every admissible compact section, with its exact endpoint values. -/
theorem area_physical_variation_le_liminf
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    (k : AreaSectionPair) {z b A B δ : ℝ} (hδ : 0 < δ)
    (hs : MapsTo (areaPhysicalPoint k z) (Icc A B) globalDomain)
    (hgap : ∀ s ∈ Icc A B,
      δ ≤ (areaPhysicalPoint k z s).2 - (areaPhysicalPoint k z s).1)
    (hb : b ∈ Icc A B) :
    eVariationOn (areaPhysicalPrimitive k d.rawFields z b) (Icc A B) ≤
      liminf (fun n => eVariationOn
        (areaPhysicalPrimitive k (T (d.subsequence n)) z b) (Icc A B)) atTop :=
  eVariationOn.le_liminf_of_tendsto_pointwise fun _ ht =>
    area_physical_primitive_limit h d k hδ hs hgap hb ht

/-- The four concrete approximating sections
satisfy the weak primitive liminf inequality on each truncated triangle.
The physical formulation includes the signed inner coordinate weights
through the Stieltjes change of variable. -/
theorem lemma61_applicability
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    (k : AreaSectionPair) {a δ : ℝ} (hδ : 0 < δ) (hδa : δ < a)
    (y : Ioo (0 : ℝ) 1) :
    areaSectionVariation k d.rawFields a δ y ≤
      liminf (fun n => areaSectionVariation k (T (d.subsequence n)) a δ y) atTop := by
  let w := (a - δ) * (y : ℝ)
  have hw : 0 < w := mul_pos (sub_pos.mpr hδa) y.property.1
  have hwa : δ + w < a := by
    have hy := y.property.2
    have haδ : 0 < a - δ := sub_pos.mpr hδa
    dsimp only [w]
    nlinarith only [haδ, hy]
  cases hki : k.incoming with
  | false =>
    simp only [areaSectionVariation, hki, Bool.false_eq_true, ite_false]
    apply area_physical_variation_le_liminf h d k hδ
      (A := δ + w) (B := a) (b := a)
    · intro s hs
      simp only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false]
      exact ⟨hw.le, by linarith only [hs.1, hδ]⟩
    · intro s hs
      simp only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false]
      linarith only [hs.1]
    · exact ⟨hwa.le, le_rfl⟩
  | true =>
    simp only [areaSectionVariation, hki, ite_true]
    apply area_physical_variation_le_liminf h d k hδ
      (A := 0) (B := w) (b := 0)
    · intro s hs
      simp only [areaPhysicalPoint, hki, ite_true]
      exact ⟨hs.1, by linarith only [hs.2, hδ]⟩
    · intro s hs
      simp only [areaPhysicalPoint, hki, ite_true]
      linarith only [hs.2]
    · exact ⟨le_rfl, hw.le⟩

end ChristodoulouBV

end
