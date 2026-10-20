module

public import ChristodoulouBV.Existence.AnalyticAreaBV
public import ChristodoulouBV.ForMathlib.BoundedVariation.Representatives
import Mathlib.Tactic

/-!
# Representative compatibility for Stieltjes transport

The variation measure of a BV primitive depends on its right limits.
Consequently almost-everywhere changes of the primitive, including the
countable characteristic jump lines of the shared limit, do not change
the measure on an open section.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Almost-everywhere equality up to a constant determines the same right
limits on an open interval. Both functions may have arbitrary point values. -/
theorem bv_rightLim_eqOn_of_ae_eq_add_const
    {f g : ℝ → ℝ} (hf : BoundedVariationOn f univ)
    (hg : BoundedVariationOn g univ) {A B c : ℝ}
    (he : f =ᵐ[volume.restrict (Ioo A B)] fun t => g t + c) :
    EqOn f.rightLim (fun t => g.rightLim t + c) (Ioo A B) := by
  have hfr : f.rightLim =ᵐ[volume.restrict (Ioo A B)] f := by
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    filter_upwards [hf.countable_not_continuousAt.ae_notMem volume] with t ht _
    exact (Classical.not_not.mp ht).continuousWithinAt.rightLim_eq
  have hgr : g.rightLim =ᵐ[volume.restrict (Ioo A B)] g := by
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    filter_upwards [hg.countable_not_continuousAt.ae_notMem volume] with t ht _
    exact (Classical.not_not.mp ht).continuousWithinAt.rightLim_eq
  have hr : f.rightLim =ᵐ[volume.restrict (Ioo A B)] fun t => g.rightLim t + c := by
    filter_upwards [hfr, hgr, he] with t ht hs hts
    rw [ht, hs, hts]
  exact (eqOn_Ico_of_ae_eq_of_right_continuous
    (fun _ _ => hf.continuousWithinAt_rightLim)
    (fun _ _ => hg.continuousWithinAt_rightLim.add_const c) hr).mono Ioo_subset_Ico_self

/-- The Stieltjes variation measure on an open section is unchanged by
almost-everywhere equality up to an anchoring constant. -/
theorem bv_variation_measure_restrict_eq_of_ae_eq_add_const
    {f g : ℝ → ℝ} (hf : BoundedVariationOn f univ)
    (hg : BoundedVariationOn g univ) {A B c : ℝ}
    (he : f =ᵐ[volume.restrict (Ioo A B)] fun t => g t + c) :
    hf.vectorMeasure.variation.restrict (Ioo A B) =
      hg.vectorMeasure.variation.restrict (Ioo A B) := by
  have hr := bv_rightLim_eqOn_of_ae_eq_add_const hf hg he
  apply Real.measure_ext_Ioo_rat
  intro a b
  rw [Measure.restrict_apply measurableSet_Ioo, Measure.restrict_apply measurableSet_Ioo,
    Ioo_inter_Ioo, hf.variation_vectorMeasure_Ioo_right, hg.variation_vectorMeasure_Ioo_right]
  calc
    _ = eVariationOn (fun t => g.rightLim t + c)
        (Ioo (max (a : ℝ) A) (min (b : ℝ) B)) := by
      apply eVariationOn.eq_of_eqOn
      intro t ht
      exact hr ⟨(le_max_right _ _).trans_lt ht.1,
        ht.2.trans_le (min_le_right _ _)⟩
    _ = _ := eVariationOn.add_const _ _ _

/-- A right-continuous representative of a BV primitive is its right
limit at every interior point, after the anchoring constant is restored.
Bounded variation of the new representative is a consequence. -/
theorem bv_eqOn_rightLim_of_ae_eq_add_const
    {f g : ℝ → ℝ} (hf : BoundedVariationOn f univ) {A B c : ℝ}
    (hg : ∀ x ∈ Ioo A B, ContinuousWithinAt g (Ici x) x)
    (he : g =ᵐ[volume.restrict (Ioo A B)] fun t => f t + c) :
    EqOn g (fun t => f.rightLim t + c) (Ioo A B) := by
  have hr : g =ᵐ[volume.restrict (Ioo A B)] fun t => f.rightLim t + c := by
    have hfr : f.rightLim =ᵐ[volume.restrict (Ioo A B)] f := by
      apply (ae_restrict_iff' measurableSet_Ioo).mpr
      filter_upwards [hf.countable_not_continuousAt.ae_notMem volume] with t ht _
      exact (Classical.not_not.mp ht).continuousWithinAt.rightLim_eq
    filter_upwards [he, hfr] with t ht hft
    rw [hft, ht]
  intro x hx
  have hsub : Ioo x B ⊆ Ioo A B := Ioo_subset_Ioo hx.1.le le_rfl
  apply eqOn_Ico_of_ae_eq_of_right_continuous
    (a := x) (b := B) (fun t ht => hg t ⟨hx.1.trans_le ht.1, ht.2⟩)
    (fun _ _ => hf.continuousWithinAt_rightLim.add_const c)
    (hr.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
  exact ⟨le_rfl, hx.2⟩

/-- On open sections, pointwise variation of the canonical representative
is exactly the raw primitive's variation-measure mass. -/
theorem bv_variation_eq_measure_of_ae_eq_add_const
    {f g : ℝ → ℝ} (hf : BoundedVariationOn f univ) {A B c : ℝ}
    (hg : ∀ x ∈ Ioo A B, ContinuousWithinAt g (Ici x) x)
    (he : g =ᵐ[volume.restrict (Ioo A B)] fun t => f t + c) :
    eVariationOn g (Ioo A B) = hf.vectorMeasure.variation (Ioo A B) := by
  rw [hf.variation_vectorMeasure_Ioo_right,
    eVariationOn.eq_of_eqOn (bv_eqOn_rightLim_of_ae_eq_add_const hf hg he)]
  exact eVariationOn.add_const _ _ _

/-- Each canonical increment is controlled by the raw variation measure
on the corresponding half-open interval. -/
theorem bv_increment_le_measure_of_ae_eq_add_const
    {f g : ℝ → ℝ} (hf : BoundedVariationOn f univ) {A B c x y : ℝ}
    (hg : ∀ t ∈ Ioo A B, ContinuousWithinAt g (Ici t) t)
    (he : g =ᵐ[volume.restrict (Ioo A B)] fun t => f t + c)
    (hx : x ∈ Ioo A B) (hy : y ∈ Ioo A B) (hxy : x ≤ y) :
    edist (g y) (g x) ≤ hf.vectorMeasure.variation (Ioc x y) := by
  have hr := bv_eqOn_rightLim_of_ae_eq_add_const hf hg he
  rw [hr hx, hr hy, edist_add_right, edist_eq_enorm_sub]
  rw [← hf.vectorMeasure_Ioc hxy]
  exact VectorMeasure.enorm_measure_le_variation _ _

private theorem coefficients_congr {S T : Fields} {u v : ℝ}
    (hr : S.r u v = T.r u v) (hm : S.m u v = T.m u v)
    (hl : S.lam u v = T.lam u v) (hn : S.nu u v = T.nu u v)
    (hφ : S.phi u v = T.phi u v) (hα : S.alpha u v = T.alpha u v)
    (hβ : S.beta u v = T.beta u v) :
    areaSectionCoefficients S (u, v) = areaSectionCoefficients T (u, v) := by
  have hc : IsBVSolution.radiusCoeff S u v = IsBVSolution.radiusCoeff T u v := by
    simp only [IsBVSolution.radiusCoeff, hr, hm, hl, hn]
  simp only [areaSectionCoefficients, hr, hl, hn, hφ, hα, hβ, hc]

/-- Outside two common countable characteristic sets, all nine area
coefficients of the raw and canonical limits agree. The initial incoming
endpoint is excluded, consistently with the carrier's open sections. -/
theorem bv_area_coefficients_eq_off_jump_lines
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    ∃ Su Sv : Set ℝ, Su.Countable ∧ Sv.Countable ∧
      ∀ u v, 0 < u → u < v → u ∉ Su → v ∉ Sv →
        areaSectionCoefficients d.scalarRightFields (u, v) =
          areaSectionCoefficients d.rawFields (u, v) := by
  obtain ⟨Su, hSu, huc⟩ := raw_incoming_common_exceptional_set h hD d
  obtain ⟨Sv, hSv, hvc⟩ := raw_outgoing_common_exceptional_set h hD d
  refine ⟨Su, Sv, hSu, hSv, ?_⟩
  intro u v hu huv hus hvs
  obtain ⟨hn, hβ⟩ := huc u v hu huv hus
  obtain ⟨hl, hα⟩ := hvc u v hu.le huv hvs
  have hel : d.rightLam u v = d.lam u v := hl.continuousWithinAt.rightLim_eq
  have hen : d.rightNu u v = d.nu u v := hn.continuousWithinAt.rightLim_eq
  have heα : d.rightAlpha u v = d.alpha u v := hα.continuousWithinAt.rightLim_eq
  have heβ : d.rightBeta u v = d.beta u v := hβ.continuousWithinAt.rightLim_eq
  exact coefficients_congr rfl rfl hel hen rfl heα heβ

/-- For almost every transverse coordinate, the raw and canonical area
coefficients agree almost everywhere on every interior physical section.
The exceptional transverse set is common to all section endpoints. -/
theorem bv_area_coefficients_ae_on_sections
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) :
    ∀ᵐ z : ℝ, ∀ A B : ℝ,
      MapsTo (areaPhysicalPoint k z) (Ioo A B) areaSmoothDomain →
        (fun t => areaSectionCoefficients d.scalarRightFields (areaPhysicalPoint k z t))
          =ᵐ[volume.restrict (Ioo A B)]
        (fun t => areaSectionCoefficients d.rawFields (areaPhysicalPoint k z t)) := by
  obtain ⟨Su, Sv, hSu, hSv, he⟩ := bv_area_coefficients_eq_off_jump_lines h hD d
  cases hki : k.incoming with
  | false =>
    filter_upwards [hSu.ae_notMem volume] with z hz A B hs
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    filter_upwards [hSv.ae_notMem volume] with t ht htI
    have hp := hs htI
    simp only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false] at hp ⊢
    exact he z t hp.1 hp.2 hz ht
  | true =>
    filter_upwards [hSv.ae_notMem volume] with z hz A B hs
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    filter_upwards [hSu.ae_notMem volume] with t ht htI
    have hp := hs htI
    simp only [areaPhysicalPoint, hki, ite_true] at hp ⊢
    exact he t z hp.1 hp.2 ht hz

/-- Replacing coefficients almost everywhere changes the physical
Stieltjes primitive only by its anchoring constant. The integration
interval endpoints need not themselves be points of agreement. -/
theorem area_physical_primitive_ae_eq_add_const
    (k : AreaSectionPair) (S T : Fields) {z A B b : ℝ} (hb : b ∈ Icc A B)
    (he : (fun t => areaSectionCoefficients S (areaPhysicalPoint k z t))
      =ᵐ[volume.restrict (Ioo A B)]
      (fun t => areaSectionCoefficients T (areaPhysicalPoint k z t))) :
    ∃ c : ℝ, areaPhysicalPrimitive k S z b
      =ᵐ[volume.restrict (Ioo A B)] fun t => areaPhysicalPrimitive k T z b t + c := by
  let f := fun t => areaSectionF k (areaSectionCoefficients S (areaPhysicalPoint k z t)) *
    areaSectionG k (areaSectionCoefficients S (areaPhysicalPoint k z t))
  let g := fun t => areaSectionF k (areaSectionCoefficients T (areaPhysicalPoint k z t)) *
    areaSectionG k (areaSectionCoefficients T (areaPhysicalPoint k z t))
  refine ⟨g b - f b, ?_⟩
  have hea := (ae_restrict_iff' measurableSet_Ioo).mp he
  have hint {t : ℝ} (ht : t ∈ Ioo A B) :
      (∫ s in b..t, areaSectionQ k (areaSectionCoefficients S (areaPhysicalPoint k z s))) =
        ∫ s in b..t, areaSectionQ k (areaSectionCoefficients T (areaPhysicalPoint k z s)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hea, volume.ae_ne A, volume.ae_ne B] with s hs hsA hsB hsI
    have hsc : s ∈ Icc A B :=
      (uIoc_subset_uIcc.trans (uIcc_subset_Icc hb ⟨ht.1.le, ht.2.le⟩)) hsI
    rw [hs ⟨lt_of_le_of_ne hsc.1 hsA.symm, lt_of_le_of_ne hsc.2 hsB⟩]
  filter_upwards [he, ae_restrict_mem measurableSet_Ioo] with t ht htI
  have hfg : f t = g t := by dsimp only [f, g]; rw [ht]
  have hi := hint htI
  change f t - f b - (∫ s in b..t, areaSectionQ k
      (areaSectionCoefficients S (areaPhysicalPoint k z s))) =
    g t - g b - (∫ s in b..t, areaSectionQ k
      (areaSectionCoefficients T (areaPhysicalPoint k z s))) + (g b - f b)
  rw [hi, hfg]
  ring

/-- On every interior compact physical section, for almost every
transverse coordinate, the canonical and raw primitives agree almost
everywhere up to a constant. This applies simultaneously to all four
ordered area pairs and uses the existing common subsequence. -/
theorem bv_area_primitives_ae_eq_add_const
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) :
    ∀ᵐ z : ℝ, ∀ A B b : ℝ, b ∈ Icc A B →
      MapsTo (areaPhysicalPoint k z) (Ioo A B) areaSmoothDomain →
        ∃ c : ℝ, areaPhysicalPrimitive k d.scalarRightFields z b
          =ᵐ[volume.restrict (Ioo A B)]
          fun t => areaPhysicalPrimitive k d.rawFields z b t + c := by
  filter_upwards [bv_area_coefficients_ae_on_sections h hD d k] with z hz A B b hb hs
  exact area_physical_primitive_ae_eq_add_const k _ _ hb (hz A B hs)

end ChristodoulouBV

end
