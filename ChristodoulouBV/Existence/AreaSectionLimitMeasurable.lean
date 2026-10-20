module

public import ChristodoulouBV.Existence.AreaSectionLimitMeasureCore
import Mathlib.Tactic

/-!
# Measurability of the four concrete BV area sections

The common sets are physical jump lines. Moving the ends of a physical
partition proves lower semicontinuity of each variation outside a
countable set of parameters. This retains prescribed point values and
does not use the failed rectangle-`L∞` argument in printed Lemma 6.2.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem measurable_area_section_variation
    (S : Fields) (k : AreaSectionPair) {a δ : ℝ} (hδ : 0 < δ) (hδa : δ < a)
    {Su Sv : Set ℝ} (hSu : Su.Countable) (hSv : Sv.Countable)
    (hcu : ∀ u v, 0 < u → u < v → u ∉ Su →
      ContinuousAt (fun t => areaSectionCoefficients S (t, v)) u)
    (hcv : ∀ u v, 0 ≤ u → u < v → v ∉ Sv →
      ContinuousAt (fun t => areaSectionCoefficients S (u, t)) v)
    (hcj : ∀ u v, 0 < u → u < v → u ∉ Su → v ∉ Sv →
      ContinuousAt (areaSectionCoefficients S) (u, v))
    (M : ℝ) (hM : ∀ p, p ∈ globalDomain → δ / 4 ≤ p.2 - p.1 →
      |areaSectionQ k (areaSectionCoefficients S p)| ≤ M)
    (hMeas : ∀ z A B, MapsTo (areaPhysicalPoint k z) (Icc A B) globalDomain →
      AEStronglyMeasurable
        (fun t => areaSectionQ k (areaSectionCoefficients S (areaPhysicalPoint k z t)))
        (volume.restrict (Icc A B))) :
    Measurable (areaSectionVariation k S a δ) ∧
      ∃ E : Set (Ioo (0 : ℝ) 1), E.Countable ∧ ∀ y ∉ E, ∀ s : ℝ,
        ContinuousAt (fun w => areaClampedPrimitive k S a δ w s) y := by
  classical
  let Y := Ioo (0 : ℝ) 1
  have haδ : 0 < a - δ := sub_pos.mpr hδa
  cases hki : k.incoming with
  | false =>
    let z : Y → ℝ := fun y => (a - δ) * y
    let t : Y → ℝ := fun y => δ + z y
    have hz : Continuous z := continuous_const.mul continuous_subtype_val
    have ht : Continuous t := continuous_const.add hz
    have hzpos (y : Y) : 0 < z y := mul_pos haδ y.property.1
    have hta (y : Y) : t y < a := by
      have hy := y.property.2
      dsimp only [t, z]
      nlinarith only [haδ, hy]
    have hzinj : Function.Injective z := by
      intro x y hxy
      apply Subtype.ext
      exact mul_left_cancel₀ haδ.ne' hxy
    have htinj : Function.Injective t := by
      intro x y hxy
      exact hzinj (add_left_cancel hxy)
    let E := z ⁻¹' Su ∪ t ⁻¹' Sv
    have hSc : E.Countable := (hSu.preimage hzinj).union (hSv.preimage htinj)
    have hpoint (z s : ℝ) : areaPhysicalPoint k z s = (z, s) := by
      simp only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false]
    have hstrong (y : Y) (hy : y ∉ E) : LowerSemicontinuousAt
        (fun w : Y => eVariationOn (areaPhysicalPrimitive k S (z w) a)
          (Icc (t w) a)) y ∧ ∀ s : ℝ,
            ContinuousAt (fun w => areaClampedPrimitive k S a δ w s) y := by
      have hyu : z y ∉ Su := fun hm => hy (Or.inl hm)
      have hyv : t y ∉ Sv := fun hm => hy (Or.inr hm)
      let A := z y + δ / 2
      let B := a + 1
      have ha : a ∈ Icc A B := by dsimp only [A, B]; constructor <;> linarith only [hta y, hδ]
      have hty : t y ∈ Ioo A B := by
        dsimp only [A, B, t]
        constructor <;> linarith only [hta y, hδ]
      have htnear : ∀ᶠ w in 𝓝 y, t w ∈ Icc A B :=
        ((ht.tendsto y).eventually (Ioo_mem_nhds hty.1 hty.2)).mono
          (fun _ hw => ⟨hw.1.le, hw.2.le⟩)
      have hz_near : ∀ᶠ w in 𝓝 y, z w < z y + δ / 4 :=
        (hz.tendsto y).eventually (Iio_mem_nhds (by linarith only [hδ]))
      have hgeo (w : Y) (hw : z w < z y + δ / 4) (s : ℝ) (hs : s ∈ Icc A B) :
          areaPhysicalPoint k (z w) s ∈ globalDomain ∧
            δ / 4 ≤ (areaPhysicalPoint k (z w) s).2 -
              (areaPhysicalPoint k (z w) s).1 := by
        rw [hpoint]
        have hs0 : z y + δ / 2 ≤ s := hs.1
        exact ⟨⟨(hzpos w).le, by linarith only [hw, hs0, hδ]⟩,
          by linarith only [hw, hs0]⟩
      have hqmeas : ∀ᶠ w in 𝓝 y, AEStronglyMeasurable
          (fun s => areaSectionQ k
            (areaSectionCoefficients S (areaPhysicalPoint k (z w) s)))
          (volume.restrict (Icc A B)) := by
        filter_upwards [hz_near] with w hw
        exact hMeas (z w) A B (fun s hs => (hgeo w hw s hs).1)
      have hqbound : ∀ᶠ w in 𝓝 y, ∀ s ∈ Icc A B,
          |areaSectionQ k
            (areaSectionCoefficients S (areaPhysicalPoint k (z w) s))| ≤ M := by
        filter_upwards [hz_near] with w hw s hs
        exact hM _ (hgeo w hw s hs).1 (hgeo w hw s hs).2
      have hfixed (s : ℝ) (hs : s ∈ Icc A B) : ContinuousAt
          (fun w => areaSectionCoefficients S (areaPhysicalPoint k (z w) s)) y := by
        have hys : z y < s := by have := hs.1; dsimp only [A] at this; linarith only [this, hδ]
        simpa only [hpoint, Function.comp_def] using
          (hcu (z y) s (hzpos y) hys hyu).comp hz.continuousAt
      have hend : ContinuousAt
          (fun w => areaSectionCoefficients S (areaPhysicalPoint k (z w) (t w))) y := by
        have hyt : z y < t y := by dsimp only [t]; linarith only [hδ]
        simpa only [hpoint, Function.comp_def] using
          (hcj (z y) (t y) (hzpos y) hyt hyu hyv).comp
            (f := fun w => (z w, t w)) (hz.prodMk ht).continuousAt
      have hbase := hfixed a ha
      have hleft := continuousAt_areaPhysicalPrimitive k S ha
        ⟨hty.1.le, hty.2.le⟩ ht.continuousAt htnear hbase hend hfixed hqmeas hqbound
      have hright : ContinuousAt (fun w => areaPhysicalPrimitive k S (z w) a a) y := by
        simpa only [area_physical_primitive_base] using (continuousAt_const (y := (0 : ℝ)))
      have hGphysical (s : ℝ) (hs : s ∈ Icc (t y) a) :
          ContinuousAt (fun w => areaPhysicalPrimitive k S (z w) a s) y := by
        have hs' : s ∈ Icc A B := ⟨hty.1.le.trans hs.1, hs.2.trans ha.2⟩
        exact continuousAt_areaPhysicalPrimitive k S ha hs' continuousAt_const
          (Eventually.of_forall fun _ => hs') hbase (hfixed s hs') hfixed hqmeas hqbound
      refine ⟨lowerSemicontinuousAt_variation_moving_interval ht.continuousAt
        continuousAt_const hta hGphysical hleft hright, ?_⟩
      intro s
      simpa only [areaClampedPrimitive, hki, Bool.false_eq_true, ite_false] using
        continuousAt_constant_extension_moving_interval ht.continuousAt continuousAt_const
          hta hGphysical hleft hright s
    constructor
    · change Measurable (fun y : Y => areaSectionVariation k S a δ y)
      simp only [areaSectionVariation, hki, Bool.false_eq_true, ite_false]
      apply measurable_of_measurable_on_compl_countable E hSc
      apply (lowerSemicontinuous_restrict_iff.mpr ?_).measurable
      intro y hy
      exact ((hstrong y hy).1).lowerSemicontinuousWithinAt _
    · exact ⟨E, hSc, fun y hy s => (hstrong y hy).2 s⟩
  | true =>
    let t : Y → ℝ := fun y => (a - δ) * y
    let z : Y → ℝ := fun y => δ + t y
    have ht : Continuous t := continuous_const.mul continuous_subtype_val
    have hz : Continuous z := continuous_const.add ht
    have htpos (y : Y) : 0 < t y := mul_pos haδ y.property.1
    have hzpos (y : Y) : 0 < z y := by dsimp only [z]; linarith only [htpos y, hδ]
    have htinj : Function.Injective t := by
      intro x y hxy
      apply Subtype.ext
      exact mul_left_cancel₀ haδ.ne' hxy
    have hzinj : Function.Injective z := by
      intro x y hxy
      exact htinj (add_left_cancel hxy)
    let E := z ⁻¹' Sv ∪ t ⁻¹' Su
    have hSc : E.Countable := (hSv.preimage hzinj).union (hSu.preimage htinj)
    have hpoint (z s : ℝ) : areaPhysicalPoint k z s = (s, z) := by
      simp only [areaPhysicalPoint, hki, ite_true]
    have hstrong (y : Y) (hy : y ∉ E) : LowerSemicontinuousAt
        (fun w : Y => eVariationOn (areaPhysicalPrimitive k S (z w) 0)
          (Icc 0 (t w))) y ∧ ∀ s : ℝ,
            ContinuousAt (fun w => areaClampedPrimitive k S a δ w s) y := by
      have hyv : z y ∉ Sv := fun hm => hy (Or.inl hm)
      have hyu : t y ∉ Su := fun hm => hy (Or.inr hm)
      let A : ℝ := 0
      let B := z y - δ / 2
      have ha : (0 : ℝ) ∈ Icc A B := by
        dsimp only [A, B, z]
        exact ⟨le_rfl, by linarith only [htpos y, hδ]⟩
      have hty : t y ∈ Ioo A B := by
        dsimp only [A, B, z]
        exact ⟨htpos y, by linarith only [hδ]⟩
      have htnear : ∀ᶠ w in 𝓝 y, t w ∈ Icc A B :=
        ((ht.tendsto y).eventually (Ioo_mem_nhds hty.1 hty.2)).mono
          (fun _ hw => ⟨hw.1.le, hw.2.le⟩)
      have hz_near : ∀ᶠ w in 𝓝 y, z y - δ / 4 < z w :=
        (hz.tendsto y).eventually (Ioi_mem_nhds (by linarith only [hδ]))
      have hgeo (w : Y) (hw : z y - δ / 4 < z w) (s : ℝ) (hs : s ∈ Icc A B) :
          areaPhysicalPoint k (z w) s ∈ globalDomain ∧
            δ / 4 ≤ (areaPhysicalPoint k (z w) s).2 -
              (areaPhysicalPoint k (z w) s).1 := by
        rw [hpoint]
        have hs0 : s ≤ z y - δ / 2 := hs.2
        exact ⟨⟨hs.1, by linarith only [hw, hs0, hδ]⟩,
          by linarith only [hw, hs0]⟩
      have hqmeas : ∀ᶠ w in 𝓝 y, AEStronglyMeasurable
          (fun s => areaSectionQ k
            (areaSectionCoefficients S (areaPhysicalPoint k (z w) s)))
          (volume.restrict (Icc A B)) := by
        filter_upwards [hz_near] with w hw
        exact hMeas (z w) A B (fun s hs => (hgeo w hw s hs).1)
      have hqbound : ∀ᶠ w in 𝓝 y, ∀ s ∈ Icc A B,
          |areaSectionQ k
            (areaSectionCoefficients S (areaPhysicalPoint k (z w) s))| ≤ M := by
        filter_upwards [hz_near] with w hw s hs
        exact hM _ (hgeo w hw s hs).1 (hgeo w hw s hs).2
      have hfixed (s : ℝ) (hs : s ∈ Icc A B) : ContinuousAt
          (fun w => areaSectionCoefficients S (areaPhysicalPoint k (z w) s)) y := by
        have hys : s < z y := by have := hs.2; dsimp only [B] at this; linarith only [this, hδ]
        simpa only [hpoint, Function.comp_def] using
          (hcv s (z y) hs.1 hys hyv).comp hz.continuousAt
      have hend : ContinuousAt
          (fun w => areaSectionCoefficients S (areaPhysicalPoint k (z w) (t w))) y := by
        have hyt : t y < z y := by dsimp only [z]; linarith only [hδ]
        simpa only [hpoint, Function.comp_def] using
          (hcj (t y) (z y) (htpos y) hyt hyu hyv).comp
            (f := fun w => (t w, z w)) (ht.prodMk hz).continuousAt
      have hbase := hfixed 0 ha
      have hright := continuousAt_areaPhysicalPrimitive k S ha
        ⟨hty.1.le, hty.2.le⟩ ht.continuousAt htnear hbase hend hfixed hqmeas hqbound
      have hleft : ContinuousAt (fun w => areaPhysicalPrimitive k S (z w) 0 0) y := by
        simpa only [area_physical_primitive_base] using (continuousAt_const (y := (0 : ℝ)))
      have hGphysical (s : ℝ) (hs : s ∈ Icc 0 (t y)) :
          ContinuousAt (fun w => areaPhysicalPrimitive k S (z w) 0 s) y := by
        have hs' : s ∈ Icc A B := ⟨hs.1, hs.2.trans hty.2.le⟩
        exact continuousAt_areaPhysicalPrimitive k S ha hs' continuousAt_const
          (Eventually.of_forall fun _ => hs') hbase (hfixed s hs') hfixed hqmeas hqbound
      refine ⟨lowerSemicontinuousAt_variation_moving_interval continuousAt_const
        ht.continuousAt htpos hGphysical hleft hright, ?_⟩
      intro s
      simpa only [areaClampedPrimitive, hki, ite_true] using
        continuousAt_constant_extension_moving_interval continuousAt_const ht.continuousAt
          htpos hGphysical hleft hright s
    constructor
    · change Measurable (fun y : Y => areaSectionVariation k S a δ y)
      simp only [areaSectionVariation, hki, ite_true]
      apply measurable_of_measurable_on_compl_countable E hSc
      apply (lowerSemicontinuous_restrict_iff.mpr ?_).measurable
      intro y hy
      exact ((hstrong y hy).1).lowerSemicontinuousWithinAt _
    · exact ⟨E, hSc, fun y hy s => (hstrong y hy).2 s⟩
/-- The actual four limiting section functionals are Borel measurable.
The proof constructs common physical jump lines and accounts for the
moving endpoints using bounds proved from the smooth sequence. -/
theorem common_section_measurability
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    Measurable (areaSectionVariation k d.rawFields a δ) := by
  obtain ⟨Su, Sv, hSu, hSv, hcu, hcv, hcj⟩ := raw_coefficients_common_continuity h hD d
  obtain ⟨M, _, hM⟩ := area_section_uniform_bound_with_limit h d
    (show 0 < δ / 4 by linarith only [hδ]) (area_section_q_continuous k)
  apply (measurable_area_section_variation d.rawFields k hδ hδa hSu hSv hcu hcv hcj M hM ?_).1
  intro z A B hs
  exact raw_area_algebra_aestronglyMeasurable h d measurableSet_Icc
    ((area_physical_point_continuous k).comp
      (continuous_const.prodMk continuous_id)).continuousOn hs (area_section_q_continuous k)

/-- The actual constant physical extensions have one countable
exceptional set of transverse parameters, independent of the evaluation
point on the extended section. -/
theorem area_clamped_common_exceptional_set
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    ∃ E : Set (Ioo (0 : ℝ) 1), E.Countable ∧ ∀ y ∉ E, ∀ s : ℝ,
      ContinuousAt (fun w => areaClampedPrimitive k d.rawFields a δ w s) y := by
  obtain ⟨Su, Sv, hSu, hSv, hcu, hcv, hcj⟩ := raw_coefficients_common_continuity h hD d
  obtain ⟨M, _, hM⟩ := area_section_uniform_bound_with_limit h d
    (show 0 < δ / 4 by linarith only [hδ]) (area_section_q_continuous k)
  apply (measurable_area_section_variation d.rawFields k hδ hδa hSu hSv hcu hcv hcj M hM ?_).2
  intro z A B hs
  exact raw_area_algebra_aestronglyMeasurable h d measurableSet_Icc
    ((area_physical_point_continuous k).comp
      (continuous_const.prodMk continuous_id)).continuousOn hs (area_section_q_continuous k)

/-- Each of the four smooth section functionals is Borel measurable on
exactly the same triangular parameter carrier as the limiting one. -/
theorem smooth_section_measurability
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    Measurable (areaSectionVariation k S a δ) := by
  have hc := h.area_section_coefficients_continuousOn
  have hcu (u v : ℝ) (hu : 0 < u) (huv : u < v) (_ : u ∉ (∅ : Set ℝ)) :
      ContinuousAt (fun t => areaSectionCoefficients S (t, v)) u := by
    exact (hc.comp (continuous_id.prodMk continuous_const).continuousOn
      (s := Ioo 0 v) (fun t ht => ⟨ht.1.le, ht.2⟩)).continuousAt (Ioo_mem_nhds hu huv)
  have hcv (u v : ℝ) (hu : 0 ≤ u) (huv : u < v) (_ : v ∉ (∅ : Set ℝ)) :
      ContinuousAt (fun t => areaSectionCoefficients S (u, t)) v := by
    exact (hc.comp (continuous_const.prodMk continuous_id).continuousOn
      (s := Ioi u) (fun t ht => ⟨hu, ht⟩)).continuousAt (Ioi_mem_nhds huv)
  have hcj (u v : ℝ) (hu : 0 < u) (huv : u < v)
      (_ : u ∉ (∅ : Set ℝ)) (_ : v ∉ (∅ : Set ℝ)) :
      ContinuousAt (areaSectionCoefficients S) (u, v) := by
    apply hc.continuousAt
    filter_upwards [(continuous_fst.tendsto (u, v)).eventually (Ioi_mem_nhds hu),
      ((continuous_snd.sub continuous_fst).tendsto (u, v)).eventually
        (Ioi_mem_nhds (sub_pos.mpr huv))] with p hp0 hpg
    exact ⟨hp0.le, sub_pos.mp hpg⟩
  obtain ⟨M, hM⟩ := area_section_uniform_bound_of_continuous (fun _ : ℕ => h)
    (show 0 < δ / 4 by linarith only [hδ]) (area_section_q_continuous k)
  apply (measurable_area_section_variation S k hδ hδa countable_empty countable_empty
    hcu hcv hcj M (hM 0) ?_).1
  intro z A B hs
  exact ((area_section_q_continuous k).continuousOn.comp
    (hc.comp ((area_physical_point_continuous k).comp
      (continuous_const.prodMk continuous_id)).continuousOn hs)
    (fun _ _ => mem_univ _)).aestronglyMeasurable measurableSet_Icc

end ChristodoulouBV

end
