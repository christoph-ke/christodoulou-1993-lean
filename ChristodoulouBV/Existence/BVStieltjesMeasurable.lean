module

public import ChristodoulouBV.Existence.BVStieltjesCalculus
import Mathlib.Tactic

/-!
# Measurability and local domination for canonical area coefficients

The simultaneous spatial translation in the transport limit construction gives a pointwise limit
of measurable raw coefficient kernels on arbitrary finite rectangles.
It preserves the distance from the axis, hence the existing local
majorants apply throughout this limit.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The nine translated raw area coefficients converge to the canonical
coefficients at every domain point. -/
theorem bv_area_coefficients_shift_limit
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {p : ℝ × ℝ} (hp : p ∈ globalDomain) :
    Tendsto (fun n => areaSectionCoefficients (transportShiftFields d.rawFields n) p)
      atTop (𝓝 (areaSectionCoefficients d.scalarRightFields p)) := by
  obtain ⟨hr, hφ, hm, hl, hn, hα, hβ⟩ := transport_shift_fields_limit h hD d hp
  have hg := scalar_right_fields_geometry h hD d p hp
  have hl0 : d.scalarRightFields.lam p.1 p.2 ≠ 0 := by linarith only [hg.1]
  have hn0 : d.scalarRightFields.nu p.1 p.2 ≠ 0 := by linarith only [hg.2.2.1]
  rw [tendsto_pi_nhds]
  intro i
  fin_cases i
  · exact hr.inv₀ (d.radius_pos h hp).ne'
  · exact hl
  · exact hn
  · exact hφ
  · exact hα
  · exact hβ
  · exact transport_shift_radius_coeff_limit h hD d hp
  · exact hl.inv₀ hl0
  · exact hn.inv₀ hn0

private theorem raw_algebra_aestronglyMeasurable
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {μ : Measure Y} {E : Set Y} (hE : MeasurableSet E) {c : Y → ℝ × ℝ}
    (hc : ContinuousOn c E) (hs : MapsTo c E globalDomain)
    {q : (Fin 9 → ℝ) → ℝ} (hq : Continuous q) :
    AEStronglyMeasurable (fun y => q (areaSectionCoefficients d.rawFields (c y)))
      (μ.restrict E) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n y => q (areaSectionCoefficients (T (d.subsequence n)) (c y)))
  · intro n
    exact (hq.continuousOn.comp
      ((h (d.subsequence n)).area_section_coefficients_continuousOn.comp hc hs)
      (fun _ _ => mem_univ _)).aestronglyMeasurable hE
  · filter_upwards [ae_restrict_mem hE] with y hy
    exact (hq.tendsto _).comp (d.area_section_coefficients_limit h (hs hy))

/-- Continuous algebraic expressions in the canonical coefficients are
strongly measurable almost everywhere on any continuously parametrized
measurable part of the carrier, including two-dimensional rectangles. -/
theorem bv_area_algebra_aestronglyMeasurable
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T)
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {μ : Measure Y} {E : Set Y} (hE : MeasurableSet E) {c : Y → ℝ × ℝ}
    (hc : ContinuousOn c E) (hs : MapsTo c E globalDomain)
    {q : (Fin 9 → ℝ) → ℝ} (hq : Continuous q) :
    AEStronglyMeasurable (fun y => q (areaSectionCoefficients d.scalarRightFields (c y)))
      (μ.restrict E) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n y => q (areaSectionCoefficients (transportShiftFields d.rawFields n) (c y)))
  · intro n
    have he : (fun y => q (areaSectionCoefficients (transportShiftFields d.rawFields n)
        (c y))) = fun y => q (areaSectionCoefficients d.rawFields
          ((c y).1 + transportStep n, (c y).2 + transportStep n)) := rfl
    rw [he]
    exact raw_algebra_aestronglyMeasurable h d hE
      ((hc.fst.add continuousOn_const).prodMk (hc.snd.add continuousOn_const))
      (fun _ hy => transport_shift_mem (hs hy) n) hq
  · filter_upwards [ae_restrict_mem hE] with y hy
    exact (hq.tendsto _).comp (bv_area_coefficients_shift_limit h hD d (hs hy))

/-- The raw off-axis algebraic majorants also bound the canonical
coefficients. The bound depends only on the existing local parameters. -/
theorem bv_area_algebra_uniform_bound
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {δ : ℝ} (hδ : 0 < δ)
    {q : (Fin 9 → ℝ) → ℝ} (hq : Continuous q) :
    ∃ M : ℝ, ∀ p ∈ globalDomain, δ ≤ p.2 - p.1 →
      |q (areaSectionCoefficients d.scalarRightFields p)| ≤ M := by
  obtain ⟨M, _, hM⟩ := area_section_uniform_bound_with_limit h d hδ hq
  refine ⟨M, fun p hp hgap => ?_⟩
  apply le_of_tendsto ((hq.tendsto _).comp
    (bv_area_coefficients_shift_limit h hD d hp)).abs
  apply Eventually.of_forall
  intro n
  exact hM _ (transport_shift_mem hp n)
    (by simpa only [add_sub_add_right_eq_sub] using hgap)

/-- Every canonical area correction is interval-integrable on an
admissible compact physical section. -/
theorem bv_area_algebra_intervalIntegrable
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {z A B δ : ℝ}
    (hab : A ≤ B) (hδ : 0 < δ)
    (hs : MapsTo (areaPhysicalPoint k z) (Icc A B) globalDomain)
    (hgap : ∀ t ∈ Icc A B,
      δ ≤ (areaPhysicalPoint k z t).2 - (areaPhysicalPoint k z t).1)
    {q : (Fin 9 → ℝ) → ℝ} (hq : Continuous q) :
    IntervalIntegrable
      (fun t => q (areaSectionCoefficients d.scalarRightFields (areaPhysicalPoint k z t)))
      volume A B := by
  have hm := bv_area_algebra_aestronglyMeasurable h hD d (μ := volume) measurableSet_Icc
    ((area_physical_point_continuous k).comp
      (continuous_const.prodMk continuous_id)).continuousOn hs hq
  obtain ⟨M, hM⟩ := bv_area_algebra_uniform_bound h hD d hδ hq
  apply (intervalIntegrable_const (a := A) (b := B) (c := M)).mono_fun'
    (hm.mono_set (by rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self))
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  have ht' : t ∈ Icc A B := by
    rw [uIoc_of_le hab] at ht
    exact Ioc_subset_Icc_self ht
  simpa only [Real.norm_eq_abs, Function.comp_def, id_eq] using hM _ (hs ht') (hgap t ht')

/-- The canonical correction is jointly integrable on every compact
off-axis rectangle. This supplies Fubini's actual hypothesis. -/
theorem bv_area_algebra_integrable_rectangle
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {Z W A B δ : ℝ}
    (hδ : 0 < δ)
    (hs : MapsTo (fun p : ℝ × ℝ => areaPhysicalPoint k p.1 p.2)
      (Icc Z W ×ˢ Icc A B) globalDomain)
    (hgap : ∀ p ∈ Icc Z W ×ˢ Icc A B,
      δ ≤ (areaPhysicalPoint k p.1 p.2).2 - (areaPhysicalPoint k p.1 p.2).1)
    {q : (Fin 9 → ℝ) → ℝ} (hq : Continuous q) :
    Integrable (fun p : ℝ × ℝ =>
      q (areaSectionCoefficients d.scalarRightFields (areaPhysicalPoint k p.1 p.2)))
      ((volume.restrict (Ioc Z W)).prod (volume.restrict (Ioc A B))) := by
  let E := Ioc Z W ×ˢ Ioc A B
  have hE : MeasurableSet E := measurableSet_Ioc.prod measurableSet_Ioc
  have hsub : E ⊆ Icc Z W ×ˢ Icc A B :=
    Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have hm := bv_area_algebra_aestronglyMeasurable h hD d
    (μ := (volume : Measure ℝ).prod volume) hE
    (area_physical_point_continuous k).continuousOn (fun p hp => hs (hsub hp)) hq
  rw [← Measure.prod_restrict] at hm
  obtain ⟨M, hM⟩ := bv_area_algebra_uniform_bound h hD d hδ hq
  apply (integrable_const M).mono' hm
  have hmem : ∀ᵐ p : ℝ × ℝ
      ∂((volume.restrict (Ioc Z W)).prod (volume.restrict (Ioc A B))), p ∈ E := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem hE
  filter_upwards [hmem] with p hp
  simpa only [Real.norm_eq_abs] using hM _ (hs (hsub hp)) (hgap p (hsub hp))

end ChristodoulouBV

end
