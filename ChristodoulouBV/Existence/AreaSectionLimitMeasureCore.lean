module

public import ChristodoulouBV.Existence.AreaSectionLimitBounds
public import ChristodoulouBV.Existence.AreaSectionLimitJoint
public import ChristodoulouBV.Existence.AreaSectionLimitMoving
import Mathlib.Tactic

/-!
# Measurable section kernels and variable-endpoint integrals

These tools retain the actual raw representatives. Every algebraic
kernel is a pointwise limit of the original smooth sequence, hence is
measurable on compact sections. Uniform coefficient bounds also control
the change in an integral when an endpoint moves.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Every continuous algebraic expression in the raw coefficients is
strongly measurable almost everywhere on any measurable, continuously
parametrized section of the global carrier. -/
theorem raw_area_algebra_aestronglyMeasurable
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    {s : Set ℝ} (hs : MeasurableSet s) {c : ℝ → ℝ × ℝ}
    (hc : ContinuousOn c s) (hcs : MapsTo c s globalDomain)
    {q : (Fin 9 → ℝ) → ℝ} (hq : Continuous q) :
    AEStronglyMeasurable (fun t => q (areaSectionCoefficients d.rawFields (c t)))
      (volume.restrict s) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n t => q (areaSectionCoefficients (T (d.subsequence n)) (c t)))
  · intro n
    exact (hq.continuousOn.comp
      ((h (d.subsequence n)).area_section_coefficients_continuousOn.comp hc hcs)
      (fun _ _ => mem_univ _)).aestronglyMeasurable hs
  · filter_upwards [ae_restrict_mem hs] with t ht
    exact (hq.tendsto _).comp (d.area_section_coefficients_limit h (hcs ht))

/-- The same off-axis majorant controls the raw limit algebraic kernel
and every original smooth kernel. -/
theorem area_section_uniform_bound_with_limit
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    {δ : ℝ} (hδ : 0 < δ) {q : (Fin 9 → ℝ) → ℝ} (hq : Continuous q) :
    ∃ M : ℝ,
      (∀ n p, p ∈ globalDomain → δ ≤ p.2 - p.1 →
        |q (areaSectionCoefficients (T n) p)| ≤ M) ∧
      ∀ p, p ∈ globalDomain → δ ≤ p.2 - p.1 →
        |q (areaSectionCoefficients d.rawFields p)| ≤ M := by
  obtain ⟨M, hM⟩ := area_section_uniform_bound_of_continuous h hδ hq
  refine ⟨M, hM, fun p hp hgap => ?_⟩
  exact le_of_tendsto ((hq.tendsto _).comp (d.area_section_coefficients_limit h hp)).abs
    (Eventually.of_forall fun n => hM (d.subsequence n) p hp hgap)

/-- Continuity of a bounded section integral with a moving upper
endpoint. The bound holds in a neighborhood of the parameter on every
section, and does not merely hold almost everywhere on a rectangle. -/
theorem continuousAt_intervalIntegral_variable_upper
    {Y : Type*} [TopologicalSpace Y] [FirstCountableTopology Y]
    {q : Y → ℝ → ℝ} {t : Y → ℝ} {y : Y} {a A B M : ℝ}
    (ha : a ∈ Icc A B) (ht : t y ∈ Icc A B) (htc : ContinuousAt t y)
    (ht_near : ∀ᶠ z in 𝓝 y, t z ∈ Icc A B)
    (hq_meas : ∀ᶠ z in 𝓝 y, AEStronglyMeasurable (q z) (volume.restrict (Icc A B)))
    (hq_bound : ∀ᶠ z in 𝓝 y, ∀ s ∈ Icc A B, |q z s| ≤ M)
    (hq_cont : ∀ s ∈ Icc A B, ContinuousAt (fun z => q z s) y) :
    ContinuousAt (fun z => ∫ s in a..t z, q z s) y := by
  have hsub : uIoc a (t y) ⊆ Icc A B :=
    uIoc_subset_uIcc.trans (uIcc_subset_Icc ha ht)
  have hfixed : Tendsto (fun z => ∫ s in a..t y, q z s) (𝓝 y)
      (𝓝 (∫ s in a..t y, q y s)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (bound := fun _ => M)
    · exact hq_meas.mono fun z hz => hz.mono_set hsub
    · filter_upwards [hq_bound] with z hz
      exact Eventually.of_forall fun s hs => by
        simpa only [Real.norm_eq_abs] using hz s (hsub hs)
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun s hs => hq_cont s (hsub hs)
  have herror : ∀ᶠ z in 𝓝 y,
      dist (∫ s in a..t z, q z s) (∫ s in a..t y, q z s) ≤
        |M| * dist (t z) (t y) := by
    filter_upwards [ht_near, hq_meas, hq_bound] with z hzt hzm hzb
    have hint (b c : ℝ) (hb : b ∈ Icc A B) (hc : c ∈ Icc A B) :
        IntervalIntegrable (q z) volume b c := by
      apply (intervalIntegrable_const (a := b) (b := c) (c := M)).mono_fun'
        (hzm.mono_set (uIoc_subset_uIcc.trans (uIcc_subset_Icc hb hc)))
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      simpa only [Real.norm_eq_abs] using hzb s
        ((uIoc_subset_uIcc.trans (uIcc_subset_Icc hb hc)) hs)
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint a (t y) ha ht)
      (hint (t y) (t z) ht hzt), Real.dist_eq, add_sub_cancel_left]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t y) (b := t z) (f := q z) (C := |M|) (fun s hs => by
        rw [Real.norm_eq_abs]
        exact (hzb s ((uIoc_subset_uIcc.trans (uIcc_subset_Icc ht hzt)) hs)).trans
          (le_abs_self M))
    simpa only [Real.norm_eq_abs, Real.dist_eq, abs_sub_comm] using hb
  have hdist : Tendsto
      (fun z => dist (∫ s in a..t z, q z s) (∫ s in a..t y, q z s)) (𝓝 y) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) herror
    have ht' : Tendsto (fun z => dist (t z) (t y)) (𝓝 y) (𝓝 0) := by
      simpa only [dist_self] using htc.dist (tendsto_const_nhds (x := t y))
    simpa only [mul_zero] using (tendsto_const_nhds (x := |M|)).mul ht'
  exact hfixed.congr_dist (by simpa only [dist_comm] using hdist)

/-- Physical null-section coordinates, before normalization to `[0,1]`. -/
@[expose] def areaPhysicalPoint (k : AreaSectionPair) (z t : ℝ) : ℝ × ℝ :=
  if k.incoming then (t, z) else (z, t)

/-- Physical section coordinates depend continuously on both inputs. -/
theorem area_physical_point_continuous (k : AreaSectionPair) :
    Continuous (fun p : ℝ × ℝ => areaPhysicalPoint k p.1 p.2) := by
  cases k <;> simp only [areaPhysicalPoint, AreaSectionPair.incoming,
    Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

/-- The ordinary-integral kernel in the physical Stieltjes primitive. -/
@[expose] def areaSectionQ (k : AreaSectionPair) (c : Fin 9 → ℝ) : ℝ :=
  areaSectionG k c * areaSectionP c + areaSectionH k c

/-- The ordinary-integral kernel is a continuous algebraic expression. -/
theorem area_section_q_continuous (k : AreaSectionPair) : Continuous (areaSectionQ k) :=
  ((area_section_formulas_continuous k).2.1.mul
    (area_section_formulas_continuous k).2.2.1).add
      (area_section_formulas_continuous k).2.2.2

/-- The pointwise Stieltjes primitive anchored at a fixed physical
coordinate. Its variation is independent of the anchoring constant. -/
@[expose] noncomputable def areaPhysicalPrimitive (k : AreaSectionPair)
    (S : Fields) (z b t : ℝ) : ℝ :=
  let c := fun s => areaSectionCoefficients S (areaPhysicalPoint k z s)
  areaSectionF k (c t) * areaSectionG k (c t) -
    areaSectionF k (c b) * areaSectionG k (c b) -
      ∫ s in b..t, areaSectionG k (c s) * areaSectionP (c s) + areaSectionH k (c s)

/-- The source's physical primitive vanishes at its basepoint. -/
theorem area_physical_primitive_base (k : AreaSectionPair) (S : Fields) (z b : ℝ) :
    areaPhysicalPrimitive k S z b b = 0 := by
  simp only [areaPhysicalPrimitive, intervalIntegral.integral_same, sub_self]

/-- Continuous endpoint coefficients, uniformly bounded measurable
section kernels, and fixed-section coefficient continuity give
continuity of the physical primitive with a moving endpoint. -/
theorem continuousAt_areaPhysicalPrimitive
    {Y : Type*} [TopologicalSpace Y] [FirstCountableTopology Y]
    (k : AreaSectionPair) (S : Fields) {z t : Y → ℝ} {y : Y} {a A B M : ℝ}
    (ha : a ∈ Icc A B) (ht : t y ∈ Icc A B) (htc : ContinuousAt t y)
    (ht_near : ∀ᶠ w in 𝓝 y, t w ∈ Icc A B)
    (hc_base : ContinuousAt
      (fun w => areaSectionCoefficients S (areaPhysicalPoint k (z w) a)) y)
    (hc_end : ContinuousAt
      (fun w => areaSectionCoefficients S (areaPhysicalPoint k (z w) (t w))) y)
    (hc_fixed : ∀ s ∈ Icc A B, ContinuousAt
      (fun w => areaSectionCoefficients S (areaPhysicalPoint k (z w) s)) y)
    (hq_meas : ∀ᶠ w in 𝓝 y, AEStronglyMeasurable
      (fun s => areaSectionQ k (areaSectionCoefficients S (areaPhysicalPoint k (z w) s)))
        (volume.restrict (Icc A B)))
    (hq_bound : ∀ᶠ w in 𝓝 y, ∀ s ∈ Icc A B,
      |areaSectionQ k (areaSectionCoefficients S (areaPhysicalPoint k (z w) s))| ≤ M) :
    ContinuousAt (fun w => areaPhysicalPrimitive k S (z w) a (t w)) y := by
  have hi := continuousAt_intervalIntegral_variable_upper ha ht htc ht_near
    hq_meas hq_bound (fun s hs => (area_section_q_continuous k).continuousAt.comp
      (hc_fixed s hs))
  obtain ⟨hf, hg, _, _⟩ := area_section_formulas_continuous k
  exact (((hf.continuousAt.comp hc_end).mul (hg.continuousAt.comp hc_end)).sub
    ((hf.continuousAt.comp hc_base).mul (hg.continuousAt.comp hc_base))).sub hi

/-- The four area section functionals in the two triangular charts.
The signed inner coordinate derivative is absorbed by the physical
change of variable. The outer factor is `a-δ`. -/
@[expose] noncomputable def areaSectionVariation (k : AreaSectionPair)
    (S : Fields) (a δ : ℝ) (y : Ioo (0 : ℝ) 1) : ℝ≥0∞ :=
  if k.incoming then
    eVariationOn (areaPhysicalPrimitive k S (δ + (a - δ) * y) 0)
      (Icc 0 ((a - δ) * y))
  else
    eVariationOn (areaPhysicalPrimitive k S ((a - δ) * y) a)
      (Icc (δ + (a - δ) * y) a)

/-- Constant physical extension of the area primitive to the entire
line. The extension retains the exact values at both section endpoints. -/
@[expose] noncomputable def areaClampedPrimitive (k : AreaSectionPair)
    (S : Fields) (a δ : ℝ) (y : Ioo (0 : ℝ) 1) (t : ℝ) : ℝ :=
  if k.incoming then
    areaPhysicalPrimitive k S (δ + (a - δ) * y) 0 (max 0 (min ((a - δ) * y) t))
  else
    areaPhysicalPrimitive k S ((a - δ) * y) a (max (δ + (a - δ) * y) (min a t))

end ChristodoulouBV

end
