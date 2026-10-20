module

public import ChristodoulouBV.Existence.AreaSectionLimitBounds
import Mathlib.Tactic

/-!
# Convergence of the four concrete area primitives

Pointwise convergence of the nine algebraic coefficients and their
uniform off-axis bounds give dominated convergence of every initial
segment integral. The variation inequality retains every raw jump value
and uses the shared existence subsequence.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Each of the four concrete area primitives converges at every point
of an admissible affine null section. The coefficient majorant is proved
from the smooth approximation bounds, rather than supplied as a new premise. -/
theorem area_section_primitive_limit
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    (k : AreaSectionPair) (z a b : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hs : MapsTo (areaNullSection k z a b) (Icc (0 : ℝ) 1) globalDomain)
    (hgap : ∀ x ∈ Icc (0 : ℝ) 1,
      δ ≤ (areaNullSection k z a b x).2 - (areaNullSection k z a b x).1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => areaSectionPrimitive k (T (d.subsequence n)) z a b x)
      atTop (𝓝 (areaSectionPrimitive k d.rawFields z a b x)) := by
  let c : ℕ → ℝ → Fin 9 → ℝ :=
    fun n t => areaSectionCoefficients (T (d.subsequence n)) (areaNullSection k z a b t)
  let c₀ : ℝ → Fin 9 → ℝ :=
    fun t => areaSectionCoefficients d.rawFields (areaNullSection k z a b t)
  have hclim (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Tendsto (fun n => c n t) atTop (𝓝 (c₀ t)) :=
    d.area_section_coefficients_limit h (hs ht)
  obtain ⟨hf, hg, hp, hh⟩ := area_section_formulas_continuous k
  let q : (Fin 9 → ℝ) → ℝ := fun v =>
    areaSectionG k v * ((b - a) * areaSectionP v) + (b - a) * areaSectionH k v
  have hq : Continuous q :=
    (hg.mul (continuous_const.mul hp)).add (continuous_const.mul hh)
  obtain ⟨M, hM⟩ := area_section_uniform_bound_of_continuous h hδ hq
  have hqcont (n : ℕ) : ContinuousOn (fun t => q (c n t)) (Icc (0 : ℝ) 1) :=
    hq.continuousOn.comp
      ((h (d.subsequence n)).area_section_coefficients_continuousOn.comp
        (area_null_section_continuous k z a b).continuousOn hs)
      (fun _ _ => mem_univ _)
  have hi : Tendsto (fun n => ∫ t in (0 : ℝ)..x, q (c n t)) atTop
      (𝓝 (∫ t in (0 : ℝ)..x, q (c₀ t))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (bound := fun _ => M)
    · refine Eventually.of_forall fun n =>
        ((hqcont n).aestronglyMeasurable measurableSet_Icc).mono_set ?_
      rw [uIoc_of_le hx.1]
      exact Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hx.2)
    · refine Eventually.of_forall fun n => Eventually.of_forall fun t ht => ?_
      have ht' : t ∈ Icc (0 : ℝ) 1 := by
        rw [uIoc_of_le hx.1] at ht
        exact ⟨ht.1.le, ht.2.trans hx.2⟩
      simpa only [Real.norm_eq_abs] using hM (d.subsequence n) _ (hs ht') (hgap t ht')
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun t ht => ?_
      have ht' : t ∈ Icc (0 : ℝ) 1 := by
        rw [uIoc_of_le hx.1] at ht
        exact ⟨ht.1.le, ht.2.trans hx.2⟩
      exact (hq.tendsto (c₀ t)).comp (hclim t ht')
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  exact (((((hf.tendsto (c₀ x)).comp (hclim x hx)).mul
    ((hg.tendsto (c₀ x)).comp (hclim x hx))).sub
    (((hf.tendsto (c₀ 0)).comp (hclim 0 hzero)).mul
      ((hg.tendsto (c₀ 0)).comp (hclim 0 hzero)))).sub hi)

/-- Lower semicontinuity of the concrete algebraic area primitives on
every admissible truncated null section. No all-point convergence to a
canonical right trace is used. -/
theorem area_section_variation_le_liminf
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    (k : AreaSectionPair) (z a b : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hs : MapsTo (areaNullSection k z a b) (Icc (0 : ℝ) 1) globalDomain)
    (hgap : ∀ x ∈ Icc (0 : ℝ) 1,
      δ ≤ (areaNullSection k z a b x).2 - (areaNullSection k z a b x).1) :
    eVariationOn (areaSectionPrimitive k d.rawFields z a b) (Icc (0 : ℝ) 1) ≤
      liminf (fun n => eVariationOn
        (areaSectionPrimitive k (T (d.subsequence n)) z a b) (Icc (0 : ℝ) 1)) atTop :=
  eVariationOn.le_liminf_of_tendsto_pointwise fun _ hx =>
    area_section_primitive_limit h d k z a b hδ hs hgap hx

end ChristodoulouBV

end
