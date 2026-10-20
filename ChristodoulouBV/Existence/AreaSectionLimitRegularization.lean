module

public import ChristodoulouBV.Existence.AreaSectionLimitRegularizationCore
import Mathlib.Tactic

/-!
# Applicability of the classical lemmas to the regularized triples

For the equivalent triples `(1,G,0)`, differentiability and derivative
convergence hold everywhere. The original sequence has uniform BV
bounds on each fixed truncation, its extended primitives converge at
every point, and their common transverse exceptional set is proved.
The stronger section-bound form of Lemma 6.2 applies with honest finite
integrals. Exact preservation of variation removes the padding scale.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

attribute [local instance] Measure.Subtype.measureSpace

namespace ChristodoulouBV

/-- Removing the padding after the smooth-index liminf leaves the
pointwise Stieltjes variation unchanged, at every section. -/
theorem area_regularization_remove (k : AreaSectionPair) (S : Fields)
    {a δ : ℝ} (hδ : 0 < δ) (hδa : δ < a) (y : Ioo (0 : ℝ) 1) :
    Tendsto (fun ε => eVariationOn
      (intervalIntegral.productPrimitive (fun _ => (1 : ℝ))
        (areaRegularizedPrimitive k S a δ ε y) (deriv (fun _ => (1 : ℝ))) (fun _ => 0))
          (Icc (0 : ℝ) 1)) (𝓝[>] (0 : ℝ)) (𝓝 (areaSectionVariation k S a δ y)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (area_regularized_stieltjes_variation k S hδ hδa hε y).symm

/-- The padding can also be removed after taking the smooth-index
liminf. Exact variation preservation makes the right-hand bound
independent of the padding scale. -/
theorem area_regularization_liminf_remove (k : AreaSectionPair) (T : ℕ → Fields)
    {a δ : ℝ} (hδ : 0 < δ) (hδa : δ < a) (y : Ioo (0 : ℝ) 1) :
    Tendsto (fun ε => liminf (fun n => eVariationOn
      (intervalIntegral.productPrimitive (fun _ => (1 : ℝ))
        (areaRegularizedPrimitive k (T n) a δ ε y)
        (deriv (fun _ => (1 : ℝ))) (fun _ => 0)) (Icc (0 : ℝ) 1)) atTop)
      (𝓝[>] (0 : ℝ))
      (𝓝 (liminf (fun n => areaSectionVariation k (T n) a δ y) atTop)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (congrArg (fun f : ℕ → ℝ≥0∞ => liminf f atTop)
    (funext fun n => area_regularized_stieltjes_variation k (T n) hδ hδa hε y)).symm

/-- The concrete equivalent triples
`(1,G,0)` have a common countable exceptional set, all-point smooth-index
convergence, uniform BV bounds and measurable section variations.
Applying the classical section and transverse lemmas gives the exact
source liminf bound. Padding removal is `area_regularization_remove`. -/
theorem area_lsc_regularization
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ ε : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) (hε : 0 < ε) :
    ∃ E : Set (Ioo (0 : ℝ) 1), E.Countable ∧
      (∀ y ∉ E, ∀ x : ℝ, ContinuousAt
        (fun z => areaRegularizedPrimitive k d.rawFields a δ ε z x) y) ∧
      (∀ y x, Tendsto
        (fun n => areaRegularizedPrimitive k (T (d.subsequence n)) a δ ε y x) atTop
        (𝓝 (areaRegularizedPrimitive k d.rawFields a δ ε y x))) ∧
      (∃ V : ℝ≥0∞, V ≠ ∞ ∧
        (∀ n y, eVariationOn (areaRegularizedPrimitive k (T (d.subsequence n)) a δ ε y) univ ≤ V) ∧
        ∀ y, eVariationOn (areaRegularizedPrimitive k d.rawFields a δ ε y) univ ≤ V) ∧
      Measurable (areaSectionVariation k d.rawFields a δ) ∧
      (∀ n, Measurable (areaSectionVariation k (T (d.subsequence n)) a δ)) ∧
      (∫⁻ y : Ioo (0 : ℝ) 1, areaSectionVariation k d.rawFields a δ y) ≤
        liminf (fun n => ∫⁻ y : Ioo (0 : ℝ) 1,
          areaSectionVariation k (T (d.subsequence n)) a δ y) atTop := by
  obtain ⟨E, hEc, hE⟩ := area_clamped_common_exceptional_set h hD d k hδ hδa
  let gₙ := fun n => areaRegularizedPrimitive k (T (d.subsequence n)) a δ ε
  let g := areaRegularizedPrimitive k d.rawFields a δ ε
  have hgcont (y : Ioo (0 : ℝ) 1) (hy : y ∉ E) (x : ℝ) :
      ContinuousAt (fun z => g z x) y :=
    (hE y hy ((a + ε) * x)).sub (hE y hy 0)
  have hglim (y : Ioo (0 : ℝ) 1) (x : ℝ) :
      Tendsto (fun n => gₙ n y x) atTop (𝓝 (g y x)) :=
    area_regularized_primitive_limit h d k hδ hδa y x
  obtain ⟨V, hV, hBn, hB⟩ := uniform_area_section_variation_bound_with_limit h hD d k hδ hδa
  have hgₙvar (n : ℕ) (y : Ioo (0 : ℝ) 1) : eVariationOn (gₙ n y) univ ≤ V :=
    (area_regularized_primitive_variation_univ_le k (T (d.subsequence n)) hδ hδa hε y).trans
      (hBn (d.subsequence n) y)
  have hgvar (y : Ioo (0 : ℝ) 1) : eVariationOn (g y) univ ≤ V :=
    (area_regularized_primitive_variation_univ_le k d.rawFields hδ hδa hε y).trans (hB y)
  have hgBV (y : Ioo (0 : ℝ) 1) : BoundedVariationOn (g y) univ :=
    ne_top_of_le_ne_top hV (hgvar y)
  have hgbound (y : Ioo (0 : ℝ) 1) (x : ℝ) : |g y x| ≤ V.toReal := by
    have hd := (hgBV y).dist_le (mem_univ x) (mem_univ 0)
    have hz : g y 0 = 0 := area_regularized_primitive_zero k d.rawFields a δ ε y
    rw [hz, Real.dist_eq, sub_zero] at hd
    exact hd.trans (ENNReal.toReal_mono hV (hgvar y))
  have heq (S : Fields) (y : Ioo (0 : ℝ) 1) :
      eVariationOn (intervalIntegral.productPrimitive (fun _ => (1 : ℝ))
        (areaRegularizedPrimitive k S a δ ε y) (deriv (fun _ => (1 : ℝ))) (fun _ => 0))
          (Icc (0 : ℝ) 1) = areaSectionVariation k S a δ y :=
    area_regularized_stieltjes_variation k S hδ hδa hε y
  have hFnmeas (n : ℕ) : Measurable (fun y : Ioo (0 : ℝ) 1 =>
      eVariationOn (intervalIntegral.productPrimitive (fun _ => (1 : ℝ))
        (gₙ n y) (deriv (fun _ => (1 : ℝ))) (fun _ => 0)) (Icc (0 : ℝ) 1)) := by
    simpa only [gₙ, heq] using smooth_section_measurability (h (d.subsequence n)) k hδ hδa
  have hFnfinite (n : ℕ) : (∫⁻ y : Ioo (0 : ℝ) 1,
      eVariationOn (intervalIntegral.productPrimitive (fun _ => (1 : ℝ))
        (gₙ n y) (deriv (fun _ => (1 : ℝ))) (fun _ => 0)) (Icc (0 : ℝ) 1)) ≠ ∞ := by
    simpa only [gₙ, heq] using (area_section_integrals_finite h hD d k hδ hδa).1 (d.subsequence n)
  have hlemma := lemma6_2_of_uniform_section_ae_bounds
    (fₙ := fun _ _ _ => (1 : ℝ)) (gₙ := gₙ) (hₙ := fun _ _ _ => (0 : ℝ))
    (f := fun _ _ => (1 : ℝ)) (g := g) (h := fun _ _ => (0 : ℝ))
    (S := E) (hS := hEc)
    (hfₙ_diff := by intros; fun_prop)
    (hf_diff := by intros; fun_prop)
    (hf_lim := by intros; exact tendsto_const_nhds)
    (hf_deriv_lim := by intros; simp only [deriv_const]; exact tendsto_const_nhds)
    (hf_deriv_bound := fun _ => ⟨0, le_rfl, fun _ => Eventually.of_forall
      (fun _ _ => by simp only [deriv_const, abs_zero, le_refl])⟩)
    (hg_var := fun y => ⟨V, hV, fun n =>
      (eVariationOn.mono (gₙ n y) (subset_univ _)).trans (hgₙvar n y)⟩)
    (hg_lim := fun y x _ => hglim y x)
    (hhₙ_meas := fun _ _ => measurable_const)
    (hhₙ_bound := fun _ => ⟨0, le_rfl, fun _ => Eventually.of_forall
      (fun _ _ => by simp only [abs_zero, le_refl])⟩)
    (hh_lim := by intros; exact tendsto_const_nhds)
    (hFₙ_meas := hFnmeas) (_hFₙ_integrable := hFnfinite)
    (_hf_bound := ⟨1, zero_le_one, fun _ => Eventually.of_forall
      (fun _ _ => by simp only [abs_one, le_refl])⟩)
    (hf_deriv_bound_lim := ⟨0, le_rfl, fun _ => Eventually.of_forall
      (fun _ _ => by simp only [deriv_const, abs_zero, le_refl])⟩)
    (hg_bound := ⟨V.toReal, ENNReal.toReal_nonneg, fun y => Eventually.of_forall
      (fun x _ => hgbound y x)⟩)
    (hh_bound := ⟨0, le_rfl, fun _ => Eventually.of_forall
      (fun _ _ => by simp only [abs_zero, le_refl])⟩)
    (hh_meas := fun _ => measurable_const)
    (hf_cont := by intros; exact continuousAt_const)
    (hf_deriv_cont := by intros; simp only [deriv_const]; exact continuousAt_const)
    (hg_cont := fun y hy x _ => hgcont y hy x)
    (hh_cont := by intros; exact continuousAt_const)
  refine ⟨E, hEc, hgcont, hglim, ⟨V, hV, hgₙvar, hgvar⟩,
    common_section_measurability h hD d k hδ hδa,
    fun n => smooth_section_measurability (h (d.subsequence n)) k hδ hδa, ?_⟩
  simpa only [gₙ, g, heq] using hlemma.2

end ChristodoulouBV

end
