module

public import ChristodoulouBV.Existence.AreaSectionLimitVariation
public import ChristodoulouBV.Existence.AreaSectionLimitMeasurable
public import ChristodoulouBV.Existence.AreaSectionLimitPhysical
import Mathlib.Tactic

/-!
# Finite integrals on each fixed off-axis truncation

These local bounds can depend on the cutoff and the positive distance
from the axis. The global universal area bounds are a separate limit
argument. Measurability is proved for both the original smooth sequence
and the actual raw limit before applying Fatou.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

attribute [local instance] Measure.Subtype.measureSpace

namespace ChristodoulouBV

private instance areaSectionFiniteVolume : IsFiniteMeasure (volume : Measure (Ioo (0 : ℝ) 1)) where
  measure_univ_lt_top := by
    rw [Measure.Subtype.volume_univ nullMeasurableSet_Ioo]
    norm_num

/-- The four smooth section variations have a bound uniform in the
smooth index and transverse parameter on each fixed off-axis truncation. -/
theorem uniform_area_section_variation_bound
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (k : AreaSectionPair) {a δ : ℝ} (hδ : 0 < δ) (hδa : δ < a) :
    ∃ V : ℝ≥0∞, V ≠ ∞ ∧ ∀ n y, areaSectionVariation k (T n) a δ y ≤ V := by
  obtain ⟨hfc, hgc, hpc, _⟩ := area_section_formulas_continuous k
  obtain ⟨F, hF⟩ := area_section_uniform_bound_of_continuous h hδ hfc
  obtain ⟨G, hG⟩ := area_section_uniform_bound_of_continuous h hδ hgc
  obtain ⟨P, hP⟩ := area_section_uniform_bound_of_continuous h hδ hpc
  obtain ⟨Q, hQ⟩ := area_section_uniform_bound_of_continuous h hδ (area_section_q_continuous k)
  let V := ENNReal.ofReal F * areaSectionFieldVariationBound D C +
    ENNReal.ofReal G * ENNReal.ofReal (|P| * a) + ENNReal.ofReal (|Q| * a)
  have hV : V ≠ ∞ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (area_section_field_variation_bound_ne_top hD C),
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩,
      ENNReal.ofReal_ne_top⟩
  have hbudget (n : ℕ) (z b A B : ℝ) (hab : A ≤ B) (hb : b ∈ Icc A B)
      (hs : MapsTo (areaPhysicalPoint k z) (Icc A B) globalDomain)
      (hgap : ∀ t ∈ Icc A B,
        δ ≤ (areaPhysicalPoint k z t).2 - (areaPhysicalPoint k z t).1)
      (hlen : B - A ≤ a) :
      eVariationOn (areaPhysicalPrimitive k (T n) z b) (Icc A B) ≤ V := by
    have hbvar := (h n).area_physical_primitive_variation_bound k hab hb hs
      (fun t ht => hF n _ (hs ht) (hgap t ht))
      (fun t ht => hG n _ (hs ht) (hgap t ht))
      (fun t ht => (hP n _ (hs ht) (hgap t ht)).trans (le_abs_self P))
      (fun t ht => (hQ n _ (hs ht) (hgap t ht)).trans (le_abs_self Q))
    apply hbvar.trans
    exact add_le_add
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hlen (abs_nonneg P))) bot_le))
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hlen (abs_nonneg Q)))
  refine ⟨V, hV, fun n y => ?_⟩
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
    apply hbudget n w a (δ + w) a hwa.le ⟨hwa.le, le_rfl⟩
    · intro t ht
      simp only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false]
      exact ⟨hw.le, by linarith only [ht.1, hδ]⟩
    · intro t ht
      simp only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false]
      linarith only [ht.1]
    · linarith only [hw, hδ]
  | true =>
    simp only [areaSectionVariation, hki, ite_true]
    apply hbudget n (δ + w) 0 0 w hw.le ⟨le_rfl, hw.le⟩
    · intro t ht
      simp only [areaPhysicalPoint, hki, ite_true]
      exact ⟨ht.1, by linarith only [ht.2, hδ]⟩
    · intro t ht
      simp only [areaPhysicalPoint, hki, ite_true]
      linarith only [ht.2]
    · linarith only [hwa, hδ]

/-- The same local bound controls every original smooth section and
every actual limiting section on the shared subsequence. -/
theorem uniform_area_section_variation_bound_with_limit
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    ∃ V : ℝ≥0∞, V ≠ ∞ ∧
      (∀ n y, areaSectionVariation k (T n) a δ y ≤ V) ∧
      ∀ y, areaSectionVariation k d.rawFields a δ y ≤ V := by
  obtain ⟨V, hV, hb⟩ := uniform_area_section_variation_bound h hD k hδ hδa
  refine ⟨V, hV, hb, fun y => (lemma61_applicability h d k hδ hδa y).trans ?_⟩
  have hlim := liminf_le_liminf (f := atTop)
    (Eventually.of_forall fun n => hb (d.subsequence n) y)
  simpa only [liminf_const] using hlim

/-- All section integrals on a fixed truncation are finite, for the
original smooth sequence and for its actual raw limit. -/
theorem area_section_integrals_finite
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    (∀ n, (∫⁻ y : Ioo (0 : ℝ) 1, areaSectionVariation k (T n) a δ y) ≠ ∞) ∧
      (∫⁻ y : Ioo (0 : ℝ) 1, areaSectionVariation k d.rawFields a δ y) ≠ ∞ := by
  obtain ⟨V, hV, hb, hlim⟩ := uniform_area_section_variation_bound_with_limit h hD d k hδ hδa
  have hc := (lintegral_const_lt_top (μ := (volume : Measure (Ioo (0 : ℝ) 1)))) hV
  exact ⟨fun n => ne_top_of_le_ne_top hc.ne (lintegral_mono (hb n)),
    ne_top_of_le_ne_top hc.ne (lintegral_mono hlim)⟩

/-- The Fatou inequality for the concrete section functionals, following
the author ruling on the lower-integral reading of Lemma 6.2.
For finite datum variation, the separate measurability theorems identify
both sides as integrals of measurable functions. -/
theorem area_section_lintegral_le_liminf
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n))
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    (∫⁻ y : Ioo (0 : ℝ) 1, areaSectionVariation k d.rawFields a δ y) ≤
      liminf (fun n => ∫⁻ y : Ioo (0 : ℝ) 1,
        areaSectionVariation k (T (d.subsequence n)) a δ y) atTop :=
  lemma6_2_lintegral_le_liminf_of_pointwise
    (fun y => lemma61_applicability h d k hδ hδa y)
    (fun n => (smooth_section_measurability (h (d.subsequence n)) k hδ hδa).aemeasurable)

end ChristodoulouBV

end
