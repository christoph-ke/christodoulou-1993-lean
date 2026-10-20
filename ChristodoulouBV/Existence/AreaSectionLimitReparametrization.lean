module

public import ChristodoulouBV.Existence.AreaSectionLimitMeasurable
public import ChristodoulouBV.Existence.AreaSectionLimitPhysical
public import ChristodoulouBV.Existence.AreaSectionLimitFinite
import Mathlib.Tactic

/-!
# The signed inner coordinate factors in the area charts

Affine substitution identifies the physical primitive with the unit
section primitive containing both factors `b-a`. This includes the
orientation-reversing outgoing chart. Thus the measurability results
apply literally to the corrected weighted section functionals.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

attribute [local instance] Measure.Subtype.measureSpace

namespace ChristodoulouBV

/-- Affine substitution in the pointwise primitive inserts the signed
inner coordinate derivative into both density terms. -/
theorem area_section_primitive_eq_physical (k : AreaSectionPair) (S : Fields)
    (z A B x : ℝ) :
    areaSectionPrimitive k S z A B x =
      areaPhysicalPrimitive k S z A (A + (B - A) * x) := by
  let c := fun t => areaSectionCoefficients S (areaPhysicalPoint k z t)
  have hpoint (t : ℝ) : areaNullSection k z A B t =
      areaPhysicalPoint k z (A + (B - A) * t) := by
    rfl
  have hi : (∫ t in (0 : ℝ)..x,
      areaSectionG k (c (A + (B - A) * t)) *
        ((B - A) * areaSectionP (c (A + (B - A) * t))) +
        (B - A) * areaSectionH k (c (A + (B - A) * t))) =
      ∫ t in A..(A + (B - A) * x), areaSectionQ k (c t) := by
    calc
      _ = ∫ t in (0 : ℝ)..x, (B - A) * areaSectionQ k (c (A + (B - A) * t)) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only [areaSectionQ]
        ring
      _ = (B - A) * ∫ t in (0 : ℝ)..x, areaSectionQ k (c (A + (B - A) * t)) :=
        intervalIntegral.integral_const_mul _ _
      _ = _ := by
        simpa only [smul_eq_mul, mul_zero, add_zero] using
          intervalIntegral.smul_integral_comp_add_mul
            (fun t => areaSectionQ k (c t)) (B - A) A (a := 0) (b := x)
  simp only [areaSectionPrimitive, intervalIntegral.productPrimitive,
    areaPhysicalPrimitive, hpoint, mul_zero, add_zero]
  exact congrArg (fun v => areaSectionF k (c (A + (B - A) * x)) *
      areaSectionG k (c (A + (B - A) * x)) -
        areaSectionF k (c A) * areaSectionG k (c A) - v) hi

/-- The signed affine parametrization preserves pointwise variation on
the whole closed section, in either orientation. -/
theorem area_section_variation_eq_physical (k : AreaSectionPair) (S : Fields)
    (z A B : ℝ) :
    eVariationOn (areaSectionPrimitive k S z A B) (Icc (0 : ℝ) 1) =
      eVariationOn (areaPhysicalPrimitive k S z A) (uIcc A B) := by
  let p := fun x : ℝ => A + (B - A) * x
  have hp : Continuous p := by fun_prop
  have hp0 : p 0 = A := by simp only [p, mul_zero, add_zero]
  have hp1 : p 1 = B := by dsimp only [p]; ring
  have heq : areaSectionPrimitive k S z A B = areaPhysicalPrimitive k S z A ∘ p :=
    funext (area_section_primitive_eq_physical k S z A B)
  rw [heq]
  rcases le_total A B with hab | hba
  · have hmono : Monotone p := fun x y hxy => add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hxy (sub_nonneg.mpr hab))
    rw [eVariationOn.comp_eq_of_monotoneOn _ _ (hmono.monotoneOn _),
      hp.continuousOn.image_Icc_of_monotoneOn zero_le_one (hmono.monotoneOn _),
      hp0, hp1, uIcc_of_le hab]
  · have hanti : Antitone p := fun x y hxy => add_le_add le_rfl
      (mul_le_mul_of_nonpos_left hxy (sub_nonpos.mpr hba))
    rw [eVariationOn.comp_eq_of_antitoneOn _ _ (hanti.antitoneOn _),
      hp.continuousOn.image_Icc_of_antitoneOn zero_le_one (hanti.antitoneOn _),
      hp0, hp1, uIcc_of_ge hba]

/-- The corrected unit-chart section variation. Both inner density
terms contain `vₓ` in the outgoing chart and `uₓ` in the incoming chart. -/
@[expose] noncomputable def areaSectionChartVariation (k : AreaSectionPair)
    (S : Fields) (a δ : ℝ) (y : Ioo (0 : ℝ) 1) : ℝ≥0∞ :=
  if k.incoming then
    eVariationOn (areaSectionPrimitive k S (δ + (a - δ) * y) 0 ((a - δ) * y))
      (Icc (0 : ℝ) 1)
  else
    eVariationOn (areaSectionPrimitive k S ((a - δ) * y) a (δ + (a - δ) * y))
      (Icc (0 : ℝ) 1)

/-- The corrected weighted chart functional is exactly the physical
functional, including the orientation reversal in the outgoing chart. -/
theorem area_section_chart_variation_eq (k : AreaSectionPair) (S : Fields)
    {a δ : ℝ} (_hδ : 0 < δ) (hδa : δ < a) (y : Ioo (0 : ℝ) 1) :
    areaSectionChartVariation k S a δ y = areaSectionVariation k S a δ y := by
  have hw : 0 < (a - δ) * (y : ℝ) := mul_pos (sub_pos.mpr hδa) y.property.1
  have hwa : δ + (a - δ) * (y : ℝ) < a := by
    have hy := y.property.2
    have haδ : 0 < a - δ := sub_pos.mpr hδa
    nlinarith only [haδ, hy]
  cases hki : k.incoming with
  | false =>
    simp only [areaSectionChartVariation, areaSectionVariation, hki,
      Bool.false_eq_true, ite_false, area_section_variation_eq_physical, uIcc_of_ge hwa.le]
  | true =>
    simp only [areaSectionChartVariation, areaSectionVariation, hki,
      ite_true, area_section_variation_eq_physical, uIcc_of_le hw.le]

/-- Measurability of the literal corrected weighted BV chart sections. -/
theorem common_chart_section_measurability
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    Measurable (areaSectionChartVariation k d.rawFields a δ) := by
  have heq : areaSectionChartVariation k d.rawFields a δ =
      areaSectionVariation k d.rawFields a δ :=
    funext (area_section_chart_variation_eq k d.rawFields hδ hδa)
  rw [heq]
  exact common_section_measurability h hD d k hδ hδa

/-- The corrected weighted smooth chart functionals are measurable. -/
theorem smooth_chart_section_measurability
    {a₀ : ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {S : Fields}
    (h : SmoothSolutionBounds a₀ D C S) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    Measurable (areaSectionChartVariation k S a δ) := by
  have heq : areaSectionChartVariation k S a δ = areaSectionVariation k S a δ :=
    funext (area_section_chart_variation_eq k S hδ hδa)
  rw [heq]
  exact smooth_section_measurability h k hδ hδa

/-- The four weighted unit-chart section inequalities, with both signed
inner density factors retained. -/
theorem lemma61_applicability_chart
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    (k : AreaSectionPair) {a δ : ℝ} (hδ : 0 < δ) (hδa : δ < a)
    (y : Ioo (0 : ℝ) 1) :
    areaSectionChartVariation k d.rawFields a δ y ≤
      liminf (fun n => areaSectionChartVariation k (T (d.subsequence n)) a δ y) atTop := by
  have heq (S : Fields) := area_section_chart_variation_eq k S hδ hδa y
  simpa only [heq] using lemma61_applicability h d k hδ hδa y

/-- Fatou for the corrected weighted chart sections, before the outer
factor `a-δ`. At finite datum variation both sides integrate measurable
functions by the preceding section-measurability theorems. -/
theorem area_chart_section_lintegral_le_liminf
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n))
    (d : RadiusLimitData T) (k : AreaSectionPair) {a δ : ℝ}
    (hδ : 0 < δ) (hδa : δ < a) :
    (∫⁻ y : Ioo (0 : ℝ) 1, areaSectionChartVariation k d.rawFields a δ y) ≤
      liminf (fun n => ∫⁻ y : Ioo (0 : ℝ) 1,
        areaSectionChartVariation k (T (d.subsequence n)) a δ y) atTop := by
  have heq (S : Fields) (y : Ioo (0 : ℝ) 1) := area_section_chart_variation_eq k S hδ hδa y
  simpa only [heq] using area_section_lintegral_le_liminf h d k hδ hδa

end ChristodoulouBV

end
