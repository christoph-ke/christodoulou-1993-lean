module

public import ChristodoulouBV.Existence.AreaSectionLimitFinite
import Mathlib.Tactic

/-!
# Primitive-preserving regularization of the area triples

The pointwise primitive can itself serve as the BV component of the
equivalent triple `(1,G,0)`. Constant physical extension, followed by
scaling into `[0,1]`, supplies the common transverse exceptional set.
The padding parameter is positive; variation is preserved exactly at
every padding scale, so removing it cannot enlarge a liminf bound.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The regularized BV component in the equivalent triple `(1,G,0)`.
The padding `ε` embeds every physical section into the same unit interval;
subtracting the base value normalizes the primitive at zero. -/
@[expose] noncomputable def areaRegularizedPrimitive (k : AreaSectionPair)
    (S : Fields) (a δ ε : ℝ) (y : Ioo (0 : ℝ) 1) (x : ℝ) : ℝ :=
  areaClampedPrimitive k S a δ y ((a + ε) * x) - areaClampedPrimitive k S a δ y 0

/-- The regularized primitive has the exact zero base value. -/
theorem area_regularized_primitive_zero (k : AreaSectionPair) (S : Fields)
    (a δ ε : ℝ) (y : Ioo (0 : ℝ) 1) : areaRegularizedPrimitive k S a δ ε y 0 = 0 := by
  simp only [areaRegularizedPrimitive, mul_zero, sub_self]

private theorem variation_clamped_scaled (F : ℝ → ℝ) {l r L : ℝ}
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ L) (hL : 0 < L) :
    eVariationOn (fun x => F (max l (min r (L * x)))) (Icc (0 : ℝ) 1) =
      eVariationOn F (Icc l r) := by
  let p := fun x : ℝ => max l (min r (L * x))
  have hp : Monotone p := fun x y hxy => max_le_max_left _
    (min_le_min_left _ (mul_le_mul_of_nonneg_left hxy hL.le))
  have himage : p '' Icc (0 : ℝ) 1 = Icc l r := by
    ext t
    constructor
    · rintro ⟨x, _, rfl⟩
      exact ⟨le_max_left _ _, max_le hlr (min_le_left _ _)⟩
    · intro ht
      refine ⟨t / L, ⟨div_nonneg (hl.trans ht.1) hL.le,
        (div_le_one hL).mpr (ht.2.trans hr)⟩, ?_⟩
      dsimp only [p]
      rw [mul_div_cancel₀ _ hL.ne', min_eq_right ht.2, max_eq_right ht.1]
  have heq := eVariationOn.comp_eq_of_monotoneOn F p (hp.monotoneOn (Icc (0 : ℝ) 1))
  rw [himage] at heq
  exact heq

private theorem variation_clamped_scaled_le_univ (F : ℝ → ℝ) {l r L : ℝ}
    (hlr : l ≤ r) (hL : 0 ≤ L) :
    eVariationOn (fun x => F (max l (min r (L * x)))) univ ≤
      eVariationOn F (Icc l r) :=
  eVariationOn.comp_le_of_monotoneOn F (fun x => max l (min r (L * x)))
    (fun _ _ _ _ hxy => max_le_max_left _
      (min_le_min_left _ (mul_le_mul_of_nonneg_left hxy hL)))
    (fun _ _ => ⟨le_max_left _ _, max_le hlr (min_le_left _ _)⟩)

/-- Each padding scale preserves the entire pointwise section variation,
including isolated values and both endpoints. -/
theorem area_regularized_primitive_variation (k : AreaSectionPair) (S : Fields)
    {a δ ε : ℝ} (hδ : 0 < δ) (hδa : δ < a) (hε : 0 < ε)
    (y : Ioo (0 : ℝ) 1) :
    eVariationOn (areaRegularizedPrimitive k S a δ ε y) (Icc (0 : ℝ) 1) =
      areaSectionVariation k S a δ y := by
  have hconst : eVariationOn (areaRegularizedPrimitive k S a δ ε y) (Icc (0 : ℝ) 1) =
      eVariationOn (fun x => areaClampedPrimitive k S a δ y ((a + ε) * x))
        (Icc (0 : ℝ) 1) := by
    change eVariationOn (fun x => areaClampedPrimitive k S a δ y ((a + ε) * x) -
      areaClampedPrimitive k S a δ y 0) (Icc (0 : ℝ) 1) = _
    simpa only [sub_eq_add_neg] using eVariationOn.add_const
      (fun x => areaClampedPrimitive k S a δ y ((a + ε) * x))
      (-areaClampedPrimitive k S a δ y 0) (Icc (0 : ℝ) 1)
  rw [hconst]
  let w := (a - δ) * (y : ℝ)
  have hw : 0 < w := mul_pos (sub_pos.mpr hδa) y.property.1
  have hwa : δ + w < a := by
    have hy := y.property.2
    have haδ : 0 < a - δ := sub_pos.mpr hδa
    dsimp only [w]
    nlinarith only [haδ, hy]
  have hL : 0 < a + ε := by linarith only [hδ, hδa, hε]
  cases hki : k.incoming with
  | false =>
    simp only [areaClampedPrimitive, areaSectionVariation, hki,
      Bool.false_eq_true, ite_false]
    exact variation_clamped_scaled _ (by linarith only [hδ, hw]) hwa.le
      (by linarith only [hε]) hL
  | true =>
    simp only [areaClampedPrimitive, areaSectionVariation, hki, ite_true]
    exact variation_clamped_scaled _ le_rfl hw.le (by linarith only [hwa, hδ, hε]) hL

/-- Constant extension bounds the whole-line variation by the exact
physical section variation, at every padding scale. -/
theorem area_regularized_primitive_variation_univ_le (k : AreaSectionPair) (S : Fields)
    {a δ ε : ℝ} (hδ : 0 < δ) (hδa : δ < a) (hε : 0 < ε)
    (y : Ioo (0 : ℝ) 1) :
    eVariationOn (areaRegularizedPrimitive k S a δ ε y) univ ≤
      areaSectionVariation k S a δ y := by
  have hconst : eVariationOn (areaRegularizedPrimitive k S a δ ε y) univ =
      eVariationOn (fun x => areaClampedPrimitive k S a δ y ((a + ε) * x)) univ := by
    change eVariationOn (fun x => areaClampedPrimitive k S a δ y ((a + ε) * x) -
      areaClampedPrimitive k S a δ y 0) univ = _
    simpa only [sub_eq_add_neg] using eVariationOn.add_const
      (fun x => areaClampedPrimitive k S a δ y ((a + ε) * x))
      (-areaClampedPrimitive k S a δ y 0) univ
  rw [hconst]
  let w := (a - δ) * (y : ℝ)
  have hw : 0 < w := mul_pos (sub_pos.mpr hδa) y.property.1
  have hwa : δ + w < a := by
    have hy := y.property.2
    have haδ : 0 < a - δ := sub_pos.mpr hδa
    dsimp only [w]
    nlinarith only [haδ, hy]
  have hL : 0 ≤ a + ε := by linarith only [hδ, hδa, hε]
  cases hki : k.incoming with
  | false =>
    simp only [areaClampedPrimitive, areaSectionVariation, hki,
      Bool.false_eq_true, ite_false]
    exact variation_clamped_scaled_le_univ _ hwa.le hL
  | true =>
    simp only [areaClampedPrimitive, areaSectionVariation, hki, ite_true]
    exact variation_clamped_scaled_le_univ _ hw.le hL

/-- The Stieltjes variation of the equivalent triple `(1,G,0)` is
exactly the source's pointwise section functional. -/
theorem area_regularized_stieltjes_variation (k : AreaSectionPair) (S : Fields)
    {a δ ε : ℝ} (hδ : 0 < δ) (hδa : δ < a) (hε : 0 < ε)
    (y : Ioo (0 : ℝ) 1) :
    eVariationOn (intervalIntegral.productPrimitive (fun _ => (1 : ℝ))
      (areaRegularizedPrimitive k S a δ ε y) (deriv (fun _ => (1 : ℝ))) (fun _ => 0))
        (Icc (0 : ℝ) 1) = areaSectionVariation k S a δ y := by
  have heq : intervalIntegral.productPrimitive (fun _ => (1 : ℝ))
      (areaRegularizedPrimitive k S a δ ε y) (deriv (fun _ => (1 : ℝ))) (fun _ => 0) =
      areaRegularizedPrimitive k S a δ ε y := by
    funext x
    simp only [intervalIntegral.productPrimitive, deriv_const, one_mul, mul_zero,
      add_zero, intervalIntegral.integral_zero, area_regularized_primitive_zero, sub_zero]
  rw [heq]
  exact area_regularized_primitive_variation k S hδ hδa hε y

/-- The original smooth primitives converge pointwise after constant
physical extension, on the same shared subsequence and at every real
evaluation point. -/
theorem area_clamped_primitive_limit
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    (k : AreaSectionPair) {a δ : ℝ} (hδ : 0 < δ) (hδa : δ < a)
    (y : Ioo (0 : ℝ) 1) (t : ℝ) :
    Tendsto (fun n => areaClampedPrimitive k (T (d.subsequence n)) a δ y t) atTop
      (𝓝 (areaClampedPrimitive k d.rawFields a δ y t)) := by
  let w := (a - δ) * (y : ℝ)
  have hw : 0 < w := mul_pos (sub_pos.mpr hδa) y.property.1
  have hwa : δ + w < a := by
    have hy := y.property.2
    have haδ : 0 < a - δ := sub_pos.mpr hδa
    dsimp only [w]
    nlinarith only [haδ, hy]
  cases hki : k.incoming with
  | false =>
    simp only [areaClampedPrimitive, hki, Bool.false_eq_true, ite_false]
    apply area_physical_primitive_limit h d k hδ (A := δ + w) (B := a)
    · intro s hs
      simp only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false]
      exact ⟨hw.le, by linarith only [hs.1, hδ]⟩
    · intro s hs
      simp only [areaPhysicalPoint, hki, Bool.false_eq_true, ite_false]
      linarith only [hs.1]
    · exact ⟨hwa.le, le_rfl⟩
    · exact ⟨le_max_left _ _, max_le hwa.le (min_le_left _ _)⟩
  | true =>
    simp only [areaClampedPrimitive, hki, ite_true]
    apply area_physical_primitive_limit h d k hδ (A := 0) (B := w)
    · intro s hs
      simp only [areaPhysicalPoint, hki, ite_true]
      exact ⟨hs.1, by linarith only [hs.2, hδ]⟩
    · intro s hs
      simp only [areaPhysicalPoint, hki, ite_true]
      linarith only [hs.2]
    · exact ⟨le_rfl, hw.le⟩
    · exact ⟨le_max_left _ _, max_le hw.le (min_le_left _ _)⟩

/-- Pointwise convergence of the regularized triples needs no further
extraction, and holds even at their BV jump values. -/
theorem area_regularized_primitive_limit
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (d : RadiusLimitData T)
    (k : AreaSectionPair) {a δ ε : ℝ} (hδ : 0 < δ) (hδa : δ < a)
    (y : Ioo (0 : ℝ) 1) (x : ℝ) :
    Tendsto (fun n => areaRegularizedPrimitive k (T (d.subsequence n)) a δ ε y x) atTop
      (𝓝 (areaRegularizedPrimitive k d.rawFields a δ ε y x)) :=
  (area_clamped_primitive_limit h d k hδ hδa y ((a + ε) * x)).sub
    (area_clamped_primitive_limit h d k hδ hδa y 0)

end ChristodoulouBV

end
