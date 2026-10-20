module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Absolute transport bounds on compact characteristic segments

The endpoint estimate is stated in extended nonnegative values so that it
can later be integrated against the analytic area measure without a prior
global area finiteness assumption.
-/

public section

open MeasureTheory Set
open scoped ENNReal Interval

namespace ChristodoulouBV

/-- Integrating a continuous derivative gives an absolute endpoint bound in
`ℝ≥0∞`. No integrability outside the compact segment is required. -/
theorem ofReal_abs_endpoint_le_initial_add_lintegral
    {a b : ℝ} (hab : a ≤ b) {f j : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hj : ContinuousOn j (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (j x) x) :
    ENNReal.ofReal |f b| ≤ ENNReal.ofReal |f a| +
      ∫⁻ x in Ioo a b, ENNReal.ofReal |j x| := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hab hf hderiv (hj.intervalIntegrable_of_Icc hab)
  have hAbsInt : 0 ≤ ∫ x in a..b, |j x| :=
    intervalIntegral.integral_nonneg hab (fun _ _ => abs_nonneg _)
  have hReal : |f b| ≤ |f a| + ∫ x in a..b, |j x| := by
    have hfb : f b = f a + ∫ x in a..b, j x := by
      linear_combination hFTC.symm
    rw [hfb]
    exact (abs_add_le _ _).trans
      (add_le_add le_rfl (intervalIntegral.abs_integral_le_integral_abs hab))
  have hCast := ENNReal.ofReal_le_ofReal hReal
  rw [ENNReal.ofReal_add (abs_nonneg _) hAbsInt] at hCast
  have hIntegrable : IntegrableOn (fun x => |j x|) (Ioo a b) :=
    (hj.abs.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hIntegral : ENNReal.ofReal (∫ x in a..b, |j x|) =
      ∫⁻ x in Ioo a b, ENNReal.ofReal |j x| := by
    rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
    exact ofReal_integral_eq_lintegral_ofReal hIntegrable
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
  simpa only [hIntegral] using hCast

/-- Tonelli on a strict characteristic triangle. Endpoint lines have zero
planar measure, so the formula uses the source's open carriers. -/
theorem lintegral_open_triangle (a b : ℝ) (F : ℝ × ℝ → ℝ≥0∞)
    (hF : AEMeasurable F
      (volume.restrict {p : ℝ × ℝ | p.1 ∈ Ioo a b ∧ p.2 ∈ Ioo p.1 b})) :
    (∫⁻ p in {p : ℝ × ℝ | p.1 ∈ Ioo a b ∧ p.2 ∈ Ioo p.1 b}, F p) =
      ∫⁻ x in Ioo a b, ∫⁻ y in Ioo x b, F (x, y) := by
  let T : Set (ℝ × ℝ) :=
    {p | p.1 ∈ Ioo a b ∧ p.2 ∈ Ioo p.1 b}
  have hT : MeasurableSet T := by
    change MeasurableSet {p : ℝ × ℝ |
      p.1 ∈ Ioo a b ∧ (p.1 < p.2 ∧ p.2 < b)}
    exact (measurableSet_Ioo.preimage measurable_fst).inter
      ((measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const))
  have hIndicator : AEMeasurable (T.indicator F) volume :=
    (aemeasurable_indicator_iff hT).mpr hF
  calc
    (∫⁻ p in T, F p) = ∫⁻ p, T.indicator F p :=
      (lintegral_indicator hT _).symm
    _ = ∫⁻ x : ℝ, ∫⁻ y : ℝ, T.indicator F (x, y) := by
      rw [Measure.volume_eq_prod ℝ ℝ]
      rw [Measure.volume_eq_prod ℝ ℝ] at hIndicator
      exact lintegral_prod _ hIndicator
    _ = ∫⁻ x in Ioo a b, ∫⁻ y in Ioo x b, F (x, y) := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ Ioo a b
      · rw [indicator_of_mem hx]
        have hfiber : (fun y : ℝ => T.indicator F (x, y)) =
            (Ioo x b).indicator (fun y => F (x, y)) := by
          funext y
          by_cases hy : y ∈ Ioo x b
          · have hxy : (x, y) ∈ T := ⟨hx, hy⟩
            simp [hxy, hy]
          · have hxy : (x, y) ∉ T := fun h => hy h.2
            simp [hxy, hy]
        rw [hfiber, lintegral_indicator measurableSet_Ioo]
      · rw [indicator_of_notMem hx]
        have hzero : (fun y : ℝ => T.indicator F (x, y)) = fun _ => 0 := by
          funext y
          have hxy : (x, y) ∉ T := fun h => hx h.1
          simp [hxy]
        rw [hzero]
        simp

/-- Tonelli on a strict characteristic triangle in the opposite order. This
is the order of the diagonal variation integral in (4.6). -/
theorem lintegral_open_triangle_swap (a b : ℝ) (F : ℝ × ℝ → ℝ≥0∞)
    (hF : AEMeasurable F
      (volume.restrict {p : ℝ × ℝ | p.1 ∈ Ioo a b ∧ p.2 ∈ Ioo p.1 b})) :
    (∫⁻ p in {p : ℝ × ℝ | p.1 ∈ Ioo a b ∧ p.2 ∈ Ioo p.1 b}, F p) =
      ∫⁻ y in Ioo a b, ∫⁻ x in Ioo a y, F (x, y) := by
  let T : Set (ℝ × ℝ) :=
    {p | p.1 ∈ Ioo a b ∧ p.2 ∈ Ioo p.1 b}
  have hT : MeasurableSet T := by
    change MeasurableSet {p : ℝ × ℝ |
      p.1 ∈ Ioo a b ∧ (p.1 < p.2 ∧ p.2 < b)}
    exact (measurableSet_Ioo.preimage measurable_fst).inter
      ((measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const))
  have hIndicator : AEMeasurable (T.indicator F) volume :=
    (aemeasurable_indicator_iff hT).mpr hF
  calc
    (∫⁻ p in T, F p) = ∫⁻ p, T.indicator F p :=
      (lintegral_indicator hT _).symm
    _ = ∫⁻ y : ℝ, ∫⁻ x : ℝ, T.indicator F (x, y) := by
      rw [Measure.volume_eq_prod ℝ ℝ]
      rw [Measure.volume_eq_prod ℝ ℝ] at hIndicator
      exact lintegral_prod_symm _ hIndicator
    _ = ∫⁻ y in Ioo a b, ∫⁻ x in Ioo a y, F (x, y) := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr_ae
      filter_upwards [] with y
      by_cases hy : y ∈ Ioo a b
      · rw [indicator_of_mem hy]
        have hfiber : (fun x : ℝ => T.indicator F (x, y)) =
            (Ioo a y).indicator (fun x => F (x, y)) := by
          funext x
          by_cases hx : x ∈ Ioo a y
          · have hxy : (x, y) ∈ T := by
              exact ⟨⟨hx.1, hx.2.trans hy.2⟩, ⟨hx.2, hy.2⟩⟩
            simp [hxy, hx]
          · have hxy : (x, y) ∉ T := by
              intro h
              exact hx ⟨h.1.1, h.2.1⟩
            simp [hxy, hx]
        rw [hfiber, lintegral_indicator measurableSet_Ioo]
      · rw [indicator_of_notMem hy]
        have hzero : (fun x : ℝ => T.indicator F (x, y)) = fun _ => 0 := by
          funext x
          have hxy : (x, y) ∉ T := by
            intro h
            exact hy ⟨h.1.1.trans h.2.1, h.2.2⟩
          simp [hxy]
        rw [hzero]
        simp

end ChristodoulouBV

end
