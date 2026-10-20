module

public import ChristodoulouBV.Existence.Lemma62CounterexamplesHypotheses
public import ChristodoulouBV.ForMathlib.BoundedVariation.AbsolutelyContinuous
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Oscillatory sections with nonintegrable variation

For `s > 0`, the section `sin (4*x/s)` has variation between `1/s`
(for `s < 1`) and `4/s`. The lower bound uses `cos² ≤ |cos|` and
an explicit primitive, avoiding a count of periods. This is a variant of
the sine construction in the author ruling on the ordinary-integral reading of Lemma 6.2; see ERRATA.md.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

attribute [local instance] Measure.Subtype.measureSpace

namespace ChristodoulouBV.Lemma62Counterexamples

/-- The oscillatory BV section. -/
noncomputable def sine (s x : ℝ) : ℝ := Real.sin (4 * x / s)

theorem sine_deriv (s x : ℝ) :
    HasDerivAt (sine s) (Real.cos (4 * x / s) * (4 / s)) x := by
  change HasDerivAt (fun x : ℝ => Real.sin (4 * x / s)) _ x
  convert ((((hasDerivAt_id x).const_mul 4).div_const s).sin) using 1 <;> simp

theorem sine_ac (s : ℝ) : AbsolutelyContinuousOnInterval (sine s) 0 1 := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  exact (Real.contDiff_sin.comp ((contDiff_const.mul contDiff_id).div_const s)).contDiffOn

theorem sine_variation (s : ℝ) :
    eVariationOn (sine s) (Icc (0 : ℝ) 1) =
      ENNReal.ofReal (∫ x in (0 : ℝ)..1, |Real.cos (4 * x / s) * (4 / s)|) := by
  rw [(sine_ac s).eVariationOn_eq_integral_abs_deriv (by norm_num)]
  simp_rw [(sine_deriv s _).deriv]

theorem sine_variation_le {s : ℝ} (hs : 0 < s) :
    eVariationOn (sine s) (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (4 / s) := by
  rw [sine_variation]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ _x in (0 : ℝ)..1, (4 / s) := by
      apply intervalIntegral.integral_mono (by norm_num)
        (((Real.continuous_cos.comp ((continuous_const.mul continuous_id).div_const s)).mul
          continuous_const).abs.intervalIntegrable 0 1) intervalIntegrable_const
      intro x
      dsimp
      rw [abs_mul, abs_of_pos (div_pos (by norm_num) hs)]
      exact mul_le_of_le_one_left (by positivity) (Real.abs_cos_le_one _)
    _ = 4 / s := by simp

theorem sine_variation_ge {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ENNReal.ofReal (1 / s) ≤ eVariationOn (sine s) (Icc (0 : ℝ) 1) := by
  rw [sine_variation]
  apply ENNReal.ofReal_le_ofReal
  have hcont : Continuous (fun x : ℝ => (4 / s) * Real.cos (4 * x / s) ^ 2) := by
    fun_prop
  have hprim : (∫ x in (0 : ℝ)..1, (4 / s) * Real.cos (4 * x / s) ^ 2) =
      2 / s + Real.sin (8 / s) / 4 := by
    have hd (x : ℝ) : HasDerivAt (fun x : ℝ => (2 / s) * x +
        Real.sin (8 * x / s) / 4) ((4 / s) * Real.cos (4 * x / s) ^ 2) x := by
      convert (((hasDerivAt_id x).const_mul (2 / s)).add
        ((((hasDerivAt_id x).const_mul 8).div_const s).sin.div_const 4)) using 1
      · rfl
      simp only [id_eq, mul_one]
      have hc := Real.cos_two_mul (4 * x / s)
      have he : 8 * x / s = 2 * (4 * x / s) := by ring
      rw [he, hc]
      ring
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hd x) (hcont.intervalIntegrable 0 1)
  have hle : (∫ x in (0 : ℝ)..1, (4 / s) * Real.cos (4 * x / s) ^ 2) ≤
      ∫ x in (0 : ℝ)..1, |Real.cos (4 * x / s) * (4 / s)| := by
    apply intervalIntegral.integral_mono (by norm_num) (hcont.intervalIntegrable 0 1)
      (((Real.continuous_cos.comp ((continuous_const.mul continuous_id).div_const s)).mul
        continuous_const).abs.intervalIntegrable 0 1)
    intro x
    dsimp
    rw [abs_mul, abs_of_pos (div_pos (by norm_num) hs), mul_comm]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hc := Real.abs_cos_le_one (4 * x / s)
    nlinarith [sq_abs (Real.cos (4 * x / s)), abs_nonneg (Real.cos (4 * x / s))]
  rw [hprim] at hle
  have hinv : 1 ≤ 1 / s := (le_div_iff₀ hs).2 (by linarith)
  have hsin := Real.neg_one_le_sin (8 / s)
  calc
    1 / s ≤ 2 / s + Real.sin (8 / s) / 4 := by
      simp only [div_eq_mul_inv] at *
      linarith
    _ ≤ _ := hle

/-- The lower integral of the reciprocal on the open unit interval is infinite. -/
theorem lintegral_inv_top :
    (∫⁻ y : Ioo (0 : ℝ) 1, ENNReal.ofReal (1 / (y : ℝ))) = ∞ := by
  by_contra h
  have hm : Measurable (fun y : Ioo (0 : ℝ) 1 =>
      ENNReal.ofReal (1 / (y : ℝ))) := by fun_prop
  have hi := integrable_toReal_of_lintegral_ne_top hm.aemeasurable h
  have hi' : Integrable (fun y : Ioo (0 : ℝ) 1 => (y : ℝ) ^ (-1 : ℝ)) volume := by
    convert hi using 1
    funext y
    simp [Real.rpow_neg_one, ENNReal.toReal_ofReal, le_of_lt y.property.1]
  have hh : IntegrableOn (fun y : ℝ => y ^ (-1 : ℝ)) (Ioo (0 : ℝ) 1) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).2 hi'
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).1 hh
  norm_num at this

end ChristodoulouBV.Lemma62Counterexamples
