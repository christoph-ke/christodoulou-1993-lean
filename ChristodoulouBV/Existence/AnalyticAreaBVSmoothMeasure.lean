module

public import ChristodoulouBV.Existence.AnalyticAreaBVLocality
public import ChristodoulouBV.ForMathlib.BoundedVariation.LocalStieltjes
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import all ChristodoulouBV.ForMathlib.BoundedVariation.LocalStieltjes
import Mathlib.Tactic

/-!
# Variation measures of absolutely continuous primitives

On an open interval, the variation measure of an absolutely continuous
primitive is its absolute derivative density. Values at the cutoff
endpoints do not enter this identification.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- An absolutely continuous local Stieltjes measure has variation
equal to the absolute derivative density. -/
theorem localStieltjes_variation_eq_withDensity
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    (BoundedVariationOn.localStieltjes (f := f) hab
      (by simpa only [uIcc_of_le hab] using hf.boundedVariationOn)).variation =
      ((volume : Measure ℝ).withDensity (fun t => ENNReal.ofReal |deriv f t|)).restrict
        (Icc a b) := by
  have hi : Integrable (deriv f) (volume.restrict (Icc a b)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hf.intervalIntegrable_deriv
  rw [BoundedVariationOn.localStieltjes_eq_withDensityᵥ hab hf,
    VectorMeasure.variation_restrict measurableSet_Icc, Measure.variation_withDensityᵥ hi]
  simp only [Real.enorm_eq_ofReal_abs]
  rw [← restrict_withDensity measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc, inter_self]

/-- If a globally BV primitive agrees with an absolutely continuous
primitive on an open interval, its variation measure there is the
absolute derivative density of the latter primitive. -/
theorem variation_measure_restrict_eq_withDensity_of_ac
    {F f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : BoundedVariationOn F univ) (hf : AbsolutelyContinuousOnInterval f a b)
    (he : EqOn F f (Ioo a b)) :
    hF.vectorMeasure.variation.restrict (Ioo a b) =
      ((volume : Measure ℝ).withDensity (fun t => ENNReal.ofReal |deriv f t|)).restrict
        (Ioo a b) := by
  have hfb : BoundedVariationOn f (Icc a b) := by
    simpa only [uIcc_of_le hab] using hf.boundedVariationOn
  let hb := BoundedVariationOn.extendIcc_boundedVariationOn hab hfb
  have hloc := localStieltjes_variation_eq_withDensity hab hf
  have hEq : EqOn F (fun t => Function.extendIcc f hab t + 0) (Ioo a b) := by
    intro t ht
    change F t = Function.extendIcc f hab t + 0
    rw [add_zero, BoundedVariationOn.extendIcc_of_mem hab (Ioo_subset_Icc_self ht)]
    exact he ht
  rw [variation_measure_restrict_Ioo_eq_of_eqOn_add_const hF hb hEq]
  have hv : hb.vectorMeasure.variation.restrict (Icc a b) =
      ((volume : Measure ℝ).withDensity (fun t => ENNReal.ofReal |deriv f t|)).restrict
        (Icc a b) := by
    rw [BoundedVariationOn.localStieltjes, VectorMeasure.variation_restrict measurableSet_Icc]
      at hloc
    exact hloc
  have hr := congrArg (fun μ : Measure ℝ => μ.restrict (Ioo a b)) hv
  simpa only [Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr Ioo_subset_Icc_self] using hr

end ChristodoulouBV

end
