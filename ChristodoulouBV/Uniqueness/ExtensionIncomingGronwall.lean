module

public import ChristodoulouBV.ForMathlib.Gronwall.Integral
import Mathlib.Tactic.FunProp

/-!
# A one-dimensional estimate for the off-axis scalar transport system

The coupled `θ` and `ζ` equations reduce to this forward Volterra bound
after the incoming expansion and radius have been bounded uniformly.
-/

public section

namespace ChristodoulouBV.Uniqueness

open Set MeasureTheory

/-- A continuous scalar envelope satisfying a constant-coefficient Volterra
inequality is bounded by its initial envelope times an exponential. -/
theorem incoming_scalar_envelope_le_exp
    {a b A C : ℝ} {Θ : ℝ → ℝ}
    (hab : a ≤ b) (hC : 0 ≤ C)
    (hΘ : ContinuousOn Θ (Icc a b))
    (hbound : ∀ v ∈ Icc a b,
      |Θ v| ≤ A + C * ∫ s in a..v, |Θ s|) :
    ∀ v ∈ Icc a b, |Θ v| ≤ A * Real.exp (C * (v - a)) := by
  have hAbs : ContinuousOn (fun v => |Θ v|) (Icc a b) :=
    continuous_abs.comp_continuousOn hΘ
  have hInt : IntervalIntegrable (fun v => |Θ v|) volume a b :=
    hAbs.intervalIntegrable_of_Icc hab
  have hProd : IntervalIntegrable (fun v => C * |Θ v|) volume a b :=
    hInt.const_mul C
  have hConst : IntervalIntegrable (fun _ : ℝ => C) volume a b :=
    intervalIntegrable_const
  have H := intervalIntegral.le_mul_exp_integral_of_le_integral
    (a := a) (b := b) (A := A) (k := fun _ => C)
    (h := fun v => |Θ v|) hab hConst hProd
    (fun _ _ => hC)
    (fun v hv => by
      simpa only [intervalIntegral.integral_const_mul] using hbound v hv)
  intro v hv
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using H v hv

end ChristodoulouBV.Uniqueness

end
