module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Radius-based attenuation comparison

A linear incoming transport equation can be compared with the change of a
monotone radius. This avoids a bound for the incoming radius derivative.
-/

public section

open Set

namespace ChristodoulouBV.ForMathlib

/-- If the coefficient in the incoming equation for a positive expansion is
at most linear in radius, its decrease is controlled by the initial radius.
The estimate is independent of the size of the radius derivative. -/
theorem expansion_lower_of_radius_coefficient
    {a b C : ℝ} {lam r nu coeff : ℝ → ℝ}
    (hab : a ≤ b) (hC : 0 ≤ C)
    (hlam_cont : ContinuousOn lam (Icc a b))
    (hr_cont : ContinuousOn r (Icc a b))
    (hlam_pos : ∀ s ∈ Icc a b, 0 < lam s)
    (hnu : ∀ s ∈ Ioo a b, nu s ≤ 0)
    (hcoeff : ∀ s ∈ Ioo a b, coeff s ≤ C * r s)
    (hlam_deriv : ∀ s ∈ Ioo a b,
      HasDerivAt lam (lam s * nu s * coeff s) s)
    (hr_deriv : ∀ s ∈ Ioo a b, HasDerivAt r (nu s) s) :
    ∀ s ∈ Icc a b,
      lam a * Real.exp (-(C / 2) * r a ^ 2) ≤ lam s := by
  let F : ℝ → ℝ := fun s => lam s * Real.exp (-(C / 2) * r s ^ 2)
  have hEcont : ContinuousOn (fun s => Real.exp (-(C / 2) * r s ^ 2))
      (Icc a b) := by
    fun_prop
  have hFcont : ContinuousOn F (Icc a b) := hlam_cont.mul hEcont
  have hFderiv (s : ℝ) (hs : s ∈ Ioo a b) :
      HasDerivAt F
        (Real.exp (-(C / 2) * r s ^ 2) *
          (lam s * nu s * (coeff s - C * r s))) s := by
    have hr := hr_deriv s hs
    have hinner : HasDerivAt (fun t => -(C / 2) * r t ^ 2)
        (-(C / 2) * (2 * r s * nu s)) s := by
      convert (hr.pow 2).const_mul (-(C / 2)) using 1
      ring
    have hExp : HasDerivAt (fun t => Real.exp (-(C / 2) * r t ^ 2))
        (Real.exp (-(C / 2) * r s ^ 2) *
          (-(C / 2) * (2 * r s * nu s))) s := hinner.exp
    convert (hlam_deriv s hs).mul hExp using 1
    ring
  have hFdiff : DifferentiableOn ℝ F (interior (Icc a b)) := by
    intro s hs
    have hs' : s ∈ Ioo a b := by simpa only [interior_Icc] using hs
    exact (hFderiv s hs').differentiableAt.differentiableWithinAt
  have hFnonneg : ∀ s ∈ interior (Icc a b), 0 ≤ deriv F s := by
    intro s hs
    have hs' : s ∈ Ioo a b := by simpa only [interior_Icc] using hs
    rw [(hFderiv s hs').deriv]
    have hprod : 0 ≤ nu s * (coeff s - C * r s) :=
      mul_nonneg_of_nonpos_of_nonpos (hnu s hs') (sub_nonpos.mpr (hcoeff s hs'))
    have hrest : 0 ≤ lam s * nu s * (coeff s - C * r s) := by
      rw [mul_assoc]
      exact mul_nonneg (hlam_pos s ⟨hs'.1.le, hs'.2.le⟩).le hprod
    exact mul_nonneg (Real.exp_nonneg _) hrest
  have hFmono := monotoneOn_of_deriv_nonneg (convex_Icc a b)
    hFcont hFdiff hFnonneg
  intro s hs
  have hFa : F a ≤ F s := hFmono ⟨le_rfl, hab⟩ hs hs.1
  have hExp : Real.exp (-(C / 2) * r s ^ 2) ≤ 1 := by
    have harg : -(C / 2) * r s ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (div_nonneg hC (by norm_num))) (sq_nonneg _)
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr harg
  have hFs : F s ≤ lam s := by
    dsimp [F]
    nlinarith only [hExp, (hlam_pos s hs).le]
  exact hFa.trans hFs

end ChristodoulouBV.ForMathlib

end
