module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Linear growth from an interior differential equation

The differential equation is required only in the open interval. Continuity
supplies the estimate at both endpoints, which is useful when initial data
are given on the boundary of a closed characteristic triangle.
-/

public section

open Set

namespace ChristodoulouBV.ForMathlib

/-- A nonnegative solution of `f' = A f` on an open interval obeys the usual
exponential upper bound even when the derivative at the initial endpoint is
only relative. -/
theorem nonneg_le_initial_mul_exp_of_interior_linear_deriv
    {a b C : ℝ} {f A : ℝ → ℝ}
    (hab : a ≤ b)
    (hfcont : ContinuousOn f (Icc a b))
    (hfnonneg : ∀ s ∈ Icc a b, 0 ≤ f s)
    (hA : ∀ s ∈ Ioo a b, A s ≤ C)
    (hderiv : ∀ s ∈ Ioo a b, HasDerivAt f (A s * f s) s) :
    ∀ s ∈ Icc a b, f s ≤ f a * Real.exp (C * (s - a)) := by
  let F : ℝ → ℝ := fun s => f s * Real.exp (-(C * (s - a)))
  have hEcont : Continuous (fun s : ℝ => Real.exp (-(C * (s - a)))) := by
    fun_prop
  have hFcont : ContinuousOn F (Icc a b) := hfcont.mul hEcont.continuousOn
  have hFderiv (s : ℝ) (hs : s ∈ Ioo a b) :
      HasDerivAt F
        (Real.exp (-(C * (s - a))) * (f s * (A s - C))) s := by
    have hinner : HasDerivAt (fun t : ℝ => -(C * (t - a))) (-C) s := by
      convert (((hasDerivAt_id s).sub_const a).const_mul C).neg using 1
      · funext t
        simp only [Pi.neg_apply, id_eq]
      · ring
    have hExp : HasDerivAt (fun t : ℝ => Real.exp (-(C * (t - a))))
        (Real.exp (-(C * (s - a))) * (-C)) s := hinner.exp
    convert (hderiv s hs).mul hExp using 1
    ring
  have hFdiff : DifferentiableOn ℝ F (interior (Icc a b)) := by
    intro s hs
    have hs' : s ∈ Ioo a b := by simpa only [interior_Icc] using hs
    exact (hFderiv s hs').differentiableAt.differentiableWithinAt
  have hFnonpos : ∀ s ∈ interior (Icc a b), deriv F s ≤ 0 := by
    intro s hs
    have hs' : s ∈ Ioo a b := by simpa only [interior_Icc] using hs
    rw [(hFderiv s hs').deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
      (mul_nonpos_of_nonneg_of_nonpos
        (hfnonneg s ⟨hs'.1.le, hs'.2.le⟩) (sub_nonpos.mpr (hA s hs')))
  have hFanti := antitoneOn_of_deriv_nonpos (convex_Icc a b)
    hFcont hFdiff hFnonpos
  intro s hs
  have hFs : F s ≤ F a := hFanti ⟨le_rfl, hab⟩ hs hs.1
  have hFs' : f s * Real.exp (-(C * (s - a))) ≤ f a := by
    simpa only [F, sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one] using hFs
  have hmul := mul_le_mul_of_nonneg_right hFs' (Real.exp_nonneg (C * (s - a)))
  calc
    f s = (f s * Real.exp (-(C * (s - a)))) *
        Real.exp (C * (s - a)) := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    _ ≤ f a * Real.exp (C * (s - a)) := hmul

end ChristodoulouBV.ForMathlib

end
