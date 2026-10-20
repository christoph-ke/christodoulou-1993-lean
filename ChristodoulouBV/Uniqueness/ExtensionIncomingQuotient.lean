module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingFlux
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Incoming mass-gap and quotient identities

These are pointwise first-derivative consequences of the C¹ characteristic
equations. They use the total mass and radius only where these fields are
defined and positive.
-/

public section

namespace ChristodoulouBV.Uniqueness

/-- The incoming derivative of the mass gap `q = 1 - 2m/r`. -/
theorem incoming_mass_gap_hasDerivAt
    {r m : ℝ → ℝ} {v N Z : ℝ}
    (hr : HasDerivAt r N v)
    (hm : HasDerivAt m
      ((1 - 2 * m v / r v) * Z ^ 2 / (2 * N)) v)
    (hr0 : r v ≠ 0) (hN0 : N ≠ 0) :
    HasDerivAt (fun w => 1 - 2 * m w / r w)
      (-(1 - 2 * m v / r v) * Z ^ 2 / (r v * N) +
        (2 * m v / r v) * N / r v) v := by
  have h := ((hasDerivAt_const v (1 : ℝ)).sub
    (((HasDerivAt.const_mul 2 hm).div hr hr0)))
  convert h using 1
  field_simp
  ring

/-- The quotient `κ = λ/(1-2m/r)` solves a linear incoming equation with
coefficient `ζ²/(rν) = -ζ²/(r|ν|)` when `ν < 0`. -/
theorem incoming_expansion_quotient_hasDerivAt
    {r m lam : ℝ → ℝ} {v N Z : ℝ}
    (hr : HasDerivAt r N v)
    (hm : HasDerivAt m
      ((1 - 2 * m v / r v) * Z ^ 2 / (2 * N)) v)
    (hlam : HasDerivAt lam
      ((2 * m v / r v) * lam v * N /
        ((1 - 2 * m v / r v) * r v)) v)
    (hr0 : r v ≠ 0) (hN0 : N ≠ 0)
    (hq0 : 1 - 2 * m v / r v ≠ 0) :
    HasDerivAt (fun w => lam w / (1 - 2 * m w / r w))
      ((lam v / (1 - 2 * m v / r v)) * Z ^ 2 / (r v * N)) v := by
  have hq := incoming_mass_gap_hasDerivAt hr hm hr0 hN0
  have hgap : r v - 2 * m v ≠ 0 := by
    intro hzero
    apply hq0
    calc
      1 - 2 * m v / r v = (r v - 2 * m v) / r v := by field_simp
      _ = 0 := by rw [hzero]; simp
  convert hlam.div hq hq0 using 1
  field_simp [hr0, hN0, hq0, hgap]
  ring

/-- A bounded nonnegative flux prevents a positive incoming quotient from
collapsing along a finite incoming segment. This derivative form is used
without taking logarithms at the initial edge. -/
theorem incoming_quotient_lower_of_flux_bound
    {a b C : ℝ} {κ G : ℝ → ℝ}
    (hab : a ≤ b)
    (hκcont : ContinuousOn κ (Set.Icc a b))
    (hκpos : ∀ u ∈ Set.Icc a b, 0 < κ u)
    (hG : ∀ u ∈ Set.Ioo a b, G u ≤ C)
    (hκderiv : ∀ u ∈ Set.Ioo a b,
      HasDerivAt κ (-(G u * κ u)) u) :
    ∀ u ∈ Set.Icc a b,
      κ a * Real.exp (-(C * (u - a))) ≤ κ u := by
  let F : ℝ → ℝ := fun u => κ u * Real.exp (C * (u - a))
  have hEcont : Continuous (fun u : ℝ => Real.exp (C * (u - a))) := by fun_prop
  have hFcont : ContinuousOn F (Set.Icc a b) :=
    hκcont.mul hEcont.continuousOn
  have hFderiv (u : ℝ) (hu : u ∈ Set.Ioo a b) :
      HasDerivAt F
        (Real.exp (C * (u - a)) * (κ u * (C - G u))) u := by
    have hinner : HasDerivAt (fun t : ℝ => C * (t - a)) C u := by
      simpa only [smul_eq_mul, mul_one, id_eq] using
        (HasDerivAt.const_mul C ((hasDerivAt_id u).sub_const a))
    have hExp : HasDerivAt (fun t : ℝ => Real.exp (C * (t - a)))
        (Real.exp (C * (u - a)) * C) u := hinner.exp
    convert (hκderiv u hu).mul hExp using 1; ring
  have hFdiff : DifferentiableOn ℝ F (interior (Set.Icc a b)) := by
    intro u hu
    have hd := (hFderiv u (by simpa only [interior_Icc] using hu)).differentiableAt
    exact hd.differentiableWithinAt
  have hFnonneg : ∀ u ∈ interior (Set.Icc a b), 0 ≤ deriv F u := by
    intro u hu
    have hu' : u ∈ Set.Ioo a b := by simpa only [interior_Icc] using hu
    rw [(hFderiv u hu').deriv]
    exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (hκpos u ⟨hu'.1.le, hu'.2.le⟩).le
      (sub_nonneg.mpr (hG u hu')))
  have hFmono := monotoneOn_of_deriv_nonneg (convex_Icc a b)
    hFcont hFdiff hFnonneg
  intro u hu
  have hFa : F a ≤ F u := hFmono ⟨le_rfl, hab⟩ hu hu.1
  have hFa' : κ a ≤ κ u * Real.exp (C * (u - a)) := by
    simpa only [F, sub_self, mul_zero, Real.exp_zero, mul_one] using hFa
  calc
    κ a * Real.exp (-(C * (u - a))) ≤
        (κ u * Real.exp (C * (u - a))) * Real.exp (-(C * (u - a))) :=
      mul_le_mul_of_nonneg_right hFa' (Real.exp_nonneg _)
    _ = κ u := by rw [mul_assoc, ← Real.exp_add]; simp

end ChristodoulouBV.Uniqueness

end
