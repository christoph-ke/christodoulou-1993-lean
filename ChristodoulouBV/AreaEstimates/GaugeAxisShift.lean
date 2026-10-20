module

public import ChristodoulouBV.Frozen.IsC1Solution
import Mathlib.Tactic

/-!
# Constant scalar shifts

The reduced scalar shift changes both scalar-radius derivatives. It preserves
the two scalar amplitudes exactly and therefore preserves the gravitational
equations. This is the normalization used in Sections 4 and 6.
-/

@[expose] public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV

/-- Add the constant `c` to the scalar field, including the induced changes
to the two derivatives of `r φ`. -/
def scalarShift (S : Fields) (c : ℝ) : Fields where
  r := S.r
  phi := fun u v => S.phi u v + c
  m := S.m
  lam := S.lam
  nu := S.nu
  alpha := fun u v => S.alpha u v + c * S.lam u v
  beta := fun u v => S.beta u v + c * S.nu u v

/-- The scalar shift leaves the radius fixed. -/
theorem scalarShift_r (S : Fields) (c : ℝ) :
    (scalarShift S c).r = S.r := by
  rfl

/-- Adding a constant leaves extended total variation unchanged. -/
theorem eVariationOn_add_const_real (f : ℝ → ℝ) (d : ℝ)
    (s : Set ℝ) :
    eVariationOn (fun x => f x + d) s = eVariationOn f s := by
  simp only [eVariationOn]
  congr 1
  ext p
  apply Finset.sum_congr rfl
  intro i hi
  simp only [edist_dist, dist_add_right]

/-- A scalar shift leaves the outgoing scalar amplitude unchanged. -/
theorem scalarShift_theta (S : Fields) (c u v : ℝ) :
    (scalarShift S c).theta u v = S.theta u v := by
  simp only [Fields.theta, scalarShift]
  ring

/-- A scalar shift leaves the incoming scalar amplitude unchanged. -/
theorem scalarShift_zeta (S : Fields) (c u v : ℝ) :
    (scalarShift S c).zeta u v = S.zeta u v := by
  simp only [Fields.zeta, scalarShift]
  ring

private theorem intervalPrimitive_add_const_mul
    {f g h k : ℝ → ℝ} {a b c : ℝ}
    (hf : IntervalPrimitive f h a b)
    (hg : IntervalPrimitive g k a b) :
    IntervalPrimitive (fun t => f t + c * g t)
      (fun t => h t + c * k t) a b := by
  rcases hf with ⟨hfint, hfeq⟩
  rcases hg with ⟨hgint, hgeq⟩
  refine ⟨hfint.add (hgint.const_mul c), ?_⟩
  rw [intervalIntegral.integral_add hfint (hgint.const_mul c),
    intervalIntegral.integral_const_mul]
  rw [← hfeq, ← hgeq]
  ring

/-- The integrated reduced equations are invariant under the scalar shift. -/
theorem IsSolution.scalarShift {U : Set (ℝ × ℝ)} {S : Fields}
    (H : IsSolution U S) (c : ℝ) :
    IsSolution U (scalarShift S c) := by
  refine {
    development := H.development
    radius_out := ?_
    radius_in := ?_
    scalar_radius_out := ?_
    scalar_radius_in := ?_
    mass_out := ?_
    mass_in := ?_
    lam_in := ?_
    nu_out := ?_
    alpha_in := ?_
    beta_out := ?_
    radius_axis := ?_
    mass_axis := ?_
    radius_pos := ?_
    lam_pos := ?_
    conformal := ?_ }
  · intro u a b hab hseg
    exact H.radius_out u a b hab hseg
  · intro v a b hab hseg
    exact H.radius_in v a b hab hseg
  · intro u a b hab hseg
    have h := intervalPrimitive_add_const_mul (c := c)
      (H.scalar_radius_out u a b hab hseg) (H.radius_out u a b hab hseg)
    change IntervalPrimitive (fun v => S.r u v * (S.phi u v + c))
      (fun v => S.alpha u v + c * S.lam u v) a b
    have heq : (fun v => S.r u v * (S.phi u v + c)) =
        (fun v => S.r u v * S.phi u v + c * S.r u v) := by
      funext v
      ring
    rw [heq]
    exact h
  · intro v a b hab hseg
    have h := intervalPrimitive_add_const_mul (c := c)
      (H.scalar_radius_in v a b hab hseg) (H.radius_in v a b hab hseg)
    change IntervalPrimitive (fun u => S.r u v * (S.phi u v + c))
      (fun u => S.beta u v + c * S.nu u v) a b
    have heq : (fun u => S.r u v * (S.phi u v + c)) =
        (fun u => S.r u v * S.phi u v + c * S.r u v) := by
      funext u
      ring
    rw [heq]
    exact h
  · intro u a b hab hseg
    change IntervalPrimitive (S.m u)
      (fun v => (1 - 2 * S.m u v / S.r u v) *
        ((ChristodoulouBV.scalarShift S c).theta u v)^2 / (2 * S.lam u v)) a b
    simpa only [scalarShift_theta] using H.mass_out u a b hab hseg
  · intro v a b hab hseg
    change IntervalPrimitive (fun u => S.m u v)
      (fun u => (1 - 2 * S.m u v / S.r u v) *
        ((ChristodoulouBV.scalarShift S c).zeta u v)^2 / (2 * S.nu u v)) a b
    simpa only [scalarShift_zeta] using H.mass_in v a b hab hseg
  · intro v a b hab hseg
    exact H.lam_in v a b hab hseg
  · intro u a b hab hseg
    exact H.nu_out u a b hab hseg
  · intro v a b hab hseg
    have h := intervalPrimitive_add_const_mul (c := c)
      (H.alpha_in v a b hab hseg) (H.lam_in v a b hab hseg)
    change IntervalPrimitive (fun u => S.alpha u v + c * S.lam u v)
      (fun u => ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v)) * (S.phi u v + c)) a b
    convert h using 1
    funext t
    ring
  · intro u a b hab hseg
    have h := intervalPrimitive_add_const_mul (c := c)
      (H.beta_out u a b hab hseg) (H.nu_out u a b hab hseg)
    change IntervalPrimitive (fun v => S.beta u v + c * S.nu u v)
      (fun v => ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v)) * (S.phi u v + c)) a b
    convert h using 1
    funext t
    ring
  · exact H.radius_axis
  · exact H.mass_axis
  · exact H.radius_pos
  · exact H.lam_pos
  · exact H.conformal

/-- The frozen C¹ class is invariant under a constant scalar shift. -/
theorem IsC1Solution.scalarShift {U : Set (ℝ × ℝ)} {S : Fields}
    (H : IsC1Solution U S) (c : ℝ) :
    IsC1Solution U (scalarShift S c) := by
  refine {
    solution := H.solution.scalarShift c
    nu_bounded_below := H.nu_bounded_below
    lam_bounded_below := H.lam_bounded_below
    lam_c1 := H.lam_c1
    nu_c1 := H.nu_c1
    phi_c1 := ?_
    theta_c1 := ?_
    zeta_c1 := ?_ }
  · exact H.phi_c1.add contDiffOn_const
  · simpa only [scalarShift_theta] using H.theta_c1
  · simpa only [scalarShift_zeta] using H.zeta_c1

/-- Undoing a scalar shift recovers every field, including both scalar-radius
derivatives. -/
theorem scalarShift_neg (S : Fields) (c : ℝ) :
    scalarShift (scalarShift S c) (-c) = S := by
  cases S with
  | mk r phi m lam nu alpha beta =>
    dsimp [scalarShift]
    congr 1 <;> try rfl
    · funext u v
      ring
    · funext u v
      ring
    · funext u v
      ring

end ChristodoulouBV

end
