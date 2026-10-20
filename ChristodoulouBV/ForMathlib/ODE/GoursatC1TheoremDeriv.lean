module

public import ChristodoulouBV.ForMathlib.ODE.GoursatC1
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# State Lipschitz bounds from full derivatives

The state derivative of a parameter-dependent map is the restriction of its
full derivative to the state inclusion. A uniform bound on that restriction
gives the Lipschitz estimate used by the ball fixed point.
-/

public section

namespace Goursat

variable {S T : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- A uniform state-direction bound for the full derivative gives the
state Lipschitz bound on a closed ball. -/
theorem dist_nonlinearity_le_of_full_deriv_state_le
    (f : ℝ × ℝ → S → T)
    (D : ((ℝ × ℝ) × S) → ((ℝ × ℝ) × S) →L[ℝ] T)
    (p : ℝ × ℝ) (c : S) (ρ : ℝ) (κ : NNReal)
    (hderiv : ∀ z, dist z c ≤ ρ →
      HasFDerivAt f.uncurry (D (p, z)) (p, z))
    (hbound : ∀ z, dist z c ≤ ρ → ∀ w : S,
      ‖D (p, z) ((0, 0), w)‖ ≤ (κ : ℝ) * ‖w‖)
    {z z' : S} (hz : dist z c ≤ ρ) (hz' : dist z' c ≤ ρ) :
    dist (f p z) (f p z') ≤ (κ : ℝ) * dist z z' := by
  have hdiff : ∀ w, dist w c ≤ ρ → DifferentiableAt ℝ (f p) w := by
    intro w hw
    have hpart : HasFDerivAt (f p)
        ((D (p, w)).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) S)) w := by
      simpa only [Function.uncurry, Function.comp_def] using
        (hderiv w hw).comp w (hasFDerivAt_prodMk_right p w)
    exact hpart.differentiableAt
  have hnorm : ∀ w, dist w c ≤ ρ → ‖fderiv ℝ (f p) w‖ ≤ (κ : ℝ) := by
    intro w hw
    have hpart : HasFDerivAt (f p)
        ((D (p, w)).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) S)) w := by
      simpa only [Function.uncurry, Function.comp_def] using
        (hderiv w hw).comp w (hasFDerivAt_prodMk_right p w)
    rw [hpart.fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ κ.coe_nonneg
    intro t
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, Prod.mk_zero_zero] using
      hbound w hw t
  let U : Set S := {w | dist w c ≤ ρ}
  have hconv : Convex ℝ U := convex_closedBall c ρ
  have h := hconv.norm_image_sub_le_of_norm_fderiv_le
    (f := f p) (C := (κ : ℝ)) (fun w hw => hdiff w hw)
    (fun w hw => hnorm w hw) hz' hz
  simpa only [dist_eq_norm] using h

end Goursat

end
