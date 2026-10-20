module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceLambdaVMixed
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceLambdaVBoundAlgebra
import ChristodoulouBV.Uniqueness.ExtensionStarTraceLambdaVFieldCoefficient
import Mathlib.Tactic.Ring

/-!
# Linear form of the incoming lambda derivative equation

The source formula for equation (10) is regrouped by its unknown `λᵥ`.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Equation (10) in linear form, with the actual outgoing derivative of
`μ/((1-μ)r)` as its forcing coefficient. -/
theorem lambda_v_hasDerivAt_u_linear_of_c1
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openDevelopment 0 b) :
    HasDerivAt (fun s => deriv (S.lam s) v)
      (((S.nu u v * S.lam u v *
          ((2 * S.m u v / S.r u v) /
            ((1 - 2 * S.m u v / S.r u v) * S.r u v))) *
          S.lam u v + S.nu u v * deriv (S.lam u) v) *
          ((2 * S.m u v / S.r u v) /
            ((1 - 2 * S.m u v / S.r u v) * S.r u v)) +
        S.nu u v * S.lam u v *
          deriv (fun t =>
            (2 * S.m u t / S.r u t) /
              ((1 - 2 * S.m u t / S.r u t) * S.r u t)) v) u := by
  have hp0 := hp
  have hcoeff := (mixed_coefficient_hasDerivAt_v_of_c1 H hp).deriv
  have h := lambda_v_hasDerivAt_u_of_c1 H hp0
  rw [hcoeff]
  convert h using 1
  ring

end ChristodoulouBV.Uniqueness

end
