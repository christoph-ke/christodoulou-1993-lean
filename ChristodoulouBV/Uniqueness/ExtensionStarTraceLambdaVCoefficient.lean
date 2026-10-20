module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceLambdaVAlgebra
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Differentiating the mixed coefficient in the outgoing direction

This is the ordinary one-variable chain rule for the outgoing derivative of
`μ / ((1-μ) r)` in the terminal trace calculation. The mass-ratio evolution removes the derivative of mass.
-/

public section

namespace ChristodoulouBV.Uniqueness

/-- Equation (8): the outgoing derivative of `μ / ((1-μ)r)` in terms of
`λ`, `μ`, and the scalar quotient. -/
theorem mass_ratio_coefficient_hasDerivAt
    {r μ : ℝ → ℝ} {v lam f : ℝ}
    (hr : 0 < r v) (hq : 0 < 1 - μ v)
    (hrv : HasDerivAt r lam v)
    (hμv : HasDerivAt μ
      ((1 - μ v) * lam * f ^ 2 / r v - μ v * lam / r v) v) :
    HasDerivAt (fun t => μ t / ((1 - μ t) * r t))
      (lam * f ^ 2 / ((1 - μ v) * (r v) ^ 2) -
        μ v * lam * (1 / (1 - μ v) ^ 2 + 1 / (1 - μ v)) /
          (r v) ^ 2) v := by
  have hden : (1 - μ v) * r v ≠ 0 :=
    ne_of_gt (mul_pos hq hr)
  have hqv := (hasDerivAt_const v (1 : ℝ)).sub hμv
  have hdenv := hqv.mul hrv
  have hd := hμv.div hdenv hden
  dsimp only [Pi.sub_apply, Pi.mul_apply, Pi.div_apply] at hd
  convert hd using 1
  field_simp [ne_of_gt hr, ne_of_gt hq]
  ring

end ChristodoulouBV.Uniqueness

end
