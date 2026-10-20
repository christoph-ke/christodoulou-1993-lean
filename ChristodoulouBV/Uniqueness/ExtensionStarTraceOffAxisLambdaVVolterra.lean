module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisCoefficients
public import ChristodoulouBV.ForMathlib.IntervalIntegral.ParametricVolterraODE
import ChristodoulouBV.Uniqueness.ExtensionStarTraceLambdaVLinear
import ChristodoulouBV.Uniqueness.ExtensionStarTraceLambdaVFieldCoefficient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Parametric Volterra continuation of the outgoing expansion derivative

Equation (10) is linear in `λᵥ`, has zero initial value, and has coefficients
continuous on the closed off-axis rectangle.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Equation (10) extends `λᵥ` jointly to a closed off-axis rectangle. -/
theorem exists_lambdaV_terminal_trace_on_rectangle
    {alpha₀ : ℝ → ℝ} {vStar a vBar : ℝ} {S : ℝ → Fields}
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (T : OffAxisTerminalTraces a vBar vStar S) :
    ∃ L : ℝ × ℝ → ℝ,
      ContinuousOn L (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar vStar,
        L (u, v) = deriv ((S ((v + vStar) / 2)).lam u) v := by
  let cutoff : ℝ → ℝ := fun v => (v + vStar) / 2
  let y : ℝ × ℝ → ℝ := fun p => deriv ((S (cutoff p.2)).lam p.1) p.2
  have hcutoff (v : ℝ) (hv : v ∈ Ico vBar vStar) :
      cutoff v ∈ Ioo (0 : ℝ) vStar ∧ v < cutoff v := by
    dsimp [cutoff]
    constructor
    · constructor
      · linarith only [ha, haBar, hv.1, hv.2]
      · linarith only [hv.2]
    · linarith only [hv.2]
  obtain ⟨L, hL, hLmatch⟩ :=
    intervalIntegral.exists_continuousOn_closed_rectangle_of_linear_ode
      (y := y) (a := T.lambdaVCoefficient)
      (b := T.lambdaVSource) (y₀ := fun _ => 0)
      (le_of_lt ha) hBarStar
      (T.coefficients_continuousOn.2.2.1)
      (T.coefficients_continuousOn.2.2.2)
      continuousOn_const
      (by
        intro v hv
        obtain ⟨hbc, hvc⟩ := hcutoff v hv
        exact lambda_v_continuousOn_incoming_of_c1
          (hfamily (cutoff v) hbc).1 ha.le
          (haBar.trans_le hv.1) hvc)
      (by
        intro v hv
        obtain ⟨hbc, hvc⟩ := hcutoff v hv
        change deriv ((S (cutoff v)).lam 0) v = 0
        exact lambda_v_initial_eq_zero_of_gauge
          (hfamily (cutoff v) hbc).1
          (fun w hw => ((hfamily (cutoff v) hbc).2 w hw).1)
          ⟨ha.trans (haBar.trans_le hv.1), hvc⟩)
      (by
        intro v hv u hu
        obtain ⟨hbc, hvc⟩ := hcutoff v hv
        have huv : u < v := hu.2.trans (haBar.trans_le hv.1)
        have hp : (u, v) ∈ openDevelopment 0 (cutoff v) :=
          ⟨⟨hu.1, huv.trans hvc⟩, ⟨huv, hvc⟩⟩
        let H := (hfamily (cutoff v) hbc).1
        have hcoeff := T.coefficients_match_old hbc
          ⟨hu.1.le, hu.2.le⟩ ⟨hv.1, hvc⟩
        have hODE := lambda_v_hasDerivAt_u_linear_of_c1 H hp
        have hQv := (mixed_coefficient_hasDerivAt_v_of_c1 H hp).deriv
        rw [hQv] at hODE
        change HasDerivAt (fun s => y (s, v))
          (T.lambdaVCoefficient (u, v) * y (u, v) +
            T.lambdaVSource (u, v)) u
        rw [hcoeff.2.2.1, hcoeff.2.2.2]
        convert hODE using 1 <;> ring)
  refine ⟨L, hL, ?_⟩
  intro u hu v hv
  exact hLmatch u hu v hv

end ChristodoulouBV.Uniqueness

end
