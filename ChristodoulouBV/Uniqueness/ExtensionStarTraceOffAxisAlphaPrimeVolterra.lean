module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisCoefficients
public import ChristodoulouBV.ForMathlib.IntervalIntegral.ParametricVolterraODE
import ChristodoulouBV.Uniqueness.ExtensionIncomingPrimeContinuity
import ChristodoulouBV.Uniqueness.ExtensionTransportEquation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.Linarith

/-!
# Parametric Volterra continuation of the outgoing scalar derivative

Equation (5.2) is linear in `α′`; its closed-rectangle coefficients and the
initial derivative of the prescribed data give a joint terminal trace.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Equation (5.2) extends the coordinate expression for `α′` jointly to a
closed off-axis rectangle. The expression below the top is evaluated on the
canonical member with cutoff `(v+vStar)/2`. -/
theorem exists_alphaPrime_terminal_trace_on_rectangle
    {alpha₀ : ℝ → ℝ} {vStar a vBar : ℝ} {S : ℝ → Fields}
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (T : OffAxisTerminalTraces a vBar vStar S) :
    ∃ P : ℝ × ℝ → ℝ,
      ContinuousOn P (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar vStar,
        P (u, v) =
          deriv (fun t =>
            (S ((v + vStar) / 2)).alpha u t /
              (S ((v + vStar) / 2)).lam u t) v /
            (S ((v + vStar) / 2)).lam u v := by
  let cutoff : ℝ → ℝ := fun v => (v + vStar) / 2
  let y : ℝ × ℝ → ℝ := fun p =>
    deriv (fun t => (S (cutoff p.2)).alpha p.1 t /
      (S (cutoff p.2)).lam p.1 t) p.2 /
      (S (cutoff p.2)).lam p.1 p.2
  have hcutoff (v : ℝ) (hv : v ∈ Ico vBar vStar) :
      cutoff v ∈ Ioo (0 : ℝ) vStar ∧ v < cutoff v := by
    dsimp [cutoff]
    constructor
    · constructor
      · linarith only [ha, haBar, hv.1, hv.2]
      · linarith only [hv.2]
    · linarith only [hv.2]
  have hderiv₀ : ContinuousOn (deriv alpha₀) (Icc vBar vStar) := by
    have hαopen : ContDiffOn ℝ 1 alpha₀ (Ioi 0) :=
      hα.mono (fun _ hv => hv.le)
    exact (hαopen.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono
      (fun v hv => ha.trans (haBar.trans_le hv.1))
  have hseed : ContinuousOn (fun v => 4 * deriv alpha₀ v)
      (Icc vBar vStar) := continuousOn_const.mul hderiv₀
  obtain ⟨P, hP, hPmatch⟩ :=
    intervalIntegral.exists_continuousOn_closed_rectangle_of_linear_ode
      (y := y) (a := T.alphaPrimeCoefficient)
      (b := T.alphaPrimeSource)
      (y₀ := fun v => 4 * deriv alpha₀ v)
      (le_of_lt ha) hBarStar
      (T.coefficients_continuousOn.1)
      (T.coefficients_continuousOn.2.1)
      hseed
      (by
        intro v hv
        obtain ⟨hbc, hvc⟩ := hcutoff v hv
        exact alphaPrime_coordinate_continuousOn_incoming_of_c1
          (hfamily (cutoff v) hbc).1 ha.le
          (haBar.trans_le hv.1) hvc)
      (by
        intro v hv
        obtain ⟨hbc, hvc⟩ := hcutoff v hv
        change deriv (fun t => (S (cutoff v)).alpha 0 t /
            (S (cutoff v)).lam 0 t) v /
          (S (cutoff v)).lam 0 v = 4 * deriv alpha₀ v
        exact initial_alphaPrime_formula
          (hfamily (cutoff v) hbc).1 hα (hfamily (cutoff v) hbc).2
          ⟨ha.trans (haBar.trans_le hv.1), hvc⟩)
      (by
        intro v hv u hu
        obtain ⟨hbc, hvc⟩ := hcutoff v hv
        have huv : u < v := hu.2.trans (haBar.trans_le hv.1)
        have hp : (u, v) ∈ openDevelopment 0 (cutoff v) :=
          ⟨⟨hu.1, huv.trans hvc⟩, ⟨huv, hvc⟩⟩
        have hcoeff := T.coefficients_match_old hbc
          ⟨hu.1.le, hu.2.le⟩ ⟨hv.1, hvc⟩
        have hODE := alphaPrime_hasDerivAt_u
          (hfamily (cutoff v) hbc).1 hp
        change HasDerivAt (fun s => y (s, v))
          (T.alphaPrimeCoefficient (u, v) * y (u, v) +
            T.alphaPrimeSource (u, v)) u
        rw [hcoeff.1, hcoeff.2.1]
        convert hODE using 1 <;> ring)
  refine ⟨P, hP, ?_⟩
  intro u hu v hv
  exact hPmatch u hu v hv

end ChristodoulouBV.Uniqueness

end
