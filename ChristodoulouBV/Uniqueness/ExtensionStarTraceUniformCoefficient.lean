module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceAllMass
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceFamilyGap
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceLambdaVFieldCoefficient
import ChristodoulouBV.Uniqueness.ExtensionIncomingRadius
import ChristodoulouBV.Uniqueness.ExtensionIncomingSigns
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform outgoing derivative of the mixed coefficient

The cubic mass and scalar estimates make the derivative in equation (8)
bounded even as the radius tends to zero. This is the coefficient estimate
needed for the incoming `λᵥ` equation.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Equation (9), uniformly over the compatible old family. The constant
does not depend on the member's cutoff or on the radius. -/
theorem exists_uniform_mixed_coefficient_derivative_bound_of_incoming_bddAbove
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε0 : 0 ≤ ε)
    (hε1 : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε)
    (hIncoming : BddAbove
      (incomingWeightedAlphaPrimeValues u₀ vStar ((1 : ℝ) / 2) S)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 < u → u < v → v < b →
          |deriv (fun t =>
            (2 * (S b).m u t / (S b).r u t) /
              ((1 - 2 * (S b).m u t / (S b).r u t) *
                (S b).r u t)) v| ≤ C := by
  obtain ⟨B, hB, _, hθ, _, hμ⟩ :=
    exists_uniform_scalar_and_cubic_mass_bounds_on_old_union_of_incoming_bddAbove
      hu₀ hα hfamily hε0 hε1 htail hIncoming
  have hεlt : ε < 1 := by
    obtain ⟨ε₁, heq, _, hε₁one, _, _, _, _⟩ := universal_epsilon_choice
    exact (show ε < ε₁ by simpa only [heq] using hε1).trans hε₁one
  obtain ⟨q, hq, hgap⟩ :=
    exists_mass_gap_floor_before_star hu₀ hα hfamily hεlt htail
  let C : ℝ := B ^ 2 / (8 * q) +
    B ^ 2 * (1 / q ^ 2 + 1 / q) / 24
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro b hb u v hu huv hvb
  let H := (hfamily b hb).1
  have hpU : (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hu.le, huv, hvb⟩
  have hp : (u, v) ∈ openDevelopment 0 b :=
    ⟨⟨hu, huv.trans hvb⟩, ⟨huv, hvb⟩⟩
  have hr : 0 < (S b).r u v := H.solution.radius_pos (u, v) hpU
  have hl0 : 0 ≤ (S b).lam u v := (H.solution.lam_pos (u, v) hpU).le
  have hl : (S b).lam u v ≤ 1 / 2 :=
    lam_le_half_of_initial_gauge H
      (fun w hw => ((hfamily b hb).2 w hw).1) hu.le huv hvb
  have hμ0 : 0 ≤ 2 * (S b).m u v / (S b).r u v :=
    (H.reduced_signs_of_c1 hpU).2.2.1
  have hμpoint : 2 * (S b).m u v / (S b).r u v ≤
      B ^ 2 * (S b).r u v ^ 2 / 12 := by
    convert hμ b hb u v hu huv hvb using 1
    ring
  have hθpoint : |(S b).theta u v / (S b).lam u v| ≤
      B * (S b).r u v / 2 := by
    convert hθ b hb u v hu huv hvb using 1
    ring
  have hcoeff := mass_ratio_coefficient_derivative_abs_le
    hr hl0 hl hμ0 hq (hgap b hb u v hu.le huv hvb)
    hB hμpoint hθpoint
  have hderiv := (mixed_coefficient_hasDerivAt_v_of_c1 H hp).deriv
  rw [hderiv]
  exact hcoeff

end ChristodoulouBV.Uniqueness

end
