module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceUnconditional
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceFamilyGap
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceExpansion
import ChristodoulouBV.Uniqueness.ExtensionStarTraceAllMass
import ChristodoulouBV.Uniqueness.ExtensionIncomingRadius
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform bound for the incoming mixed coefficient

The cubic mass estimate bounds `μ/((1-μ)r)` on the full strict old union.
The bound is independent of the finite member's cutoff.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A cutoff-independent bound for the nonnegative coefficient
`μ/((1-μ)r)` in the incoming `λᵥ` equation. -/
theorem exists_uniform_mixed_coefficient_bound_before_star
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε1 : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 < u → u < v → v < b →
          0 ≤ (2 * (S b).m u v / (S b).r u v) /
            ((1 - 2 * (S b).m u v / (S b).r u v) *
              (S b).r u v) ∧
          (2 * (S b).m u v / (S b).r u v) /
            ((1 - 2 * (S b).m u v / (S b).r u v) *
              (S b).r u v) ≤ D := by
  have hεlt : ε < 1 := by
    obtain ⟨ε₁, heq, _, hε₁one, _, _, _, _⟩ := universal_epsilon_choice
    exact (show ε < ε₁ by simpa only [heq] using hε1).trans hε₁one
  have hIncoming := incoming_weighted_bound_before_star
    hu₀.1 hu₀.2 hεlt (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hα hfamily htail
  have hε0 : 0 ≤ ε := tail_mass_upper_nonneg hu₀ hfamily htail
  obtain ⟨B, _, _, _, _, hmass⟩ :=
    exists_uniform_scalar_and_cubic_mass_bounds_on_old_union_of_incoming_bddAbove
      hu₀ hα hfamily hε0 hε1 htail hIncoming
  obtain ⟨q, hq, hgap⟩ :=
    exists_mass_gap_floor_before_star hu₀ hα hfamily hεlt htail
  let R : ℝ := vStar / 2
  let D : ℝ := B ^ 2 / (12 * q) * R
  have hR : 0 ≤ R := by dsimp [R]; linarith only [hu₀.1, hu₀.2]
  have hfactor : 0 ≤ B ^ 2 / (12 * q) := by positivity
  refine ⟨D, mul_nonneg hfactor hR, ?_⟩
  intro b hb u v hu huv hvb
  let H := (hfamily b hb).1
  have hpU : (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hu.le, huv, hvb⟩
  have hr : 0 < (S b).r u v := H.solution.radius_pos (u, v) hpU
  have hμ : 0 ≤ 2 * (S b).m u v / (S b).r u v :=
    H.mass_ratio_nonneg_of_c1 hpU
  have hqpoint := hgap b hb u v hu.le huv hvb
  have hrad : (S b).r u v ≤ (S b).r 0 v :=
    radius_antitone_on_incoming_of_c1 H (le_refl 0) hu.le huv hvb
  have hinit : (S b).r 0 v = v / 2 :=
    ((hfamily b hb).2 v ⟨hu.trans huv, hvb⟩).1
  have hradR : (S b).r u v ≤ R := by
    rw [hinit] at hrad
    dsimp [R]
    linarith only [hrad, hvb, hb.2]
  constructor
  · exact div_nonneg hμ (mul_nonneg (hq.trans_le hqpoint).le hr.le)
  · have hmasspoint := hmass b hb u v hu huv hvb
    have hmasspoint' : 2 * (S b).m u v / (S b).r u v ≤
        B ^ 2 * (S b).r u v ^ 2 / 12 := by
      convert hmasspoint using 1
      ring
    have hcoeff := mass_ratio_coefficient_le_linear_radius
      hr hq hqpoint hmasspoint'
    exact hcoeff.trans (mul_le_mul_of_nonneg_left hradR hfactor)

end ChristodoulouBV.Uniqueness

end
