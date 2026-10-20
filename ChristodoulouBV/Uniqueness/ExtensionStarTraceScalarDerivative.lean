module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceAllMass
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceFamilyNu
import ChristodoulouBV.Uniqueness.ExtensionStarTraceUnconditional
import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarTransport
import ChristodoulouBV.Uniqueness.ExtensionIncomingSigns
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Uniform outgoing scalar derivative bounds

The linear-radius estimate for `θ/λ` makes `θ/r`, hence the outgoing
derivatives of `φ` and `ζ`, uniformly bounded before the terminal edge.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A linear-radius quotient bound and `λ ≤ 1/2` bound `θ/r` uniformly. -/
theorem theta_over_radius_abs_le_quarter
    {theta lam r B : ℝ} (hr : 0 < r) (hlam : 0 < lam)
    (hlamHalf : lam ≤ 1 / 2) (hB : 0 ≤ B)
    (hquot : |theta / lam| ≤ B / 2 * r) :
    |theta / r| ≤ B / 4 := by
  have htheta : |theta| = |theta / lam| * lam := by
    rw [abs_div, abs_of_pos hlam]
    field_simp [ne_of_gt hlam]
  have hθbound : |theta| ≤ B / 4 * r := by
    calc
      |theta| = |theta / lam| * lam := htheta
      _ ≤ (B / 2 * r) * lam :=
        mul_le_mul_of_nonneg_right hquot hlam.le
      _ ≤ (B / 2 * r) * (1 / 2) := by
        exact mul_le_mul_of_nonneg_left hlamHalf
          (mul_nonneg (div_nonneg hB (by norm_num)) hr.le)
      _ = B / 4 * r := by ring
  rw [abs_div, abs_of_pos hr]
  exact (div_le_iff₀ hr).2 hθbound

/-- The scalar outgoing derivative coefficients are bounded uniformly on
the strict old union, independent of the finite cutoff. -/
theorem exists_uniform_scalar_outgoing_derivative_bounds_before_star
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
    ∃ B N : ℝ, 0 ≤ B ∧ 0 ≤ N ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 < u → u < v → v < b →
          |(S b).theta u v / (S b).r u v| ≤ B / 4 ∧
          |deriv ((S b).zeta u) v| ≤ N * B / 4 := by
  have hεlt : ε < 1 := by
    obtain ⟨ε₁, heq, _, hε₁one, _, _, _, _⟩ := universal_epsilon_choice
    exact (show ε < ε₁ by simpa only [heq] using hε1).trans hε₁one
  have hIncoming := incoming_weighted_bound_before_star
    hu₀.1 hu₀.2 hεlt (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hα hfamily htail
  have hε0 : 0 ≤ ε := tail_mass_upper_nonneg hu₀ hfamily htail
  obtain ⟨B, hB, _, hθ, _, _⟩ :=
    exists_uniform_scalar_and_cubic_mass_bounds_on_old_union_of_incoming_bddAbove
      hu₀ hα hfamily hε0 hε1 htail hIncoming
  obtain ⟨N, hN, hNu⟩ :=
    exists_nu_bound_before_star_from_cubic_mass
      hu₀ hα hfamily hε1 htail
  refine ⟨B, N, hB, hN, ?_⟩
  intro b hb u v hu huv hvb
  let H := (hfamily b hb).1
  have hpU : (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hu.le, huv, hvb⟩
  have hp : (u, v) ∈ openDevelopment 0 b :=
    ⟨⟨hu, huv.trans hvb⟩, ⟨huv, hvb⟩⟩
  have hr : 0 < (S b).r u v := H.solution.radius_pos (u, v) hpU
  have hlam : 0 < (S b).lam u v := H.solution.lam_pos (u, v) hpU
  have hlamHalf : (S b).lam u v ≤ 1 / 2 :=
    lam_le_half_of_initial_gauge H
      (fun w hw => ((hfamily b hb).2 w hw).1)
      hu.le huv hvb
  have hθr := theta_over_radius_abs_le_quarter hr hlam hlamHalf hB
    (hθ b hb u v hu huv hvb)
  constructor
  · exact hθr
  · rw [(zeta_hasDerivAt_v_of_c1 H hp).deriv, abs_neg]
    have hν := hNu b hb u v hu.le huv hvb
    have hprod : |(S b).nu u v *
        ((S b).theta u v / (S b).r u v)| ≤ N * (B / 4) := by
      rw [abs_mul]
      exact mul_le_mul hν hθr (abs_nonneg _) hN
    simpa only [mul_div_assoc] using hprod

end ChristodoulouBV.Uniqueness

end
