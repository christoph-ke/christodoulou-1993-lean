module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceUniformCoefficientBase
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceFamilyNu
import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarTransport
import ChristodoulouBV.Uniqueness.ExtensionIncomingSigns
import Mathlib.Tactic.Ring

/-!
# Uniform outgoing derivative of the incoming expansion

The mixed radius coefficient bounds the `νᵥ` equation on the old union.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The outgoing derivative of `ν` is uniformly bounded on the strict old
union, independently of the family cutoff. -/
theorem exists_uniform_nu_outgoing_derivative_bound_before_star
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
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 < u → u < v → v < b →
          |deriv ((S b).nu u) v| ≤ C := by
  obtain ⟨D, hD, hQ⟩ :=
    exists_uniform_mixed_coefficient_bound_before_star
      hu₀ hα hfamily hε1 htail
  obtain ⟨N, hN, hNu⟩ :=
    exists_nu_bound_before_star_from_cubic_mass
      hu₀ hα hfamily hε1 htail
  refine ⟨N * (1 / 2) * D,
    mul_nonneg (mul_nonneg hN (by norm_num)) hD, ?_⟩
  intro b hb u v hu huv hvb
  let H := (hfamily b hb).1
  have hp : (u, v) ∈ openDevelopment 0 b :=
    ⟨⟨hu, huv.trans hvb⟩, ⟨huv, hvb⟩⟩
  have hlam0 : 0 ≤ (S b).lam u v :=
    (H.solution.lam_pos (u, v) ⟨hu.le, huv, hvb⟩).le
  have hlamHalf : (S b).lam u v ≤ 1 / 2 :=
    lam_le_half_of_initial_gauge H
      (fun w hw => ((hfamily b hb).2 w hw).1)
      hu.le huv hvb
  let Q : ℝ :=
    (2 * (S b).m u v / (S b).r u v) /
      ((1 - 2 * (S b).m u v / (S b).r u v) * (S b).r u v)
  have hQ0 : 0 ≤ Q := (hQ b hb u v hu huv hvb).1
  have hQD : Q ≤ D := (hQ b hb u v hu huv hvb).2
  have hν : |(S b).nu u v| ≤ N := hNu b hb u v hu.le huv hvb
  have heq :
      (2 * (S b).m u v / (S b).r u v) *
        (S b).lam u v * (S b).nu u v /
        ((1 - 2 * (S b).m u v / (S b).r u v) * (S b).r u v) =
      (S b).nu u v * (S b).lam u v * Q := by
    dsimp [Q]
    ring
  rw [(nu_hasDerivAt_v_of_c1 H hp).deriv, heq,
    abs_mul, abs_mul, abs_of_nonneg hlam0, abs_of_nonneg hQ0]
  calc
    |(S b).nu u v| * (S b).lam u v * Q ≤
        N * (S b).lam u v * Q := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hν hlam0) hQ0
    _ ≤ N * (1 / 2) * Q := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlamHalf hN) hQ0
    _ ≤ N * (1 / 2) * D := by
      exact mul_le_mul_of_nonneg_left hQD
        (mul_nonneg hN (by norm_num))

end ChristodoulouBV.Uniqueness

end
