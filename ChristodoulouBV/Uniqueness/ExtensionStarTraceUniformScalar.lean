module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceUniformAlphaPrime
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceScalar
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceCubicMass
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Uniform scalar and cubic mass estimates before the terminal edge

The unweighted incoming bootstrap feeds the zero-weight outgoing averaging
identity and then the outgoing mass equation. All constants are shared by
the compatible old family.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The improved scalar quotient and mass bounds from the unweighted
`α′` estimate, uniformly over every earlier family member. -/
theorem exists_uniform_scalar_and_cubic_mass_bounds_before_star_of_incoming_bddAbove
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
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, u₀ < u → u < v → v < b →
          |deriv (fun t => (S b).alpha u t / (S b).lam u t) v /
            (S b).lam u v| ≤ B) ∧
      (∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, u₀ < u → u < v → v < b →
          |(S b).theta u v / (S b).lam u v| ≤
            B / 2 * (S b).r u v) ∧
      (∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, u₀ < u → u < v → v < b →
          (S b).m u v ≤ B ^ 2 / 24 * ((S b).r u v) ^ 3) ∧
      (∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, u₀ < u → u < v → v < b →
          2 * (S b).m u v / (S b).r u v ≤
            B ^ 2 / 12 * ((S b).r u v) ^ 2) := by
  obtain ⟨B, hB0, hprime⟩ :=
    exists_uniform_alphaPrime_bound_before_star_of_incoming_bddAbove
      hu₀ hα hfamily hε0 hε1 htail hIncoming
  have hθ : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ u v : ℝ, u₀ < u → u < v → v < b →
        |(S b).theta u v / (S b).lam u v| ≤
          B / 2 * (S b).r u v := by
    intro b hb u v hu₀u huv hvb
    apply theta_ratio_le_half_radius_of_alphaPrime_bound
      (hfamily b hb).1 (hu₀.1.trans hu₀u) huv hvb hB0
    intro t ht
    exact hprime b hb u t hu₀u ht.1 (ht.2.trans_lt hvb)
  have hm : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ u v : ℝ, u₀ < u → u < v → v < b →
        (S b).m u v ≤ B ^ 2 / 24 * ((S b).r u v) ^ 3 := by
    intro b hb u v hu₀u huv hvb
    have hmass := mass_le_sixth_sq_mul_radius_cubed_of_theta_ratio_le_radius
      (hfamily b hb).1 (hu₀.1.trans hu₀u) huv hvb
      (div_nonneg hB0 (by norm_num : (0 : ℝ) ≤ 2))
      (fun t ht => hθ b hb u t hu₀u ht.1 (ht.2.trans_lt hvb))
    convert hmass using 1
    ring
  refine ⟨B, hB0, hprime, hθ, hm, ?_⟩
  intro b hb u v hu₀u huv hvb
  have hr : 0 < (S b).r u v :=
    (hfamily b hb).1.solution.radius_pos (u, v)
      ⟨(hu₀.1.trans hu₀u).le, huv, hvb⟩
  apply (div_le_iff₀ hr).2
  have hmass := hm b hb u v hu₀u huv hvb
  nlinarith only [hmass]

end ChristodoulouBV.Uniqueness

end
