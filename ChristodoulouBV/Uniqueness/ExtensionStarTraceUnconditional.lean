module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceUniformScalar
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceMass
public import ChristodoulouBV.Uniqueness.ExtensionIncomingWeighted
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import Mathlib.Tactic.Linarith

/-!
# Unconditional old-development estimates before the terminal edge

The incoming strip estimate supplies the incoming weighted bound from the original family and tail
premises. These statements remove that auxiliary hypothesis from the
unweighted scalar and cubic mass estimates used in the terminal trace.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- An upper mass-ratio bound on the nonempty terminal tail is necessarily
nonnegative. Thus the sign premise used by the absorption estimate is a
consequence of the original family and tail hypotheses. -/
theorem tail_mass_upper_nonneg
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    0 ≤ ε := by
  let u := (u₀ + vStar) / 2
  let v := (u + vStar) / 2
  let b := (v + vStar) / 2
  have hu₀u : u₀ < u := by dsimp [u]; linarith only [hu₀.2]
  have huv : u < v := by dsimp [v, u]; linarith only [hu₀.2]
  have hvb : v < b := by dsimp [b, v, u]; linarith only [hu₀.2]
  have hbStar : b < vStar := by dsimp [b, v, u]; linarith only [hu₀.2]
  have hb : b ∈ Ioo (0 : ℝ) vStar :=
    ⟨hu₀.1.trans (hu₀u.trans (huv.trans hvb)), hbStar⟩
  have hp : (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hu₀.1.le.trans hu₀u.le, huv, hvb⟩
  have hdev : (u, v) ∈ openDevelopment u₀ vStar :=
    ⟨⟨hu₀u, huv.trans (hvb.trans hbStar)⟩,
      ⟨huv, hvb.trans hbStar⟩⟩
  have hμ := (hfamily b hb).1.mass_ratio_nonneg_of_c1 hp
  exact hμ.trans (htail b hb (u, v) ⟨hdev, hp⟩)

/-- The first radius improvement, `m ≤ A²r²/9`, follows from the frozen
family and tail premises because the incoming strip estimate supplies the incoming bound. -/
theorem exists_uniform_quadratic_mass_bound_before_star
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
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, u₀ < u → u < v → v < b →
          (S b).m u v ≤ A ^ 2 / 9 * ((S b).r u v) ^ 2 := by
  obtain ⟨ε₁, heq, _, hε₁one, _, _, _, _⟩ := universal_epsilon_choice
  have hεlt : ε < 1 :=
    (show ε < ε₁ by simpa only [heq] using hε1).trans hε₁one
  have hIncoming := incoming_weighted_bound_before_star
    hu₀.1 hu₀.2 hεlt (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hα hfamily htail
  have hε0 : 0 ≤ ε := tail_mass_upper_nonneg hu₀ hfamily htail
  exact exists_uniform_quadratic_mass_bound_before_star_of_incoming_bddAbove
    hu₀ hα hfamily hε0 hε1 htail hIncoming

/-- The incoming bound required in the unweighted alpha-prime bootstrap is
already a consequence of the original small-tail hypotheses. -/
theorem exists_uniform_alphaPrime_bound_before_star
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
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, u₀ < u → u < v → v < b →
          |deriv (fun t => (S b).alpha u t / (S b).lam u t) v /
            (S b).lam u v| ≤ B := by
  have hεlt : ε < 1 := by
    obtain ⟨ε₁, heq, _, hε₁one, _, _, _, _⟩ := universal_epsilon_choice
    exact (show ε < ε₁ by simpa only [heq] using hε1).trans hε₁one
  have hIncoming := incoming_weighted_bound_before_star
    hu₀.1 hu₀.2 hεlt (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hα hfamily htail
  have hε0 : 0 ≤ ε := tail_mass_upper_nonneg hu₀ hfamily htail
  exact exists_uniform_alphaPrime_bound_before_star_of_incoming_bddAbove
    hu₀ hα hfamily hε0 hε1 htail hIncoming

/-- The scalar quotient is linear in radius, while mass and mass ratio have
cubic and quadratic bounds, with constants independent of the cutoff. -/
theorem exists_uniform_scalar_and_cubic_mass_bounds_before_star
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
  have hεlt : ε < 1 := by
    obtain ⟨ε₁, heq, _, hε₁one, _, _, _, _⟩ := universal_epsilon_choice
    exact (show ε < ε₁ by simpa only [heq] using hε1).trans hε₁one
  have hIncoming := incoming_weighted_bound_before_star
    hu₀.1 hu₀.2 hεlt (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hα hfamily htail
  have hε0 : 0 ≤ ε := tail_mass_upper_nonneg hu₀ hfamily htail
  exact exists_uniform_scalar_and_cubic_mass_bounds_before_star_of_incoming_bddAbove
    hu₀ hα hfamily hε0 hε1 htail hIncoming

end ChristodoulouBV.Uniqueness

end
