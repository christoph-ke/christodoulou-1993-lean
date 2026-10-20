module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceLowerPrime
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceUniformAlphaPrime
import ChristodoulouBV.Uniqueness.ExtensionCutoff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Uniform alpha-prime on the whole compatible old union

The lower off-axis strip is controlled by the incoming strip estimates, its earlier compact part by
one fixed family member, and the upper triangle by the unweighted bootstrap.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The coordinate expression of `α′` has one cutoff-independent bound on
the entire strict old union. This combines the bounded lower strip with the
unweighted terminal bootstrap. -/
theorem exists_uniform_alphaPrime_bound_on_old_union_of_incoming_bddAbove
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
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 < u → u < v → v < b →
          |deriv (fun t => (S b).alpha u t / (S b).lam u t) v /
            (S b).lam u v| ≤ B := by
  let u₁ : ℝ := (u₀ + vStar) / 2
  let vBar : ℝ := (u₁ + vStar) / 2
  have hu₀u₁ : u₀ < u₁ := by dsimp [u₁]; linarith only [hu₀.2]
  have hu₁Bar : u₁ < vBar := by dsimp [vBar, u₁]; linarith only [hu₀.2]
  have hBarStar : vBar < vStar := by dsimp [vBar, u₁]; linarith only [hu₀.2]
  have hεlt : ε < 1 := by
    obtain ⟨ε₁, heq, _, hε₁one, _, _, _, _⟩ := universal_epsilon_choice
    exact (show ε < ε₁ by simpa only [heq] using hε1).trans hε₁one
  obtain ⟨P, hP, hstrip⟩ :=
    exists_alphaPrime_bound_on_lower_terminal_strip
      hu₀.1 hu₀u₁ hu₁Bar hBarStar hεlt hα hfamily htail
  obtain ⟨B₁, hB₁, hupper⟩ :=
    exists_uniform_alphaPrime_bound_before_star_of_incoming_bddAbove
      hu₀ hα hfamily hε0 hε1 htail hIncoming
  obtain ⟨b₀, hb₀, H₀⟩ :=
    exists_family_member_beyond_cutoff (hu₀.1.trans (hu₀u₁.trans hu₁Bar))
      hBarStar hfamily
  have hb₀Star : b₀ ∈ Ioo (0 : ℝ) vStar :=
    ⟨(hu₀.1.trans (hu₀u₁.trans hu₁Bar)).trans hb₀.1, hb₀.2⟩
  let T : ℝ := (vBar + b₀) / 2
  have hBarT : vBar < T := by dsimp [T]; linarith only [hb₀.1]
  have hTb₀ : T < b₀ := by dsimp [T]; linarith only [hb₀.1]
  obtain ⟨M, hM, hcompact⟩ :=
    exists_weighted_alphaPrime_bound_on_finite_member
      (hu₀.1.trans (hu₀u₁.trans hu₁Bar)) hBarT hTb₀
      (by norm_num : (0 : ℝ) ≤ 0) H₀
  let B : ℝ := max (max P M) B₁
  refine ⟨B, hP.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro b hb u v hu huv hvb
  by_cases hu₀u : u₀ < u
  · exact (hupper b hb u v hu₀u huv hvb).trans (le_max_right _ _)
  have huu₀ : u ≤ u₀ := le_of_not_gt hu₀u
  by_cases hBarv : vBar ≤ v
  · exact (hstrip b hb u v hu.le huu₀ hBarv hvb).trans
      ((le_max_left _ _).trans (le_max_left _ _))
  have hvBar : v ≤ vBar := (lt_of_not_ge hBarv).le
  have hp : (u, v) ∈ openDevelopment 0 b :=
    ⟨⟨hu, huv.trans hvb⟩, ⟨huv, hvb⟩⟩
  have hp₀ : (u, v) ∈ openDevelopment 0 b₀ :=
    ⟨⟨hu, huv.trans (hvBar.trans_lt hb₀.1)⟩,
      ⟨huv, hvBar.trans_lt hb₀.1⟩⟩
  have heq := family_alphaPrime_eq_on_common_development
    hfamily hb hb₀Star hp hp₀
  let p₀ : AlphaPrimeDomain (S b₀) :=
    ⟨(u, v), alphaPrimeDomain_of_open H₀ hp₀⟩
  have hbound := hcompact (u, v) hp₀ hvBar p₀.2
  have hpow : (S b₀).r u v ^ (0 : ℝ) = 1 := by simp
  rw [hpow, one_mul] at hbound
  have hvalue : |deriv (fun t => (S b).alpha u t / (S b).lam u t) v /
      (S b).lam u v| ≤ M := by
    rw [← alphaPrime_eq_deriv (S b)
      ⟨(u, v), alphaPrimeDomain_of_open (hfamily b hb).1 hp⟩]
    rw [heq]
    exact hbound
  exact hvalue.trans ((le_max_right _ _).trans (le_max_left _ _))

end ChristodoulouBV.Uniqueness

end
