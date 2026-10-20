module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingPrimeFamily
import ChristodoulouBV.Uniqueness.ExtensionIncomingPrimeCoefficient
import ChristodoulouBV.Uniqueness.ExtensionIncomingFamilyTailGap
import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarFamily
import ChristodoulouBV.Uniqueness.ExtensionIncomingNu
import ChristodoulouBV.Uniqueness.ExtensionIncomingFamilyRadius
import ChristodoulouBV.Uniqueness.ExtensionIncomingInitialPrime
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform alpha-prime bound below the incoming tail line

The incoming off-axis strip estimates bound every coefficient in the incoming
transport equation (5.2) on `0 ≤ u ≤ u₀`, uniformly in the old-family cutoff.
The initial derivative of the prescribed scalar datum supplies the seed.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- On the terminal off-axis strip, the outgoing quotient derivative is
uniformly bounded for *all* incoming coordinates below `u₀`. No incoming
weighted bound is required for this part of the old development. -/
theorem exists_alphaPrime_bound_on_lower_terminal_strip
    {alpha₀ : ℝ → ℝ} {vStar u₀ u₁ vBar ε : ℝ} {S : ℝ → Fields}
    (hu₀ : 0 < u₀) (hu₀u₁ : u₀ < u₁) (hu₁Bar : u₁ < vBar)
    (hBarStar : vBar < vStar) (hε : ε < 1)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    ∃ P : ℝ, 0 ≤ P ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 ≤ u → u ≤ u₀ → vBar ≤ v → v < b →
          |deriv (fun t => (S b).alpha u t / (S b).lam u t) v /
            (S b).lam u v| ≤ P := by
  have hu₁ : 0 < u₁ := hu₀.trans hu₀u₁
  obtain ⟨ρ, hρ, hr⟩ :=
    exists_radius_floor_before_star hu₁.le hu₁Bar hBarStar hfamily
  obtain ⟨N, hN, hnu⟩ :=
    exists_nu_bound_closed_before_star hu₁ hu₁Bar hBarStar hα hfamily
  obtain ⟨M, hM, hscalar⟩ :=
    exists_scalar_bound_before_star hu₁ hu₁Bar hBarStar hα hfamily
  obtain ⟨l, q, hl, hq, hgap⟩ :=
    exists_expansion_and_gap_floor_before_star
      hu₀ hu₀u₁ hu₁Bar hBarStar hε hα hfamily htail
  obtain ⟨P₀, hP₀, hinitial⟩ :=
    exists_initial_alphaPrime_bound_before_star
      (hu₁.trans hu₁Bar) hBarStar hα hfamily
  let C : ℝ := 2 * (N / ρ) * (1 / q)
  let F : ℝ := 3 * (N / ρ ^ 2) * (1 / q) * (M / l) +
    (N / ρ ^ 2) * (1 / q) * (M / l) ^ 3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  let P : ℝ := max P₀ (max 0 (gronwallBound (P₀ + 1) C F u₀))
  refine ⟨P, hP₀.trans (le_max_left _ _), ?_⟩
  intro b hb u v hu huu₀ hBarv hvb
  let H := (hfamily b hb).1
  let f : ℝ → ℝ := fun s =>
    deriv (fun t => (S b).alpha s t / (S b).lam s t) v /
      (S b).lam s v
  let f' : ℝ → ℝ := fun s =>
    -2 * ((S b).nu s v / (S b).r s v) *
      ((2 * (S b).m s v / (S b).r s v) /
        (1 - 2 * (S b).m s v / (S b).r s v)) * f s +
    3 * ((S b).nu s v / (S b).r s v ^ 2) *
      ((2 * (S b).m s v / (S b).r s v) /
        (1 - 2 * (S b).m s v / (S b).r s v)) *
      ((S b).theta s v / (S b).lam s v) -
    ((S b).nu s v / (S b).r s v ^ 2) *
      (1 / (1 - 2 * (S b).m s v / (S b).r s v)) *
      ((S b).theta s v / (S b).lam s v) ^ 3
  have hinit : |f 0| ≤ P₀ := hinitial b hb v hBarv hvb
  by_cases hu0 : u = 0
  · subst u
    exact hinit.trans (le_max_left _ _)
  have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  have huv : u < v := huu₀.trans_lt (hu₀u₁.trans (hu₁Bar.trans_le hBarv))
  have hcont : ContinuousOn f (Icc (0 : ℝ) u) :=
    alphaPrime_coordinate_continuousOn_incoming_of_c1 H hu huv hvb
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) u, HasDerivAt f (f' s) s := by
    intro s hs
    have hsb : s < v := hs.2.trans huv
    exact alphaPrime_hasDerivAt_u H
      (show (s, v) ∈ openDevelopment 0 b from
        ⟨⟨hs.1, hsb.trans hvb⟩, ⟨hsb, hvb⟩⟩)
  have hbound : ∀ s ∈ Ioo (0 : ℝ) u,
      |f' s| ≤ C * |f s| + F := by
    intro s hs
    have hsle : s ≤ u₁ := hs.2.le.trans (huu₀.trans hu₀u₁.le)
    have hpU : (s, v) ∈ developmentWithInitialEdge b :=
      ⟨hs.1.le, hsle.trans_lt (hu₁Bar.trans_le hBarv), hvb⟩
    obtain ⟨_, _, hmu, hmu1⟩ := H.reduced_signs_of_c1 hpU
    have hpoint := hgap b hb s v hs.1.le hsle hBarv hvb
    have hrest := alphaPrime_rhs_abs_le hρ
      (hr b hb s v hs.1.le hsle hBarv hvb) hN
      (hnu b hb s v hs.1.le hsle hBarv hvb)
      ⟨hmu, hmu1.le⟩ hq hpoint.2 hl hpoint.1 hM
      (hscalar b hb s v hs.1.le hsle hBarv hvb).1
      (P := f s)
    simpa only [f', C, F] using hrest
  have hpoint := abs_le_gronwall_from_initial_continuity
    hu' hP₀ hC hF hcont hinit hderiv hbound
  simp only [sub_zero] at hpoint
  have hmono := gronwallBound_mono (by linarith : 0 ≤ P₀ + 1) hF hC
  have hlength : u ≤ u₀ := huu₀
  exact hpoint.trans ((hmono hlength).trans
    ((le_max_right _ _).trans (le_max_right _ _)))

end ChristodoulouBV.Uniqueness

end
