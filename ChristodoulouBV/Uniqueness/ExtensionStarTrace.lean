module

public import ChristodoulouBV.Uniqueness.ExtensionOldAbsorption
public import ChristodoulouBV.Uniqueness.ExtensionOldEstimateLinear
import Mathlib.Tactic.Linarith

/-!
# Uniform old-development estimates toward the terminal trace

The first step of the terminal trace construction extracts one cutoff
independent weighted `α′` bound from (5.12) and applies the outgoing Hardy
estimate (5.5) to the scalar quotient on every old family member.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Equations (5.12) and (5.5) give one bound for `θ/λ` on every compatible
old ray. The constant is independent of the member's cutoff. This is the
first estimate in part (A) of the terminal trace data. -/
theorem exists_uniform_theta_ratio_bound_before_star_of_incoming_bddAbove
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (_hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
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
    ∃ A : ℝ, 0 ≤ A ∧
      (∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, u₀ < u → u < v → v < b →
          (S b).r u v ^ ((1 : ℝ) / 2) *
            |deriv (fun t => (S b).alpha u t / (S b).lam u t) v /
              (S b).lam u v| ≤ A) ∧
      (∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, u₀ < u → u < v → v < b →
          |(S b).theta u v / (S b).lam u v| ≤
            A / (2 - (1 : ℝ) / 2) *
              ((S b).r u v) ^ (1 - (1 : ℝ) / 2)) := by
  obtain ⟨ε₁, hε₁eq, _, _, _, _, _, hcompare⟩ :=
    universal_epsilon_choice
  have hεlt : ε < ε₁ := by simpa only [hε₁eq] using hε1
  have hcoeff := hcompare ε hε0 hεlt
  let D := incomingWeightedAlphaPrimeSup u₀ vStar ((1 : ℝ) / 2) S
  let A : ℝ := D / (1 - ε / ε₁)
  have hden : 0 < 1 - ε / ε₁ := by linarith [hcoeff.2]
  have hpoint : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ u v : ℝ, u₀ < u → u < v → v < b →
        (S b).r u v ^ ((1 : ℝ) / 2) *
          |deriv (fun t => (S b).alpha u t / (S b).lam u t) v /
            (S b).lam u v| ≤ A := by
    intro b hb u v hu₀u huv hvb
    have hp : (u, v) ∈ openDevelopment 0 b :=
      ⟨⟨hu₀.1.trans hu₀u, huv.trans hvb⟩, ⟨huv, hvb⟩⟩
    let p : AlphaPrimeDomain (S b) :=
      ⟨(u, v), alphaPrimeDomain_of_open (hfamily b hb).1 hp⟩
    have hdev : (u, v) ∈ openDevelopment u₀ vStar :=
      ⟨⟨hu₀u, huv.trans (hvb.trans hb.2)⟩,
        ⟨huv, hvb.trans hb.2⟩⟩
    let u₁ : ℝ := (v + vStar) / 2
    let t : ℝ := (u₁ + vStar) / 2
    have huu₁ : u < u₁ := by dsimp [u₁]; linarith [hdev.2.1, hdev.2.2]
    have hu₀u₁ : u₀ < u₁ := hu₀u.trans huu₁
    have hu₁Star : u₁ < vStar := by dsimp [u₁]; linarith [hdev.2.2]
    have hu₁t : u₁ < t := by dsimp [t]; linarith [hu₁Star]
    have htStar : t < vStar := by dsimp [t]; linarith [hu₁Star]
    have hvt : v ≤ t := by dsimp [t, u₁]; linarith [hdev.2.2]
    have htrunc : (u, v) ∈ truncatedDevelopment u₀ u₁ vStar :=
      (mem_truncatedDevelopment_iff hu₁Star).2
        ⟨hu₀u, huu₁, huv, hdev.2.2⟩
    let Aₜ := finiteWeightedAlphaPrimeSup u₀ u₁ vStar ((1 : ℝ) / 2) t S
    let Dₜ := finiteIncomingWeightedAlphaPrimeSup u₀ vStar ((1 : ℝ) / 2) t S
    have hfinite : Aₜ ≤ Dₜ / (1 - ε / ε₁) := by
      rw [hε₁eq]
      exact finiteWeightedAlphaPrimeSup_le_finiteIncoming_div
        hu₀.1 hu₀u₁ hu₁t htStar hε0 hε1 hfamily htail
    have hDₜ : Dₜ ≤ D :=
      finiteIncomingWeightedAlphaPrimeSup_le_incomingSup
        hu₀.1 (hu₀u₁.trans hu₁t) htStar hfamily hIncoming
    have hAₜ : Aₜ ≤ A :=
      hfinite.trans (by
        dsimp [A]
        exact div_le_div_of_nonneg_right hDₜ hden.le)
    have hvalue : (S b).r u v ^ ((1 : ℝ) / 2) *
        |alphaPrime (S b) p| ≤ Aₜ :=
      weighted_alphaPrime_le_finite_cutoff_sup
        (hu₀.1.trans (hu₀u₁.trans hu₁t)) htStar (by norm_num)
        hfamily hb p htrunc hp hvt
    simpa only [alphaPrime_eq_deriv] using hvalue.trans hAₜ
  have hA0 : 0 ≤ A := by
    let u := (u₀ + vStar) / 2
    let v := (u + vStar) / 2
    let b := (v + vStar) / 2
    have huu : u₀ < u := by dsimp [u]; linarith [hu₀.2]
    have huStar : u < vStar := by dsimp [u]; linarith [hu₀.2]
    have huv : u < v := by dsimp [v]; linarith [huStar]
    have hvStar : v < vStar := by dsimp [v]; linarith [huStar]
    have hvb : v < b := by dsimp [b]; linarith [hvStar]
    have hb : b ∈ Ioo (0 : ℝ) vStar := by
      constructor
      · exact (hu₀.1.trans (huu.trans (huv.trans hvb)))
      · dsimp [b]; linarith [hvStar]
    have h := hpoint b hb u v huu huv hvb
    have hr := (hfamily b hb).1.solution.radius_pos (u, v)
      (show (u, v) ∈ developmentWithInitialEdge b from
        ⟨(hu₀.1.trans huu).le, huv, hvb⟩)
    exact (mul_nonneg (Real.rpow_nonneg hr.le _)
      (abs_nonneg _)).trans h
  refine ⟨A, hA0, hpoint, ?_⟩
  intro b hb u v hu₀u huv hvb
  have hu : 0 < u := hu₀.1.trans hu₀u
  apply theta_ratio_le_weightedAlphaPrime (hfamily b hb).1 hu huv hvb
    (by norm_num : 0 < (1 : ℝ) / 2)
    (by norm_num : (1 : ℝ) / 2 < 1)
  intro s hs
  exact hpoint b hb u s hu₀u hs.1 (hs.2.trans_lt hvb)

end ChristodoulouBV.Uniqueness

end
