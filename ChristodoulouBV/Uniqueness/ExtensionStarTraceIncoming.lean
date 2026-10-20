module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceMass
public import ChristodoulouBV.Uniqueness.ExtensionIncomingFamilyRadius
import Mathlib.Tactic.Linarith

/-!
# The unweighted incoming seed for the terminal trace

On the compact part of `u=u₀`, one fixed member bounds `α′`. On the remaining
part, the uniform off-axis radius floor converts the incoming weighted bound to an
unweighted one. Both bounds are independent of the family cutoff.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The unweighted `B₀` input for the incoming transport bootstrap. The only
extra premise is the bounded incoming weighted sample set. -/
theorem exists_uniform_incoming_alphaPrime_bound_before_star_of_incoming_bddAbove
    {alpha₀ : ℝ → ℝ} {vStar u₀ : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hIncoming : BddAbove
      (incomingWeightedAlphaPrimeValues u₀ vStar ((1 : ℝ) / 2) S)) :
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ v : ℝ, u₀ < v → v < b →
          |deriv (fun t => (S b).alpha u₀ t / (S b).lam u₀ t) v /
            (S b).lam u₀ v| ≤ B₀ := by
  let vBar : ℝ := (u₀ + vStar) / 2
  have hu₀Bar : u₀ < vBar := by dsimp [vBar]; linarith [hu₀.2]
  have hBarStar : vBar < vStar := by dsimp [vBar]; linarith [hu₀.2]
  obtain ⟨ρ, hρ, hρfloor⟩ :=
    exists_radius_floor_before_star hu₀.1.le hu₀Bar hBarStar hfamily
  obtain ⟨b₀, hb₀, H₀⟩ :=
    exists_family_member_beyond_cutoff (hu₀.1.trans hu₀Bar) hBarStar hfamily
  let B : ℝ := (vBar + b₀) / 2
  have hBarB : vBar < B := by dsimp [B]; linarith [hb₀.1]
  have hBb₀ : B < b₀ := by dsimp [B]; linarith [hb₀.1]
  obtain ⟨M₀, hM₀, hcompact⟩ :=
    exists_weighted_alphaPrime_bound_on_finite_member
      (hu₀.1.trans hu₀Bar) hBarB hBb₀
      (by norm_num : (0 : ℝ) ≤ 0) H₀
  obtain ⟨D, hD⟩ := hIncoming
  have hρsqrt : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ
  let B₀ : ℝ := max M₀ (D / Real.sqrt ρ)
  refine ⟨max 0 B₀, le_max_left _ _, ?_⟩
  intro b hb v hu₀v hvb
  have hp : (u₀, v) ∈ openDevelopment 0 b :=
    ⟨⟨hu₀.1, hu₀v.trans hvb⟩, ⟨hu₀v, hvb⟩⟩
  let p : AlphaPrimeDomain (S b) :=
    ⟨(u₀, v), alphaPrimeDomain_of_open (hfamily b hb).1 hp⟩
  have hprime : alphaPrime (S b) p =
      deriv (fun t => (S b).alpha u₀ t / (S b).lam u₀ t) v /
        (S b).lam u₀ v := alphaPrime_eq_deriv _ _
  rw [← hprime]
  by_cases hvBar : v ≤ vBar
  · have hb₀Star : b₀ ∈ Ioo (0 : ℝ) vStar :=
      ⟨(hu₀.1.trans hu₀Bar).trans hb₀.1, hb₀.2⟩
    have hp₀ : (u₀, v) ∈ openDevelopment 0 b₀ :=
      ⟨⟨hu₀.1, hu₀v.trans (hvBar.trans_lt hb₀.1)⟩,
        ⟨hu₀v, hvBar.trans_lt hb₀.1⟩⟩
    have heq := family_alphaPrime_eq_on_common_development
      hfamily hb hb₀Star hp hp₀
    have hbound := hcompact (u₀, v) hp₀ hvBar
      (alphaPrimeDomain_of_open H₀ hp₀)
    have h0 : (S b₀).r u₀ v ^ (0 : ℝ) = 1 := by simp
    rw [h0, one_mul] at hbound
    have hthis : |alphaPrime (S b) p| ≤ M₀ := by
      simpa only [← heq] using hbound
    exact hthis.trans (le_max_left _ _ |>.trans (le_max_right _ _))
  · have hvBar' : vBar ≤ v := le_of_not_ge hvBar
    have hrFloor : ρ ≤ (S b).r u₀ v :=
      hρfloor b hb u₀ v hu₀.1.le le_rfl hvBar' hvb
    have hr : 0 < (S b).r u₀ v := hρ.trans_le hrFloor
    have hsample : (S b).r u₀ v ^ ((1 : ℝ) / 2) *
        |alphaPrime (S b) p| ∈
          incomingWeightedAlphaPrimeValues u₀ vStar ((1 : ℝ) / 2) S := by
      refine ⟨b, hb, p, rfl, ⟨hu₀v, hvb.trans hb.2⟩, hp, rfl⟩
    have hweighted := hD hsample
    have hrootle : Real.sqrt ρ ≤ Real.sqrt ((S b).r u₀ v) :=
      Real.sqrt_le_sqrt hrFloor
    have hsmall : Real.sqrt ρ * |alphaPrime (S b) p| ≤ D := by
      calc
        _ ≤ Real.sqrt ((S b).r u₀ v) * |alphaPrime (S b) p| :=
          mul_le_mul_of_nonneg_right hrootle (abs_nonneg _)
        _ = (S b).r u₀ v ^ ((1 : ℝ) / 2) *
            |alphaPrime (S b) p| := by rw [Real.sqrt_eq_rpow]
        _ ≤ D := hweighted
    have hthis : |alphaPrime (S b) p| ≤ D / Real.sqrt ρ :=
      (le_div_iff₀ hρsqrt).2 (by simpa only [mul_comm] using hsmall)
    exact hthis.trans (le_max_right _ _ |>.trans (le_max_right _ _))

end ChristodoulouBV.Uniqueness

end
