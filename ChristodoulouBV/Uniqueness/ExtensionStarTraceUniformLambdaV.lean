module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceLambdaVLinear
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceUniformCoefficientBase
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceUniformCoefficient
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceFamilyNu
import ChristodoulouBV.Uniqueness.ExtensionIncomingPrimeGronwall
import ChristodoulouBV.Uniqueness.ExtensionIncomingSigns
import ChristodoulouBV.Uniqueness.ExtensionStarTraceUnconditional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform outgoing derivative of lambda before the terminal edge

The linear equation for `λᵥ` has zero initial seed and uniformly bounded
coefficients. Gronwall gives one bound for all finite old members.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The outgoing first derivative of `λ` is uniformly bounded on the
strict old union. The incoming weighted bound is the already proved incoming strip estimate. -/
theorem exists_uniform_lambda_v_bound_before_star_of_incoming_bddAbove
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
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε)
    (hIncoming : BddAbove
      (incomingWeightedAlphaPrimeValues u₀ vStar ((1 : ℝ) / 2) S)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 ≤ u → u < v → v < b →
          |deriv ((S b).lam u) v| ≤ C := by
  obtain ⟨D, hD, hQ⟩ :=
    exists_uniform_mixed_coefficient_bound_before_star
      hu₀ hα hfamily hε1 htail
  obtain ⟨N, hN, hNu⟩ :=
    exists_nu_bound_before_star_from_cubic_mass
      hu₀ hα hfamily hε1 htail
  have hε0 : 0 ≤ ε := tail_mass_upper_nonneg hu₀ hfamily htail
  obtain ⟨Cq, hCq, hQv⟩ :=
    exists_uniform_mixed_coefficient_derivative_bound_of_incoming_bddAbove
      hu₀ hα hfamily hε0 hε1 htail hIncoming
  let K : ℝ := N * D
  let F : ℝ := N * D ^ 2 + N * Cq
  let C : ℝ := max 0 (gronwallBound 1 K F vStar)
  have hK : 0 ≤ K := mul_nonneg hN hD
  have hF : 0 ≤ F := add_nonneg
    (mul_nonneg hN (sq_nonneg D)) (mul_nonneg hN hCq)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro b hb u v hu huv hvb
  let H := (hfamily b hb).1
  have hv0 : 0 < v := hu.trans_lt huv
  have hvstar : v < vStar := hvb.trans hb.2
  have hseed : deriv ((S b).lam 0) v = 0 :=
    lambda_v_initial_eq_zero_of_gauge H
      (fun w hw => ((hfamily b hb).2 w hw).1) ⟨hv0, hvb⟩
  by_cases hu0 : u = 0
  · subst u
    rw [hseed, abs_zero]
    exact le_max_left _ _
  have huPos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  let y : ℝ → ℝ := fun s => deriv ((S b).lam s) v
  have hy : ContinuousOn y (Icc 0 u) :=
    lambda_v_continuousOn_incoming_of_c1 H hu huv hvb
  have hy0 : |y 0| ≤ 0 := by simp [y, hseed]
  have hderiv : ∀ s ∈ Ioo 0 u,
      HasDerivAt y (deriv y s) s := by
    intro s hs
    have hp : (s, v) ∈ openDevelopment 0 b :=
      ⟨⟨hs.1, (hs.2.trans huv).trans hvb⟩,
        ⟨hs.2.trans huv, hvb⟩⟩
    exact (lambda_v_hasDerivAt_u_linear_of_c1 H hp).differentiableAt.hasDerivAt
  have hbound : ∀ s ∈ Ioo 0 u,
      |deriv y s| ≤ K * |y s| + F := by
    intro s hs
    have hsv : s < v := hs.2.trans huv
    have hp : (s, v) ∈ openDevelopment 0 b :=
      ⟨⟨hs.1, hsv.trans hvb⟩, ⟨hsv, hvb⟩⟩
    have hpU : (s, v) ∈ developmentWithInitialEdge b :=
      ⟨hs.1.le, hsv, hvb⟩
    have hlam0 : 0 ≤ (S b).lam s v :=
      (H.solution.lam_pos (s, v) hpU).le
    have hlamHalf : (S b).lam s v ≤ 1 / 2 :=
      lam_le_half_of_initial_gauge H
        (fun w hw => ((hfamily b hb).2 w hw).1)
        hs.1.le hsv hvb
    have hlam1 : (S b).lam s v ≤ 1 := by linarith only [hlamHalf]
    have hnu := hNu b hb s v hs.1.le hsv hvb
    have hcoeff := hQ b hb s v hs.1 hsv hvb
    have hcoeffv := hQv b hb s v hs.1 hsv hvb
    have halgebra := lambda_v_source_abs_le (L := y s)
      hlam0 hlam1 hnu hcoeff.1 hcoeff.2 hcoeffv
    have heq := (lambda_v_hasDerivAt_u_linear_of_c1 H hp).deriv
    rw [heq]
    convert halgebra using 1
  have hresult := abs_le_gronwall_from_initial_continuity
    (a := 0) (b := u) (P := 0) (C := K) (F := F)
    huPos (by norm_num) hK hF hy hy0 hderiv hbound
  have hlength : u ≤ vStar := (le_of_lt huv).trans (le_of_lt hvstar)
  have hmono := gronwallBound_mono (by norm_num : (0 : ℝ) ≤ 1) hF hK
  have hcompare : gronwallBound 1 K F u ≤ gronwallBound 1 K F vStar := by
    simpa only [sub_zero] using hmono hlength
  have hresult' : |y u| ≤ gronwallBound 1 K F u := by
    simpa only [zero_add, sub_zero] using hresult
  have hfinal : |y u| ≤ gronwallBound 1 K F vStar :=
    hresult'.trans hcompare
  exact hfinal.trans (le_max_right _ _)

/-- The incoming strip estimate removes the auxiliary incoming boundedness premise from the uniform
`λᵥ` estimate. -/
theorem exists_uniform_lambda_v_bound_before_star
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
        ∀ u v : ℝ, 0 ≤ u → u < v → v < b →
          |deriv ((S b).lam u) v| ≤ C := by
  have hεlt : ε < 1 := by
    obtain ⟨ε₁, heq, _, hε₁one, _, _, _, _⟩ := universal_epsilon_choice
    exact (show ε < ε₁ by simpa only [heq] using hε1).trans hε₁one
  have hIncoming := incoming_weighted_bound_before_star
    hu₀.1 hu₀.2 hεlt (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hα hfamily htail
  exact exists_uniform_lambda_v_bound_before_star_of_incoming_bddAbove
    hu₀ hα hfamily hε1 htail hIncoming

end ChristodoulouBV.Uniqueness

end
