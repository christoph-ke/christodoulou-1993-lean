module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceBootstrap
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceIncoming
import ChristodoulouBV.Uniqueness.ExtensionIncomingRadius
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Uniform unweighted alpha-prime bound before the terminal edge

The one-member square-root comparison is supplied with the compatible
family's weighted bound, linear mass-ratio improvement, incoming seed, and
small mass gap. The resulting constant is independent of the cutoff.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The unweighted improvement of (5.12) above the initial incoming line.
Incoming boundedness is the only extra premise beyond the frozen
family, gauge, and small mass-ratio hypotheses. -/
theorem exists_uniform_alphaPrime_bound_before_star_of_incoming_bddAbove
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
        ∀ u v : ℝ, u₀ < u → u < v → v < b →
          |deriv (fun t => (S b).alpha u t / (S b).lam u t) v /
            (S b).lam u v| ≤ B := by
  obtain ⟨A, hA0, hweighted, hθ⟩ :=
    exists_uniform_theta_ratio_bound_before_star_of_incoming_bddAbove
      hu₀ hα hfamily hε0 hε1 htail hIncoming
  obtain ⟨M, hM0, hμ⟩ :=
    exists_uniform_linear_mass_ratio_before_star_of_incoming_bddAbove
      hu₀ hα hfamily hε0 hε1 htail hIncoming
  obtain ⟨B₀, hB₀0, hseed⟩ :=
    exists_uniform_incoming_alphaPrime_bound_before_star_of_incoming_bddAbove
      hu₀ hfamily hIncoming
  obtain ⟨ε₁, hε₁eq, _, hε₁one, _, _, _, _⟩ := universal_epsilon_choice
  have hεlt : ε < ε₁ := by simpa only [hε₁eq] using hε1
  have hq₀ : 0 < 1 - ε := by linarith only [hεlt, hε₁one]
  let C : ℝ := (4 * M * A + 8 * A ^ 3 / 27) / (1 - ε)
  let B : ℝ := B₀ + 2 * C * Real.sqrt (vStar / 2)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    apply div_nonneg
    · positivity
    · exact hq₀.le
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨B, hB0, ?_⟩
  intro b hb u v hu₀u huv hvb
  have H := (hfamily b hb).1
  have hu0v : u₀ < v := hu₀u.trans huv
  have hsegweighted : ∀ s ∈ Ioo u₀ u,
      Real.sqrt ((S b).r s v) *
        |deriv (fun t => (S b).alpha s t / (S b).lam s t) v /
          (S b).lam s v| ≤ A := by
    intro s hs
    simpa only [Real.sqrt_eq_rpow] using
      hweighted b hb s v hs.1 (hs.2.trans huv) hvb
  have hsegθ : ∀ s ∈ Ioo u₀ u,
      |(S b).theta s v / (S b).lam s v| ≤
        (2 * A / 3) * Real.sqrt ((S b).r s v) := by
    intro s hs
    have h := hθ b hb s v hs.1 (hs.2.trans huv) hvb
    calc
      |(S b).theta s v / (S b).lam s v| ≤
          A / (2 - (1 : ℝ) / 2) *
            ((S b).r s v) ^ (1 - (1 : ℝ) / 2) := h
      _ = (2 * A / 3) * Real.sqrt ((S b).r s v) := by
        have htwo : (2 : ℝ) - 1 / 2 = 3 / 2 := by norm_num
        have hone : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
        have hcoeff : A / (3 / 2) = 2 * A / 3 := by ring
        rw [htwo, hone, hcoeff, Real.sqrt_eq_rpow]
  have hsegμ : ∀ s ∈ Ioo u₀ u,
      2 * (S b).m s v / (S b).r s v ≤ M * (S b).r s v := by
    intro s hs
    exact hμ b hb s v hs.1 (hs.2.trans huv) hvb
  have hseggap : ∀ s ∈ Ioo u₀ u,
      1 - ε ≤ 1 - 2 * (S b).m s v / (S b).r s v := by
    intro s hs
    have hdev : (s, v) ∈ openDevelopment u₀ vStar :=
      ⟨⟨hs.1, (hs.2.trans huv).trans (hvb.trans hb.2)⟩,
        ⟨hs.2.trans huv, hvb.trans hb.2⟩⟩
    have hmember : (s, v) ∈ developmentWithInitialEdge b :=
      ⟨(hu₀.1.trans hs.1).le, hs.2.trans huv, hvb⟩
    linarith only [htail b hb (s, v) ⟨hdev, hmember⟩]
  have hpoint := alphaPrime_abs_le_incoming_add_sqrt_radius H hu₀.1
    hu₀u huv hvb hA0 hM0 hq₀ hsegweighted hsegθ hsegμ hseggap
    (hseed b hb v hu0v hvb)
  have hrad : (S b).r u₀ v ≤ (S b).r 0 v :=
    radius_antitone_on_incoming_of_c1 H (le_refl 0) hu₀.1.le hu0v hvb
  have hinit : (S b).r 0 v = v / 2 :=
    ((hfamily b hb).2 v ⟨hu₀.1.trans hu0v, hvb⟩).1
  have hradStar : (S b).r u₀ v ≤ vStar / 2 := by
    rw [hinit] at hrad
    linarith only [hrad, hvb, hb.2]
  have hroot : Real.sqrt ((S b).r u₀ v) ≤ Real.sqrt (vStar / 2) :=
    Real.sqrt_le_sqrt hradStar
  have hbound : 2 * C * Real.sqrt ((S b).r u₀ v) ≤
      2 * C * Real.sqrt (vStar / 2) :=
    mul_le_mul_of_nonneg_left hroot (by positivity)
  exact hpoint.trans (by dsimp [B, C] at hbound ⊢; linarith only [hbound])

end ChristodoulouBV.Uniqueness

end
