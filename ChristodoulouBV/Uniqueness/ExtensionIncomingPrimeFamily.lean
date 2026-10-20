module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingPrimeContinuity
public import ChristodoulouBV.Uniqueness.ExtensionIncomingPrimeCoefficient
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Uniform outgoing derivative on the incoming line

The initial derivative, strip coefficients, and equation (5.2) give a
cutoff independent bound for the outgoing derivative at `u₀`.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Equation (5.2) bounds `α′(u₀,v)` uniformly for outgoing coordinates
above a fixed off-axis cutoff and below `vStar`. -/
theorem exists_alphaPrime_bound_on_incoming_strip
    {alpha₀ : ℝ → ℝ} {vStar u₀ u₁ vBar η : ℝ} {S : ℝ → Fields}
    (hu₀ : 0 < u₀) (hu₀u₁ : u₀ < u₁) (hu₁v : u₁ < vBar)
    (hvBarStar : vBar < vStar) (hη : η < 1)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ η) :
    ∃ P : ℝ, 0 ≤ P ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ v : ℝ, vBar ≤ v → v < b →
          |deriv (fun t => (S b).alpha u₀ t / (S b).lam u₀ t) v /
            (S b).lam u₀ v| ≤ P := by
  have hu₁ : 0 < u₁ := hu₀.trans hu₀u₁
  obtain ⟨ρ, hρ, hr⟩ :=
    exists_radius_floor_before_star hu₁.le hu₁v hvBarStar hfamily
  obtain ⟨N, hN, hnu⟩ :=
    exists_nu_bound_closed_before_star hu₁ hu₁v hvBarStar hα hfamily
  obtain ⟨M, hM, hscalar⟩ :=
    exists_scalar_bound_before_star hu₁ hu₁v hvBarStar hα hfamily
  obtain ⟨l, q, hl, hq, hgap⟩ :=
    exists_expansion_and_gap_floor_before_star hu₀ hu₀u₁ hu₁v
      hvBarStar hη hα hfamily htail
  obtain ⟨P₀, hP₀, hinitial⟩ :=
    exists_initial_alphaPrime_bound_before_star
      (hu₁.trans hu₁v) hvBarStar hα hfamily
  let C : ℝ := 2 * (N / ρ) * (1 / q)
  let F : ℝ := 3 * (N / ρ ^ 2) * (1 / q) * (M / l) +
    (N / ρ ^ 2) * (1 / q) * (M / l) ^ 3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  let P : ℝ := max 0 (gronwallBound (P₀ + 1) C F u₀)
  have hP : 0 ≤ P := le_max_left _ _
  refine ⟨P, hP, ?_⟩
  intro b hb v hvBarv hvb
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
  have hvpos : 0 < v := hu₁.trans (hu₁v.trans_le hvBarv)
  have hcont : ContinuousOn f (Icc (0 : ℝ) u₀) :=
    alphaPrime_coordinate_continuousOn_incoming_of_c1 H
      hu₀.le (hu₀u₁.trans (hu₁v.trans_le hvBarv)) hvb
  have hinit : |f 0| ≤ P₀ := hinitial b hb v hvBarv hvb
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) u₀, HasDerivAt f (f' s) s := by
    intro s hs
    have hsb : s < v := hs.2.trans (hu₀u₁.trans (hu₁v.trans_le hvBarv))
    have hp : (s, v) ∈ openDevelopment 0 b :=
      ⟨⟨hs.1, hsb.trans hvb⟩, ⟨hsb, hvb⟩⟩
    exact alphaPrime_hasDerivAt_u H hp
  have hbound : ∀ s ∈ Ioo (0 : ℝ) u₀,
      |f' s| ≤ C * |f s| + F := by
    intro s hs
    have hsle : s ≤ u₁ := hs.2.le.trans hu₀u₁.le
    have hpU : (s, v) ∈ developmentWithInitialEdge b :=
      ⟨hs.1.le, hsle.trans_lt (hu₁v.trans_le hvBarv), hvb⟩
    obtain ⟨_, _, hmu, hmu1⟩ := H.reduced_signs_of_c1 hpU
    have hpoint := hgap b hb s v hs.1.le hsle hvBarv hvb
    have hrest := alphaPrime_rhs_abs_le hρ
      (hr b hb s v hs.1.le hsle hvBarv hvb) hN
      (hnu b hb s v hs.1.le hsle hvBarv hvb)
      ⟨hmu, hmu1.le⟩ hq hpoint.2 hl hpoint.1 hM
      (hscalar b hb s v hs.1.le hsle hvBarv hvb).1
      (P := f s)
    simpa only [f', C, F] using hrest
  have hbound₀ := abs_le_gronwall_from_initial_continuity hu₀ hP₀ hC hF
    hcont hinit hderiv hbound
  simp only [sub_zero] at hbound₀
  exact hbound₀.trans (le_max_right _ _)

end ChristodoulouBV.Uniqueness

end
