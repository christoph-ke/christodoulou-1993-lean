module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceExpansion
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceUnconditional
public import ChristodoulouBV.Uniqueness.ExtensionIncomingFamilyTailGap
import ChristodoulouBV.Uniqueness.ExtensionIncomingRadius
import ChristodoulouBV.Uniqueness.ExtensionCutoff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Uniform expansion floor on the old family's terminal tail

The off-axis expansion floor at the initial incoming line propagates to
the corner by the radius attenuation comparison. Its constant is independent
of the family cutoff.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The expansion has one positive lower bound throughout a full near-top
triangle of every old member, including points arbitrarily near the axis.
This is the tail portion of part (A) of the terminal trace construction. -/
theorem exists_expansion_floor_on_terminal_tail_before_star
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
    ∃ vBar c : ℝ, u₀ < vBar ∧ vBar < vStar ∧ 0 < c ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 ≤ u → u < v → vBar ≤ v → v < b →
          c ≤ (S b).lam u v := by
  let u₁ : ℝ := (u₀ + vStar) / 2
  let vBar : ℝ := (u₁ + vStar) / 2
  have hu₀u₁ : u₀ < u₁ := by dsimp [u₁]; linarith only [hu₀.2]
  have hu₁Star : u₁ < vStar := by dsimp [u₁]; linarith only [hu₀.2]
  have hu₁vBar : u₁ < vBar := by dsimp [vBar]; linarith only [hu₁Star]
  have hvBarStar : vBar < vStar := by dsimp [u₁, vBar]; linarith only [hu₀.2]
  have hεlt : ε < 1 := by
    obtain ⟨ε₁, heq, _, hε₁one, _, _, _, _⟩ := universal_epsilon_choice
    exact (show ε < ε₁ by simpa only [heq] using hε1).trans hε₁one
  have hq₀ : 0 < 1 - ε := by linarith only [hεlt]
  obtain ⟨l, q, hl, _, hfloor⟩ :=
    exists_expansion_and_gap_floor_before_star
      hu₀.1 hu₀u₁ hu₁vBar hvBarStar hεlt hα hfamily htail
  obtain ⟨B, _, _, _, _, hmass⟩ :=
    exists_uniform_scalar_and_cubic_mass_bounds_before_star
      hu₀ hα hfamily hε1 htail
  let R : ℝ := vStar / 2
  let C : ℝ := B ^ 2 / (24 * (1 - ε))
  let c : ℝ := l * Real.exp (-(C * R ^ 2))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hR : 0 < R := by dsimp [R]; linarith only [hu₀.1, hu₀.2]
  have hc : 0 < c := mul_pos hl (Real.exp_pos _)
  have hc_le_l : c ≤ l := by
    dsimp [c]
    have harg : -(C * R ^ 2) ≤ 0 := neg_nonpos.mpr (mul_nonneg hC (sq_nonneg R))
    have hexp : Real.exp (-(C * R ^ 2)) ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr harg
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hl.le
  refine ⟨vBar, c, hu₀u₁.trans hu₁vBar, hvBarStar, hc, ?_⟩
  intro b hb u v hu huv hvBarv hvb
  by_cases huu₁ : u ≤ u₁
  · exact hc_le_l.trans (hfloor b hb u v hu huu₁ hvBarv hvb).1
  have hu₀u : u₀ < u := hu₀u₁.trans (lt_of_not_ge huu₁)
  have hseed : l ≤ (S b).lam u₀ v :=
    (hfloor b hb u₀ v hu₀.1.le hu₀u₁.le hvBarv hvb).1
  have hsegmass : ∀ s ∈ Ioo u₀ u,
      2 * (S b).m s v / (S b).r s v ≤
        B ^ 2 / 12 * ((S b).r s v) ^ 2 := by
    intro s hs
    exact hmass b hb s v hs.1 (hs.2.trans huv) hvb
  have hseggap : ∀ s ∈ Ioo u₀ u,
      1 - ε ≤ 1 - 2 * (S b).m s v / (S b).r s v := by
    intro s hs
    have hdev : (s, v) ∈ openDevelopment u₀ vStar :=
      ⟨⟨hs.1, (hs.2.trans huv).trans (hvb.trans hb.2)⟩,
        ⟨hs.2.trans huv, hvb.trans hb.2⟩⟩
    have hmember : (s, v) ∈ developmentWithInitialEdge b :=
      ⟨hu₀.1.le.trans hs.1.le, hs.2.trans huv, hvb⟩
    linarith only [htail b hb (s, v) ⟨hdev, hmember⟩]
  have hpoint := lam_lower_of_cubic_mass_on_incoming (hfamily b hb).1
    hu₀.1 hu₀u huv hvb hq₀ hsegmass hseggap
  have hr0 : 0 < (S b).r u₀ v :=
    (hfamily b hb).1.solution.radius_pos (u₀, v)
      ⟨hu₀.1.le, hu₀u.trans huv, hvb⟩
  have hrad : (S b).r u₀ v ≤ (S b).r 0 v :=
    radius_antitone_on_incoming_of_c1 (hfamily b hb).1
      (le_refl 0) hu₀.1.le (hu₀u.trans huv) hvb
  have hinit : (S b).r 0 v = v / 2 :=
    ((hfamily b hb).2 v ⟨hu₀.1.trans (hu₀u.trans huv), hvb⟩).1
  have hradR : (S b).r u₀ v ≤ R := by
    rw [hinit] at hrad
    dsimp [R]
    linarith only [hrad, hvb, hb.2]
  have hsquare : ((S b).r u₀ v) ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ hr0.le hR.le).2 hradR
  have hexp : Real.exp (-(C * R ^ 2)) ≤
      Real.exp (-(C * ((S b).r u₀ v) ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hsquare hC
    linarith only [hmul]
  have hseedprod : c ≤ (S b).lam u₀ v *
      Real.exp (-(C * ((S b).r u₀ v) ^ 2)) := by
    dsimp [c]
    calc
      l * Real.exp (-(C * R ^ 2)) ≤
          l * Real.exp (-(C * ((S b).r u₀ v) ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp hl.le
      _ ≤ (S b).lam u₀ v *
          Real.exp (-(C * ((S b).r u₀ v) ^ 2)) :=
        mul_le_mul_of_nonneg_right hseed (Real.exp_nonneg _)
  have hexpEq : Real.exp (-(C * ((S b).r u₀ v) ^ 2)) =
      Real.exp (-(B ^ 2 / (24 * (1 - ε))) * ((S b).r u₀ v) ^ 2) := by
    congr 1
    dsimp [C]
    ring
  rw [hexpEq] at hseedprod
  exact hseedprod.trans hpoint

/-- The expansion has a positive lower bound on the whole compatible old
union, with one constant independent of the family cutoff. -/
theorem exists_expansion_floor_before_star
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
    ∃ c : ℝ, 0 < c ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 ≤ u → u < v → v < b →
          c ≤ (S b).lam u v := by
  obtain ⟨vBar, cTail, hu₀Bar, hBarStar, hcTail, htailfloor⟩ :=
    exists_expansion_floor_on_terminal_tail_before_star
      hu₀ hα hfamily hε1 htail
  obtain ⟨b₀, hb₀, H₀⟩ :=
    exists_family_member_beyond_cutoff (hu₀.1.trans hu₀Bar)
      hBarStar hfamily
  have hb₀Star : b₀ ∈ Ioo (0 : ℝ) vStar :=
    ⟨(hu₀.1.trans hu₀Bar).trans hb₀.1, hb₀.2⟩
  obtain ⟨c₀, hc₀, hcl⟩ := H₀.lam_bounded_below
  refine ⟨min c₀ cTail, lt_min hc₀ hcTail, ?_⟩
  intro b hb u v hu huv hvb
  by_cases hBarv : vBar ≤ v
  · exact (min_le_right c₀ cTail).trans
      (htailfloor b hb u v hu huv hBarv hvb)
  have hvBar : v < vBar := lt_of_not_ge hBarv
  have hp₀ : (u, v) ∈ developmentWithInitialEdge b₀ :=
    ⟨hu, huv, hvBar.trans (hb₀.1)⟩
  have hfields := family_fields_eq_on_common_development
    hfamily hb hb₀Star
      (show (u, v) ∈ developmentWithInitialEdge b ∩
        developmentWithInitialEdge b₀ from
        ⟨⟨hu, huv, hvb⟩, hp₀⟩)
  exact (min_le_left c₀ cTail).trans (by
    rw [hfields.2.2.2.1]
    exact hcl (u, v) hp₀)

end ChristodoulouBV.Uniqueness

end
