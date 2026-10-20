module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceNu
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceUnconditional
public import ChristodoulouBV.Uniqueness.ExtensionIncomingNu
import ChristodoulouBV.Uniqueness.ExtensionIncomingRadius
import ChristodoulouBV.Uniqueness.ExtensionCutoff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Uniform incoming expansion bound on the compatible old family

The incoming off-axis bound and a regular-axis growth comparison cover the
terminal tail. One fixed family member controls the earlier compact part.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The incoming expansion is uniformly bounded on the full near-top
triangle of every old family member. -/
theorem exists_nu_bound_on_terminal_tail_before_star
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
    ∃ vBar N : ℝ, u₀ < vBar ∧ vBar < vStar ∧ 0 ≤ N ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 ≤ u → u < v → vBar ≤ v → v < b →
          |(S b).nu u v| ≤ N := by
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
  obtain ⟨B, _, _, _, _, hmass⟩ :=
    exists_uniform_scalar_and_cubic_mass_bounds_before_star
      hu₀ hα hfamily hε1 htail
  obtain ⟨N₁, hN₁, hoffaxis⟩ :=
    exists_nu_bound_closed_before_star
      (hu₀.1.trans hu₀u₁) hu₁vBar hvBarStar hα hfamily
  let R : ℝ := vStar / 2
  let C : ℝ := B ^ 2 * R / (24 * (1 - ε))
  let N₂ : ℝ := (1 / 2 : ℝ) * Real.exp (C * vStar)
  let N : ℝ := max N₁ N₂
  have hR : 0 < R := by dsimp [R]; linarith only [hu₀.1, hu₀.2]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨vBar, N, hu₀u₁.trans hu₁vBar, hvBarStar,
    hN₁.trans (le_max_left N₁ N₂), ?_⟩
  intro b hb u v hu huv hvBarv hvb
  by_cases huu₁ : u ≤ u₁
  · exact (hoffaxis b hb u v hu huu₁ hvBarv hvb).trans
      (le_max_left N₁ N₂)
  have hu₀u : u₀ < u := hu₀u₁.trans (lt_of_not_ge huu₁)
  have hu : 0 < u := hu₀.1.trans hu₀u
  have hsegmass : ∀ w ∈ Ioo u v,
      2 * (S b).m u w / (S b).r u w ≤
        B ^ 2 / 12 * ((S b).r u w) ^ 2 := by
    intro w hw
    exact hmass b hb u w hu₀u hw.1 (hw.2.trans hvb)
  have hseggap : ∀ w ∈ Ioo u v,
      1 - ε ≤ 1 - 2 * (S b).m u w / (S b).r u w := by
    intro w hw
    have hdev : (u, w) ∈ openDevelopment u₀ vStar :=
      ⟨⟨hu₀u, hw.1.trans (hw.2.trans (hvb.trans hb.2))⟩,
        ⟨hw.1, hw.2.trans (hvb.trans hb.2)⟩⟩
    have hmember : (u, w) ∈ developmentWithInitialEdge b :=
      ⟨hu.le, hw.1, hw.2.trans hvb⟩
    linarith only [htail b hb (u, w) ⟨hdev, hmember⟩]
  have hrUpper : ∀ w ∈ Ioo u v, (S b).r u w ≤ R := by
    intro w hw
    have hrad : (S b).r u w ≤ (S b).r 0 w :=
      radius_antitone_on_incoming_of_c1 (hfamily b hb).1
        (le_refl 0) hu.le hw.1 (hw.2.trans hvb)
    have hinit : (S b).r 0 w = w / 2 :=
      ((hfamily b hb).2 w ⟨hu.trans hw.1, hw.2.trans hvb⟩).1
    rw [hinit] at hrad
    dsimp [R]
    linarith only [hrad, hw.2, hvb, hb.2]
  have hpoint := nu_abs_le_of_cubic_mass_on_outgoing (hfamily b hb).1
    (fun w hw => ((hfamily b hb).2 w hw).1)
    hu huv hvb hq₀ hsegmass hseggap hrUpper
  have htime : v - u ≤ vStar := by
    linarith only [hu, hvb, hb.2]
  have hexp : Real.exp (C * (v - u)) ≤ Real.exp (C * vStar) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htime hC)
  have hbound : (1 / 2 : ℝ) * Real.exp (C * (v - u)) ≤ N₂ := by
    dsimp [N₂]
    exact mul_le_mul_of_nonneg_left hexp (by norm_num)
  have hpoint' : |(S b).nu u v| ≤ (1 / 2 : ℝ) *
      Real.exp (C * (v - u)) := by simpa only [C] using hpoint
  exact hpoint'.trans (hbound.trans (le_max_right N₁ N₂))

/-- The incoming expansion is uniformly bounded on the whole old union. -/
theorem exists_nu_bound_before_star_from_cubic_mass
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
    ∃ N : ℝ, 0 ≤ N ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 ≤ u → u < v → v < b →
          |(S b).nu u v| ≤ N := by
  obtain ⟨vBar, N₁, hu₀Bar, hBarStar, hN₁, htailbound⟩ :=
    exists_nu_bound_on_terminal_tail_before_star
      hu₀ hα hfamily hε1 htail
  obtain ⟨b₀, hb₀, H₀⟩ :=
    exists_family_member_beyond_cutoff (hu₀.1.trans hu₀Bar)
      hBarStar hfamily
  have hb₀Star : b₀ ∈ Ioo (0 : ℝ) vStar :=
    ⟨(hu₀.1.trans hu₀Bar).trans hb₀.1, hb₀.2⟩
  obtain ⟨N₀, hN₀⟩ := H₀.nu_bounded_below
  let N := max (max 0 N₀) N₁
  refine ⟨N, (le_max_left 0 N₀).trans (le_max_left _ _), ?_⟩
  intro b hb u v hu huv hvb
  by_cases hBarv : vBar ≤ v
  · exact (htailbound b hb u v hu huv hBarv hvb).trans
      (le_max_right _ _)
  have hvBar : v < vBar := lt_of_not_ge hBarv
  have hp₀ : (u, v) ∈ developmentWithInitialEdge b₀ :=
    ⟨hu, huv, hvBar.trans hb₀.1⟩
  have hfields := family_fields_eq_on_common_development
    hfamily hb hb₀Star
      (show (u, v) ∈ developmentWithInitialEdge b ∩
        developmentWithInitialEdge b₀ from
        ⟨⟨hu, huv, hvb⟩, hp₀⟩)
  have hneg : (S b).nu u v < 0 :=
    ((hfamily b hb).1.reduced_signs_of_c1
      (show (u, v) ∈ developmentWithInitialEdge b from
        ⟨hu, huv, hvb⟩)).1
  rw [abs_of_neg hneg, hfields.2.2.2.2.1]
  exact (hN₀ (u, v) hp₀).trans
    ((le_max_right 0 N₀).trans (le_max_left _ _))

end ChristodoulouBV.Uniqueness

end
