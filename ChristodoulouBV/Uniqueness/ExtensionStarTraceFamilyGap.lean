module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingFamilyTailGap
import ChristodoulouBV.Uniqueness.ExtensionCutoff
import ChristodoulouBV.C1Solution.ExtractionMass
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# Uniform mass gap on the compatible old union

The incoming strip estimate controls the off-axis lower terminal strip, the tail premise controls
the upper terminal triangle, and one C¹ member controls the earlier compact
part through its canonical mass ratio.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The positive mass gap has one floor at every strict point of every old
member. This floor is independent of the member's outgoing cutoff. -/
theorem exists_mass_gap_floor_before_star
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε : ε < 1)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    ∃ q : ℝ, 0 < q ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 ≤ u → u < v → v < b →
          q ≤ 1 - 2 * (S b).m u v / (S b).r u v := by
  let u₁ : ℝ := (u₀ + vStar) / 2
  let vBar : ℝ := (u₁ + vStar) / 2
  have hu₀u₁ : u₀ < u₁ := by dsimp [u₁]; linarith only [hu₀.2]
  have hu₁Bar : u₁ < vBar := by dsimp [vBar, u₁]; linarith only [hu₀.2]
  have hBarStar : vBar < vStar := by dsimp [vBar, u₁]; linarith only [hu₀.2]
  obtain ⟨_, qStrip, _, hqStrip, hstrip⟩ :=
    exists_expansion_and_gap_floor_before_star
      hu₀.1 hu₀u₁ hu₁Bar hBarStar hε hα hfamily htail
  obtain ⟨b₀, hb₀, H₀⟩ :=
    exists_family_member_beyond_cutoff
      (hu₀.1.trans (hu₀u₁.trans hu₁Bar)) hBarStar hfamily
  have hb₀Star : b₀ ∈ Ioo (0 : ℝ) vStar :=
    ⟨(hu₀.1.trans (hu₀u₁.trans hu₁Bar)).trans hb₀.1, hb₀.2⟩
  let T : ℝ := (vBar + b₀) / 2
  have hT : 0 < T := by dsimp [T]; linarith only [hu₀.1, hu₀u₁, hu₁Bar, hb₀.1]
  have hBarT : vBar < T := by dsimp [T]; linarith only [hb₀.1]
  have hTb₀ : T < b₀ := by dsimp [T]; linarith only [hb₀.1]
  obtain ⟨qCompact, hqCompact, hcompact⟩ :=
    C1Solution.exists_canonical_mass_gap_lower_bound hT hTb₀ H₀
  let q : ℝ := min qStrip (min (1 - ε) qCompact)
  have hq : 0 < q := lt_min hqStrip (lt_min (by linarith only [hε]) hqCompact)
  refine ⟨q, hq, ?_⟩
  intro b hb u v hu huv hvb
  by_cases hBarv : vBar ≤ v
  · by_cases huu₁ : u ≤ u₁
    · exact (min_le_left _ _).trans
        (hstrip b hb u v hu huu₁ hBarv hvb).2
    have hu₀u : u₀ < u := hu₀u₁.trans (lt_of_not_ge huu₁)
    have htailpoint := htail b hb (u, v)
      (show (u, v) ∈ openDevelopment u₀ vStar ∩
        developmentWithInitialEdge b from
        ⟨⟨⟨hu₀u, huv.trans (hvb.trans hb.2)⟩,
            ⟨huv, hvb.trans hb.2⟩⟩,
          ⟨hu, huv, hvb⟩⟩)
    have htailgap : 1 - ε ≤ 1 - 2 * (S b).m u v / (S b).r u v := by
      linarith only [htailpoint]
    exact ((min_le_right _ _).trans (min_le_left _ _)).trans htailgap
  have hvBar : v < vBar := lt_of_not_ge hBarv
  have hp₀ : (u, v) ∈ developmentWithInitialEdge b₀ :=
    ⟨hu, huv, hvBar.trans hb₀.1⟩
  have hfields := family_fields_eq_on_common_development
    hfamily hb hb₀Star
      (show (u, v) ∈ developmentWithInitialEdge b ∩
        developmentWithInitialEdge b₀ from
        ⟨⟨hu, huv, hvb⟩, hp₀⟩)
  have hK : (u, v) ∈ closedCoordTriangle 0 T :=
    by
      change 0 ≤ u ∧ u ≤ v ∧ v ≤ T
      exact ⟨hu, huv.le, (hvBar.trans hBarT).le⟩
  have hpoint := hcompact (u, v) hK
  rw [C1Solution.canonicalMassRatio_eq_mass_ratio H₀ hp₀] at hpoint
  rw [hfields.1, hfields.2.2.1]
  exact ((min_le_right _ _).trans (min_le_right _ _)).trans hpoint

end ChristodoulouBV.Uniqueness

end
