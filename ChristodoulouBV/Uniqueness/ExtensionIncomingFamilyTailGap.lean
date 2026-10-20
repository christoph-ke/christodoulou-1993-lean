module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingFamilyLower
public import ChristodoulouBV.Uniqueness.ExtensionIncomingGap
public import ChristodoulouBV.Uniqueness.ExtensionIncomingFamilyQuotient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform expansion and mass gap from the tail line

The lower quotient bound and the mass bound at one later incoming coordinate
give positive lower bounds for `λ` and `1−μ` throughout the earlier strip.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The tail mass bound at `u₁` propagates a positive
expansion and mass gap backwards across the off-axis strip. -/
theorem exists_expansion_and_gap_floor_before_star
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
    ∃ l q : ℝ, 0 < l ∧ 0 < q ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 ≤ u → u ≤ u₁ → vBar ≤ v → v < b →
          l ≤ (S b).lam u v ∧
          q ≤ 1 - 2 * (S b).m u v / (S b).r u v := by
  have hu₁ : 0 < u₁ := hu₀.trans hu₀u₁
  obtain ⟨c, hc, hκlower⟩ :=
    exists_quotient_floor_before_star hu₁ hu₁v hvBarStar hα hfamily
  obtain ⟨K, hK, hκupper⟩ :=
    exists_quotient_ceiling_before_star hu₁.le hu₁v hvBarStar hα hfamily
  let l : ℝ := (1 - η) * c
  have hl : 0 < l := mul_pos (by linarith) hc
  let q : ℝ := l / K
  have hq : 0 < q := div_pos hl hK
  refine ⟨l, q, hl, hq, ?_⟩
  intro b hb u v hu huu₁ hvBarv hvb
  have hu₁v' : u₁ < v := hu₁v.trans_le hvBarv
  have hvStar : v < vStar := hvb.trans hb.2
  have htailpoint : 2 * (S b).m u₁ v / (S b).r u₁ v ≤ η := by
    apply htail b hb (u₁, v)
    refine ⟨?_, ?_⟩
    · exact ⟨⟨hu₀u₁, hu₁v'.trans hvStar⟩, ⟨hu₁v', hvStar⟩⟩
    · exact ⟨hu₁.le, hu₁v', hvb⟩
  have hκ₁ := hκlower b hb u₁ v hu₁.le le_rfl hvBarv hvb
  have hκu := hκupper b hb u v hu huu₁ hvBarv hvb
  have hlam := lam_lower_of_tail_quotient_lower (hfamily b hb).1
    hu huu₁ hu₁v' hvb hc.le htailpoint hκ₁
  have hgap := mass_gap_lower_of_tail_quotient_bounds (hfamily b hb).1
    hu huu₁ hu₁v' hvb hη hc hK htailpoint hκ₁ hκu
  exact ⟨hlam, hgap.2⟩

end ChristodoulouBV.Uniqueness

end
