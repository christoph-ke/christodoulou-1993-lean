module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingRadius
public import ChristodoulouBV.Uniqueness.ExtensionFamily
import Mathlib.Tactic.Linarith

/-!
# A cutoff independent radius floor for the compatible family

All family members agree at a fixed off-axis corner. The radius signs then
give that corner radius as a common floor on the entire exhausting strip.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A single positive radius floor
works for every compatible member on the strip below `u₁` and above `vBar`.
It depends on the family at one fixed corner, not on the outgoing cutoff. -/
theorem exists_radius_floor_before_star
    {alpha₀ : ℝ → ℝ} {vStar u₁ vBar : ℝ} {S : ℝ → Fields}
    (hu₁ : 0 ≤ u₁) (hu₁v : u₁ < vBar) (hvStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 ≤ u → u ≤ u₁ → vBar ≤ v → v < b →
          ρ ≤ (S b).r u v := by
  let b₀ : ℝ := (vBar + vStar) / 2
  have hvBar : 0 < vBar := hu₁.trans_lt hu₁v
  have hBarB₀ : vBar < b₀ := by dsimp [b₀]; linarith
  have hB₀Star : b₀ < vStar := by dsimp [b₀]; linarith
  have hb₀ : b₀ ∈ Ioo (0 : ℝ) vStar :=
    ⟨hvBar.trans hBarB₀, hB₀Star⟩
  let ρ := (S b₀).r u₁ vBar
  have hρ : 0 < ρ :=
    (hfamily b₀ hb₀).1.solution.radius_pos (u₁, vBar)
      ⟨hu₁, hu₁v, hBarB₀⟩
  refine ⟨ρ, hρ, ?_⟩
  intro b hb u v hu huu₁ hvBarv hvb
  have hBarb : vBar < b := hvBarv.trans_lt hvb
  have hcorner₀ : (u₁, vBar) ∈ developmentWithInitialEdge b₀ :=
    ⟨hu₁, hu₁v, hBarB₀⟩
  have hcornerb : (u₁, vBar) ∈ developmentWithInitialEdge b :=
    ⟨hu₁, hu₁v, hBarb⟩
  have heq := (family_fields_eq_on_common_development hfamily hb₀ hb
    ⟨hcorner₀, hcornerb⟩).1
  change (S b₀).r u₁ vBar ≤ (S b).r u v
  rw [heq]
  exact radius_lower_on_offaxis_rectangle_of_c1 (hfamily b hb).1
    hu huu₁ hu₁v hvBarv hvb

end ChristodoulouBV.Uniqueness

end
