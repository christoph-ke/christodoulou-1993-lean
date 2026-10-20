module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableGapPower
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.AttenuatedVolterraAxis
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Uniform axis coefficients for normalized gap quotients

A uniform expansion stated with the coefficient at `(u,u)` also yields a
continuous normalized quotient. This is the form produced by diagonal
Volterra asymptotics.
-/

public section

open Set

namespace intervalIntegral

/-- A uniform diagonal expansion with a continuous axis coefficient yields
continuity of the normalized quotient on the closed triangle. -/
theorem continuousOn_gapPowerQuotient_of_uniform_diagonal_axis
    {a b : ℝ} {n : ℕ} {f A : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hA : ContinuousOn A (closedCoordTriangle a b))
    (haxis : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b → v - u < δ →
        |f (u, v) - A (u, u) * (v - u) ^ n| ≤
          ε * (v - u) ^ n) :
    ContinuousOn (gapPowerQuotient n f A) (closedCoordTriangle a b) := by
  apply continuousOn_gapPowerQuotient_of_uniform_axis hf hA
  intro ε hε
  have hε₂ : 0 < ε / 2 := by positivity
  obtain ⟨δ₁, hδ₁, h₁⟩ := haxis (ε / 2) hε₂
  obtain ⟨δ₂, hδ₂, h₂⟩ := uniform_diagonal_continuity hA (ε / 2) hε₂
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  rintro ⟨u, v⟩ hp hgap
  change a ≤ u ∧ u ≤ v ∧ v ≤ b at hp
  have hd : 0 ≤ v - u := sub_nonneg.mpr hp.2.1
  have hpow : 0 ≤ (v - u) ^ n := pow_nonneg hd n
  have hfirst := h₁ u v hp.1 hp.2.1 hp.2.2
    (lt_of_lt_of_le hgap (min_le_left _ _))
  have hsecond := h₂ u v hp.1 hp.2.1 hp.2.2
    (lt_of_lt_of_le hgap (min_le_right _ _))
  have hid : f (u, v) - A (u, v) * (v - u) ^ n =
      (f (u, v) - A (u, u) * (v - u) ^ n) +
        (A (u, u) - A (u, v)) * (v - u) ^ n := by ring
  rw [hid]
  have hterm : |(A (u, u) - A (u, v)) * (v - u) ^ n| ≤
      (ε / 2) * (v - u) ^ n := by
    rw [abs_mul, abs_of_nonneg hpow, abs_sub_comm]
    exact mul_le_mul_of_nonneg_right hsecond.le hpow
  have h := (abs_add_le _ _).trans (add_le_add hfirst hterm)
  convert h using 1
  ring

end intervalIntegral

end
