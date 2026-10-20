module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceFamilyExpansion
import ChristodoulouBV.C1Solution.Extraction
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMeanIntegral
import Mathlib.Tactic.Linarith

/-!
# A uniform radius floor on the old compatible family

The cutoff-independent expansion floor extends to the closed triangle by
continuity. Integrating it from the regular axis gives a uniform linear
radius floor.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- On the strict old union, the radius is bounded below by the coordinate
distance from the axis with one cutoff-independent coefficient. -/
theorem exists_uniform_radius_floor_before_star
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
          c * (v - u) ≤ (S b).r u v := by
  obtain ⟨c, hc, hfloor⟩ :=
    exists_expansion_floor_before_star hu₀ hα hfamily hε1 htail
  refine ⟨c, hc, ?_⟩
  intro b hb u v hu huv hvb
  let B : ℝ := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v ≤ B := by dsimp [B]; linarith
  let K := closedCoordTriangle 0 B
  let O := openCoordTriangle 0 B
  have hlamCont : ContinuousOn (fun p : ℝ × ℝ => (S b).lam p.1 p.2) K :=
    (C1Solution.five_fields_contDiffOn hB hBb (hfamily b hb).1).1.continuousOn
  have hfloorOpen : ∀ p ∈ O, c ≤ (S b).lam p.1 p.2 := by
    intro p hp
    exact hfloor b hb p.1 p.2 hp.1.le hp.2.1 (hp.2.2.trans hBb)
  have hclosure : closure O = K := closure_openCoordTriangle hB
  have hfloorClosed : ∀ p ∈ K, c ≤ (S b).lam p.1 p.2 := by
    intro p hp
    exact le_on_closure hfloorOpen
      (by rw [hclosure]; exact continuousOn_const)
      (by rw [hclosure]; exact hlamCont)
      (by rw [hclosure]; exact hp)
  have hrCanonical : c * (v - u) ≤
      C1Solution.canonicalRadius (S b) (u, v) := by
    exact intervalIntegral.mul_sub_le_weightedDiagonalRadius
      hlamCont hfloorClosed hu huv.le hvB
  rwa [C1Solution.canonicalRadius_eq_radius hB hBb
    (hfamily b hb).1 hu huv hvB] at hrCanonical

end ChristodoulouBV.Uniqueness

end
