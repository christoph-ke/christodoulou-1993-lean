module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.AttenuatedVolterraAxisHorizontal
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Simultaneous uniform axis expansions

The diagonal coefficients are supplied by the source's quadratic amplitude
and horizontal first-jet amplitude. A single delta controls all three errors.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- A quadratic source with diagonal amplitudes `weight h²/4` and `-weight h²/2`
has the cubic and quadratic axis coefficients, with one modulus over the
whole compact diagonal. -/
theorem attenuatedVolterraIntegral_uniform_axis_coefficients
    {a b J₀ J₁ K₀ K₁ : ℝ}
    {j k A B weight h : ℝ × ℝ → ℝ}
    (hab : a < b)
    (hj : ContDiffOn ℝ 1 j (closedCoordTriangle a b))
    (hk : ContDiffOn ℝ 1 k (closedCoordTriangle a b))
    (hA : ContinuousOn A (closedCoordTriangle a b))
    (hB : ContinuousOn B (closedCoordTriangle a b))
    (hjdiag : ∀ x ∈ Icc a b, j (x, x) = 0)
    (hJ₀ : 0 ≤ J₀) (hJ₁ : 0 ≤ J₁)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁)
    (hsource : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ j p ∧ j p ≤ J₀ * (p.2 - p.1) ^ 2 ∧
        j p = (p.2 - p.1) ^ 2 * A p)
    (hkernel : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ k p ∧ k p ≤ K₀ * (p.2 - p.1))
    (hjet : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ j (closedCoordTriangle a b) p) (1, 0)| ≤
        J₁ * (p.2 - p.1) ∧
      (fderivWithin ℝ j (closedCoordTriangle a b) p) (1, 0) =
        (p.2 - p.1) * B p)
    (hkjet : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ k (closedCoordTriangle a b) p) (1, 0)| ≤ K₁)
    (hAdiag : ∀ x ∈ Icc a b, A (x, x) = weight (x, x) * h (x, x) ^ 2 / 4)
    (hBdiag : ∀ x ∈ Icc a b, B (x, x) = -weight (x, x) * h (x, x) ^ 2 / 2) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b → v - u < δ →
        |attenuatedVolterraIntegral j k u v -
          weight (u, u) * h (u, u) ^ 2 * (v - u) ^ 3 / 12| ≤
            ε * (v - u) ^ 3 ∧
        |(fderivWithin ℝ (fun p : ℝ × ℝ =>
            attenuatedVolterraIntegral j k p.1 p.2)
            (closedCoordTriangle a b) (u, v)) (0, 1) -
          weight (u, u) * h (u, u) ^ 2 * (v - u) ^ 2 / 4| ≤
            ε * (v - u) ^ 2 ∧
        |(fderivWithin ℝ (fun p : ℝ × ℝ =>
            attenuatedVolterraIntegral j k p.1 p.2)
            (closedCoordTriangle a b) (u, v)) (1, 0) +
          weight (u, u) * h (u, u) ^ 2 * (v - u) ^ 2 / 4| ≤
            ε * (v - u) ^ 2 := by
  intro ε hε
  obtain ⟨δ₀, hδ₀, hval⟩ := attenuatedVolterraIntegral_uniform_axis_value
    hj.continuousOn hk.continuousOn hA hJ₀ hK₀ hsource hkernel ε hε
  obtain ⟨δ₁, hδ₁, hver⟩ := attenuatedVolterraIntegral_uniform_axis_vertical
    hab hj hk hA hJ₀ hK₀ hsource hkernel ε hε
  obtain ⟨δ₂, hδ₂, hhor⟩ := attenuatedVolterraIntegral_uniform_axis_horizontal
    hab hj hk hB hjdiag hJ₀ hJ₁ hK₀ hK₁
    (fun p hp => ⟨(hsource p hp).1, (hsource p hp).2.1⟩)
    hkernel hjet hkjet ε hε
  refine ⟨min δ₀ (min δ₁ δ₂), lt_min hδ₀ (lt_min hδ₁ hδ₂), ?_⟩
  intro u v hu huv hv hgap
  have huI : u ∈ Icc a b := ⟨hu, huv.trans hv⟩
  have hgap₀ : v - u < δ₀ := lt_of_lt_of_le hgap (min_le_left _ _)
  have hgap₁ : v - u < δ₁ :=
    lt_of_lt_of_le hgap ((min_le_right _ _).trans (min_le_left _ _))
  have hgap₂ : v - u < δ₂ :=
    lt_of_lt_of_le hgap ((min_le_right _ _).trans (min_le_right _ _))
  have h₀ := hval u v hu huv hv hgap₀
  have h₁ := hver u v hu huv hv hgap₁
  have h₂ := hhor u v hu huv hv hgap₂
  rw [hAdiag u huI] at h₀ h₁
  rw [hBdiag u huI] at h₂
  convert And.intro h₀ (And.intro h₁ h₂) using 1 <;> ring

end intervalIntegral

end
