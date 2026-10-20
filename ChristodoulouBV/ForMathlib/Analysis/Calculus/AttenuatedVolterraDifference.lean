module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.AttenuatedVolterraBounds
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Two-input first-jet bounds for attenuated Volterra integrals

The vertical estimate follows directly from the Volterra differential
equation and the cubic two-input value estimate.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- The difference of two vertical first jets has a quadratic bound with
the three terms from the source, kernel, and Volterra-value differences. -/
theorem abs_fderivWithin_attenuatedVolterraIntegral_vertical_sub_le
    {a b u v J₀ K₀ JΔ KΔ D : ℝ}
    {j₁ j₂ k₁ k₂ : ℝ × ℝ → ℝ}
    (hab : a < b) (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b)
    (hsize : b - a ≤ 1)
    (hj₁ : ContDiffOn ℝ 1 j₁ (closedCoordTriangle a b))
    (hj₂ : ContDiffOn ℝ 1 j₂ (closedCoordTriangle a b))
    (hk₁ : ContDiffOn ℝ 1 k₁ (closedCoordTriangle a b))
    (hk₂ : ContDiffOn ℝ 1 k₂ (closedCoordTriangle a b))
    (hJ₀ : 0 ≤ J₀) (hK₀ : 0 ≤ K₀)
    (hJΔ : 0 ≤ JΔ) (hKΔ : 0 ≤ KΔ) (hD : 0 ≤ D)
    (hsource₁ : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ j₁ p ∧ j₁ p ≤ J₀ * (p.2 - p.1) ^ 2)
    (hsource₂ : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ j₂ p ∧ j₂ p ≤ J₀ * (p.2 - p.1) ^ 2)
    (hkernel₁ : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ k₁ p ∧ k₁ p ≤ K₀ * (p.2 - p.1))
    (hkernel₂ : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ k₂ p ∧ k₂ p ≤ K₀ * (p.2 - p.1))
    (hjdifference : ∀ p ∈ closedCoordTriangle a b,
      |j₁ p - j₂ p| ≤ JΔ * (p.2 - p.1) ^ 2 * D)
    (hkdifference : ∀ p ∈ closedCoordTriangle a b,
      |k₁ p - k₂ p| ≤ KΔ * (p.2 - p.1) * D) :
    |(fderivWithin ℝ (fun p : ℝ × ℝ =>
          attenuatedVolterraIntegral j₁ k₁ p.1 p.2)
          (closedCoordTriangle a b) (u, v)) (0, 1) -
      (fderivWithin ℝ (fun p : ℝ × ℝ =>
          attenuatedVolterraIntegral j₂ k₂ p.1 p.2)
          (closedCoordTriangle a b) (u, v)) (0, 1)| ≤
      (JΔ + KΔ * (J₀ / 3) +
        K₀ * (JΔ / 3 + J₀ * KΔ / 6)) * (v - u) ^ 2 * D := by
  let K := closedCoordTriangle a b
  let d := v - u
  let V₁ := attenuatedVolterraIntegral j₁ k₁ u v
  let V₂ := attenuatedVolterraIntegral j₂ k₂ u v
  have hp : (u, v) ∈ K := ⟨hu, huv, hv⟩
  have hd : 0 ≤ d ∧ d ≤ 1 := ⟨sub_nonneg.mpr huv, by dsimp [d]; linarith⟩
  have hd2 : d ^ 2 ≤ 1 := by nlinarith only [hd.1, hd.2]
  have hd4 : d ^ 4 ≤ d ^ 2 := by
    calc
      d ^ 4 = d ^ 2 * d ^ 2 := by ring
      _ ≤ d ^ 2 * 1 := mul_le_mul_of_nonneg_left hd2 (sq_nonneg d)
      _ = d ^ 2 := by ring
  have hV₁ := attenuatedVolterraIntegral_nonneg_le hu huv hv hj₁.continuousOn
    hk₁.continuousOn (fun p hp => (hkernel₁ p hp).1) hsource₁
  have hVdiff := abs_attenuatedVolterraIntegral_sub_le hu huv hv hsize
    hj₁.continuousOn hj₂.continuousOn hk₁.continuousOn hk₂.continuousOn
    (fun p hp => (hkernel₁ p hp).1)
    (fun p hp => (hkernel₂ p hp).1)
    hJ₀ hKΔ hD hsource₂ hjdifference hkdifference
  have hkd := hkdifference (u, v) hp
  have hkj := hkernel₂ (u, v) hp
  have hjd := hjdifference (u, v) hp
  have hdiffprod : |k₁ (u, v) * V₁ - k₂ (u, v) * V₂| ≤
      (KΔ * (J₀ / 3) + K₀ * (JΔ / 3 + J₀ * KΔ / 6)) * d ^ 2 * D := by
    have hfirst : |(k₁ (u, v) - k₂ (u, v)) * V₁| ≤
        KΔ * (J₀ / 3) * d ^ 2 * D := by
      rw [abs_mul, abs_of_nonneg hV₁.1]
      calc
        _ ≤ (KΔ * d * D) * V₁ :=
          mul_le_mul_of_nonneg_right hkd hV₁.1
        _ ≤ (KΔ * d * D) * (J₀ * d ^ 3 / 3) :=
          mul_le_mul_of_nonneg_left hV₁.2
            (by positivity)
        _ = (KΔ * (J₀ / 3) * D) * d ^ 4 := by ring
        _ ≤ (KΔ * (J₀ / 3) * D) * d ^ 2 :=
          mul_le_mul_of_nonneg_left hd4 (by positivity)
        _ = _ := by ring
    have hsecond : |k₂ (u, v) * (V₁ - V₂)| ≤
        K₀ * (JΔ / 3 + J₀ * KΔ / 6) * d ^ 2 * D := by
      rw [abs_mul, abs_of_nonneg hkj.1]
      calc
        _ ≤ (K₀ * d) * |V₁ - V₂| :=
          mul_le_mul_of_nonneg_right hkj.2 (abs_nonneg _)
        _ ≤ (K₀ * d) * ((JΔ / 3 + J₀ * KΔ / 6) * d ^ 3 * D) :=
          mul_le_mul_of_nonneg_left hVdiff (by positivity)
        _ = (K₀ * (JΔ / 3 + J₀ * KΔ / 6) * D) * d ^ 4 := by ring
        _ ≤ (K₀ * (JΔ / 3 + J₀ * KΔ / 6) * D) * d ^ 2 :=
          mul_le_mul_of_nonneg_left hd4 (by positivity)
        _ = _ := by ring
    calc
      _ = |(k₁ (u, v) - k₂ (u, v)) * V₁ + k₂ (u, v) * (V₁ - V₂)| := by
        congr 1
        ring
      _ ≤ |(k₁ (u, v) - k₂ (u, v)) * V₁| +
          |k₂ (u, v) * (V₁ - V₂)| := abs_add_le _ _
      _ ≤ _ := by nlinarith only [hfirst, hsecond]
  rw [fderivWithin_attenuatedVolterraIntegral_vertical hab hj₁ hk₁ hp,
    fderivWithin_attenuatedVolterraIntegral_vertical hab hj₂ hk₂ hp]
  have h := abs_add_le (j₁ (u, v) - j₂ (u, v))
    (-(k₁ (u, v) * V₁ - k₂ (u, v) * V₂))
  simp only [abs_neg, ← sub_eq_add_neg] at h
  have hval :
      |(j₁ (u, v) - k₁ (u, v) * V₁) -
          (j₂ (u, v) - k₂ (u, v) * V₂)| ≤
        |j₁ (u, v) - j₂ (u, v)| +
          |k₁ (u, v) * V₁ - k₂ (u, v) * V₂| := by
    convert h using 1
    ring
  have hfinal := hval.trans (add_le_add hjd hdiffprod)
  nlinarith only [hfinal]

end intervalIntegral

end
