module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.AttenuatedVolterraAxisValue
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Quadratic vertical axis estimate for attenuated Volterra integrals
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- The vertical first jet has the quadratic axis coefficient of the source.
The attenuation correction is fourth order. -/
theorem abs_fderivWithin_attenuatedVolterraIntegral_vertical_sub_axis_le
    {a b u v J₀ K₀ η : ℝ} {j k A : ℝ × ℝ → ℝ}
    (hab : a < b) (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b)
    (hj : ContDiffOn ℝ 1 j (closedCoordTriangle a b))
    (hk : ContDiffOn ℝ 1 k (closedCoordTriangle a b))
    (_hJ₀ : 0 ≤ J₀) (hK₀ : 0 ≤ K₀) (_hη : 0 ≤ η)
    (hsource : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ j p ∧ j p ≤ J₀ * (p.2 - p.1) ^ 2 ∧
        j p = (p.2 - p.1) ^ 2 * A p)
    (hkernel : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ k p ∧ k p ≤ K₀ * (p.2 - p.1))
    (hmod : |A (u, v) - A (u, u)| ≤ η) :
    |(fderivWithin ℝ (fun p : ℝ × ℝ =>
        attenuatedVolterraIntegral j k p.1 p.2)
        (closedCoordTriangle a b) (u, v)) (0, 1) -
      A (u, u) * (v - u) ^ 2| ≤
      (η + K₀ * J₀ * (v - u) ^ 2 / 3) * (v - u) ^ 2 := by
  let d := v - u
  have hp : (u, v) ∈ closedCoordTriangle a b := ⟨hu, huv, hv⟩
  have hd : 0 ≤ d := sub_nonneg.mpr huv
  have hsrc := hsource (u, v) hp
  have hker := hkernel (u, v) hp
  have hJ := attenuatedVolterraIntegral_nonneg_le hu huv hv
    hj.continuousOn hk.continuousOn (fun p hp => (hkernel p hp).1)
    (fun p hp => ⟨(hsource p hp).1, (hsource p hp).2.1⟩)
  have hfirst : |j (u, v) - A (u, u) * d ^ 2| ≤ η * d ^ 2 := by
    rw [hsrc.2.2]
    change |d ^ 2 * A (u, v) - A (u, u) * d ^ 2| ≤ _
    rw [mul_comm (d ^ 2) (A (u, v)), ← sub_mul, abs_mul]
    simpa only [abs_of_nonneg (sq_nonneg d)] using
      mul_le_mul_of_nonneg_right hmod (sq_nonneg d)
  have hsecond : 0 ≤ k (u, v) * attenuatedVolterraIntegral j k u v ∧
      k (u, v) * attenuatedVolterraIntegral j k u v ≤
        K₀ * J₀ * d ^ 4 / 3 := by
    constructor
    · exact mul_nonneg hker.1 hJ.1
    · calc
        _ ≤ (K₀ * d) * attenuatedVolterraIntegral j k u v :=
          mul_le_mul_of_nonneg_right hker.2 hJ.1
        _ ≤ (K₀ * d) * (J₀ * d ^ 3 / 3) :=
          mul_le_mul_of_nonneg_left hJ.2 (mul_nonneg hK₀ hd)
        _ = _ := by ring
  rw [fderivWithin_attenuatedVolterraIntegral_vertical hab hj hk hp]
  change |j (u, v) - k (u, v) * attenuatedVolterraIntegral j k u v -
    A (u, u) * d ^ 2| ≤ _
  rw [show j (u, v) - k (u, v) * attenuatedVolterraIntegral j k u v -
    A (u, u) * d ^ 2 = (j (u, v) - A (u, u) * d ^ 2) -
      k (u, v) * attenuatedVolterraIntegral j k u v by ring]
  have h := abs_add_le (j (u, v) - A (u, u) * d ^ 2)
    (-(k (u, v) * attenuatedVolterraIntegral j k u v))
  simp only [abs_neg, ← sub_eq_add_neg, abs_of_nonneg hsecond.1] at h
  nlinarith only [h, hfirst, hsecond.2]

/-- The vertical quadratic expansion is uniform over the compact diagonal. -/
theorem attenuatedVolterraIntegral_uniform_axis_vertical
    {a b J₀ K₀ : ℝ} {j k A : ℝ × ℝ → ℝ}
    (hab : a < b)
    (hj : ContDiffOn ℝ 1 j (closedCoordTriangle a b))
    (hk : ContDiffOn ℝ 1 k (closedCoordTriangle a b))
    (hA : ContinuousOn A (closedCoordTriangle a b))
    (hJ₀ : 0 ≤ J₀) (hK₀ : 0 ≤ K₀)
    (hsource : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ j p ∧ j p ≤ J₀ * (p.2 - p.1) ^ 2 ∧
        j p = (p.2 - p.1) ^ 2 * A p)
    (hkernel : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ k p ∧ k p ≤ K₀ * (p.2 - p.1)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b → v - u < δ →
        |(fderivWithin ℝ (fun p : ℝ × ℝ =>
            attenuatedVolterraIntegral j k p.1 p.2)
            (closedCoordTriangle a b) (u, v)) (0, 1) -
          A (u, u) * (v - u) ^ 2| ≤ ε * (v - u) ^ 2 := by
  intro ε hε
  obtain ⟨δA, hδA, hmod⟩ := uniform_diagonal_continuity hA (ε / 2) (by linarith)
  let C := K₀ * J₀
  have hC : 0 ≤ C := mul_nonneg hK₀ hJ₀
  let δ := min δA (min 1 (ε / (1 + C)))
  have hδ : 0 < δ := lt_min hδA
    (lt_min (by norm_num) (div_pos hε (by linarith)))
  refine ⟨δ, hδ, ?_⟩
  intro u v hu huv hv hgap
  have hd0 : 0 ≤ v - u := sub_nonneg.mpr huv
  have hd1 : v - u ≤ 1 :=
    (le_of_lt hgap).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmall : v - u < ε / (1 + C) :=
    lt_of_lt_of_le hgap ((min_le_right _ _).trans (min_le_right _ _))
  have hCd : C * (v - u) ^ 2 ≤ ε := by
    have hmul : (1 + C) * (v - u) < ε := by
      simpa only [mul_comm] using
        (lt_div_iff₀ (by linarith : 0 < 1 + C)).mp hsmall
    have hsquare : (v - u) ^ 2 ≤ v - u := by nlinarith only [hd0, hd1]
    have h := mul_le_mul_of_nonneg_left hsquare hC
    nlinarith only [h, hmul, hd0]
  have hmod' : |A (u, v) - A (u, u)| ≤ ε / 2 :=
    (hmod u v hu huv hv (lt_of_lt_of_le hgap (min_le_left _ _))).le
  have hlocal := abs_fderivWithin_attenuatedVolterraIntegral_vertical_sub_axis_le
    hab hu huv hv hj hk hJ₀ hK₀ (by linarith : 0 ≤ ε / 2)
    hsource hkernel hmod'
  have hcoef : ε / 2 + K₀ * J₀ * (v - u) ^ 2 / 3 ≤ ε := by
    dsimp [C] at hCd
    linarith
  have := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (v - u))
  nlinarith only [hlocal, this]

end intervalIntegral

end
