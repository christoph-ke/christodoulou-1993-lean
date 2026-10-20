module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.AttenuatedVolterraAxis
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Cubic axis estimate for attenuated Volterra integrals

The estimate uses the diagonal value of the quadratic source amplitude. Its
error is controlled by one modulus along the entire compact diagonal.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- A local modulus for the quadratic source amplitude gives the cubic axis
coefficient; attenuation contributes only a fifth-order error. -/
theorem abs_attenuatedVolterraIntegral_sub_axis_le
    {a b u v J₀ K₀ η : ℝ} {j k A : ℝ × ℝ → ℝ}
    (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b)
    (hj : ContinuousOn j (closedCoordTriangle a b))
    (hk : ContinuousOn k (closedCoordTriangle a b))
    (hJ₀ : 0 ≤ J₀) (hK₀ : 0 ≤ K₀) (_hη : 0 ≤ η)
    (hsource : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ j p ∧ j p ≤ J₀ * (p.2 - p.1) ^ 2 ∧
        j p = (p.2 - p.1) ^ 2 * A p)
    (hkernel : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ k p ∧ k p ≤ K₀ * (p.2 - p.1))
    (hmod : ∀ s ∈ Icc u v, |A (u, s) - A (u, u)| ≤ η) :
    |attenuatedVolterraIntegral j k u v -
        A (u, u) * (v - u) ^ 3 / 3| ≤
      (η + J₀ * K₀ * (v - u) ^ 2 / 2) * (v - u) ^ 3 / 3 := by
  let d := v - u
  let g : ℝ → ℝ := fun s =>
    j (u, s) * Real.exp (-(∫ t in s..v, k (u, t)))
  let m : ℝ → ℝ := fun s => A (u, u) * (s - u) ^ 2
  have hseg : ∀ s ∈ Icc u v, (u, s) ∈ closedCoordTriangle a b := by
    intro s hs
    exact ⟨hu, hs.1, hs.2.trans hv⟩
  have harg : ContinuousOn (fun s : ℝ => ((u, s), v)) (Icc u v) := by fun_prop
  have hmap : MapsTo (fun s : ℝ => ((u, s), v))
      (Icc u v) (closedVolterraTriple a b) := by
    intro s hs
    exact ⟨hu, hs.1, hs.2, hv⟩
  have hqc : ContinuousOn (fun s => ∫ t in s..v, k (u, t)) (Icc u v) :=
    (continuousOn_verticalVolterraPrimitive hk).comp harg hmap
  have hgi : IntervalIntegrable g volume u v := by
    apply ContinuousOn.intervalIntegrable_of_Icc huv
    exact (hj.comp (continuous_const.prodMk continuous_id).continuousOn hseg).mul
      (Real.continuous_exp.comp_continuousOn hqc.neg)
  have hmi : IntervalIntegrable m volume u v :=
    (continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).intervalIntegrable _ _
  have hpoint (s : ℝ) (hs : s ∈ Icc u v) :
      |g s - m s| ≤
        (η + J₀ * K₀ * d ^ 2 / 2) * (s - u) ^ 2 := by
    let q := ∫ t in s..v, k (u, t)
    let e := Real.exp (-q)
    have hq := attenuation_integral_nonneg_le_half_sq hu hs.1 hs.2 hv hk hK₀ hkernel
    have he : |e - 1| ≤ K₀ * d ^ 2 / 2 :=
      (abs_exp_neg_sub_one_le hq.1).trans hq.2
    have hsrc := hsource (u, s) (hseg s hs)
    have hdiff : |j (u, s) - m s| ≤ η * (s - u) ^ 2 := by
      rw [hsrc.2.2]
      change |(s - u) ^ 2 * A (u, s) - A (u, u) * (s - u) ^ 2| ≤ _
      rw [mul_comm ((s - u) ^ 2) (A (u, s)), ← sub_mul, abs_mul]
      simpa only [abs_of_nonneg (sq_nonneg (s - u))] using
        mul_le_mul_of_nonneg_right (hmod s hs) (sq_nonneg (s - u))
    have hdecay : |j (u, s) * (e - 1)| ≤
        J₀ * K₀ * d ^ 2 / 2 * (s - u) ^ 2 := by
      rw [abs_mul, abs_of_nonneg hsrc.1]
      have h := mul_le_mul hsrc.2.1 he (abs_nonneg _) (by positivity)
      nlinarith only [h]
    calc
      |g s - m s| = |(j (u, s) - m s) + j (u, s) * (e - 1)| := by
        congr 1
        dsimp [g]
        ring
      _ ≤ |j (u, s) - m s| + |j (u, s) * (e - 1)| := abs_add_le _ _
      _ ≤ _ := by nlinarith only [hdiff, hdecay]
  have hint := abs_integral_le_third_cube_of_abs_le_quadratic huv
    (hgi.sub hmi) hpoint
  have heq : attenuatedVolterraIntegral j k u v -
      A (u, u) * d ^ 3 / 3 = ∫ s in u..v, g s - m s := by
    rw [intervalIntegral.integral_sub hgi hmi]
    rw [intervalIntegral.integral_const_mul, integral_sq_sub_left]
    simp only [attenuatedVolterraIntegral, g, d]
    ring
  rw [heq]
  simpa only [d] using hint

/-- The cubic axis expansion has one error modulus for the whole diagonal,
including both vertices of the closed triangle. -/
theorem attenuatedVolterraIntegral_uniform_axis_value
    {a b J₀ K₀ : ℝ} {j k A : ℝ × ℝ → ℝ}
    (hj : ContinuousOn j (closedCoordTriangle a b))
    (hk : ContinuousOn k (closedCoordTriangle a b))
    (hA : ContinuousOn A (closedCoordTriangle a b))
    (hJ₀ : 0 ≤ J₀) (hK₀ : 0 ≤ K₀)
    (hsource : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ j p ∧ j p ≤ J₀ * (p.2 - p.1) ^ 2 ∧
        j p = (p.2 - p.1) ^ 2 * A p)
    (hkernel : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ k p ∧ k p ≤ K₀ * (p.2 - p.1)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b → v - u < δ →
        |attenuatedVolterraIntegral j k u v -
          A (u, u) * (v - u) ^ 3 / 3| ≤ ε * (v - u) ^ 3 := by
  intro ε hε
  obtain ⟨δA, hδA, hmod⟩ := uniform_diagonal_continuity hA ε hε
  let C := J₀ * K₀
  have hC : 0 ≤ C := mul_nonneg hJ₀ hK₀
  let δ := min δA (min 1 (ε / (1 + C)))
  have hfrac : 0 < ε / (1 + C) := div_pos hε (by linarith)
  have hδ : 0 < δ := lt_min hδA (lt_min (by norm_num) hfrac)
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
  have hmod' : ∀ s ∈ Icc u v, |A (u, s) - A (u, u)| ≤ ε := by
    intro s hs
    exact (hmod u s hu hs.1 (hs.2.trans hv)
      (lt_of_le_of_lt (sub_le_sub_right hs.2 u)
        (lt_of_lt_of_le hgap (min_le_left _ _)))).le
  have hlocal := abs_attenuatedVolterraIntegral_sub_axis_le hu huv hv
    hj hk hJ₀ hK₀ hε.le hsource hkernel hmod'
  have hcoef : (ε + J₀ * K₀ * (v - u) ^ 2 / 2) / 3 ≤ ε := by
    dsimp [C] at hCd
    linarith
  have := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hd0 3)
  nlinarith only [hlocal, this]

end intervalIntegral

end
