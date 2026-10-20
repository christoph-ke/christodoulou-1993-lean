module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.AttenuatedVolterraAxisVertical
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Quadratic horizontal axis estimate for attenuated Volterra integrals
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

private theorem integral_sub_left_axis (u v : ℝ) :
    (∫ s in u..v, s - u) = (v - u) ^ 2 / 2 := by
  rw [intervalIntegral.integral_sub]
  · simp [integral_id]
    ring
  · exact continuous_id.intervalIntegrable _ _
  · exact continuous_const.intervalIntegrable _ _

/-- A local modulus for the horizontal source-jet amplitude gives its
quadratic axis coefficient. All attenuation errors are fourth order. -/
theorem abs_fderivWithin_attenuatedVolterraIntegral_horizontal_sub_axis_le
    {a b u v J₀ J₁ K₀ K₁ η : ℝ} {j k B : ℝ × ℝ → ℝ}
    (hab : a < b) (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b)
    (hj : ContDiffOn ℝ 1 j (closedCoordTriangle a b))
    (hk : ContDiffOn ℝ 1 k (closedCoordTriangle a b))
    (hjdiag : ∀ x ∈ Icc a b, j (x, x) = 0)
    (hJ₀ : 0 ≤ J₀) (hJ₁ : 0 ≤ J₁)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hη : 0 ≤ η)
    (hsource : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ j p ∧ j p ≤ J₀ * (p.2 - p.1) ^ 2)
    (hkernel : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ k p ∧ k p ≤ K₀ * (p.2 - p.1))
    (hjet : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ j (closedCoordTriangle a b) p) (1, 0)| ≤
        J₁ * (p.2 - p.1) ∧
      (fderivWithin ℝ j (closedCoordTriangle a b) p) (1, 0) =
        (p.2 - p.1) * B p)
    (hkjet : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ k (closedCoordTriangle a b) p) (1, 0)| ≤ K₁)
    (hmod : ∀ s ∈ Icc u v, |B (u, s) - B (u, u)| ≤ η) :
    |(fderivWithin ℝ (fun p : ℝ × ℝ =>
        attenuatedVolterraIntegral j k p.1 p.2)
        (closedCoordTriangle a b) (u, v)) (1, 0) -
      B (u, u) * (v - u) ^ 2 / 2| ≤
      (η + (J₁ * K₀ / 2 + J₀ * K₁) * (v - u) ^ 2) *
        (v - u) ^ 2 / 2 := by
  let K := closedCoordTriangle a b
  let d := v - u
  let ju : ℝ → ℝ := fun s => (fderivWithin ℝ j K (u, s)) (1, 0)
  let qu : ℝ → ℝ := fun s =>
    ∫ t in s..v, (fderivWithin ℝ k K (u, t)) (1, 0)
  let q : ℝ → ℝ := fun s => ∫ t in s..v, k (u, t)
  let e : ℝ → ℝ := fun s => Real.exp (-q s)
  let g : ℝ → ℝ := fun s => e s * (ju s - j (u, s) * qu s)
  let m : ℝ → ℝ := fun s => B (u, u) * (s - u)
  have hd : 0 ≤ d := sub_nonneg.mpr huv
  have hseg : ∀ s ∈ Icc u v, (u, s) ∈ K := by
    intro s hs
    exact ⟨hu, hs.1, hs.2.trans hv⟩
  have hgi : IntervalIntegrable g volume u v :=
    horizontal_integrand_intervalIntegrable hab hu huv hv hj hk
  have hmi : IntervalIntegrable m volume u v :=
    (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have hpoint (s : ℝ) (hs : s ∈ Icc u v) :
      |g s - m s| ≤
        (η + (J₁ * K₀ / 2 + J₀ * K₁) * d ^ 2) * (s - u) := by
    have hgap : 0 ≤ s - u ∧ s - u ≤ d :=
      ⟨sub_nonneg.mpr hs.1, by dsimp [d]; linarith only [hs.2]⟩
    have hremain : 0 ≤ v - s ∧ v - s ≤ d :=
      ⟨sub_nonneg.mpr hs.2, by dsimp [d]; linarith only [hs.1]⟩
    have hprod : (s - u) ^ 2 * (v - s) ≤ (s - u) * d ^ 2 := by
      have h := mul_le_mul hgap.2 hremain.2 hremain.1 hd
      have h' := mul_le_mul_of_nonneg_left h hgap.1
      nlinarith only [h']
    have hq := attenuation_integral_nonneg_le_half_sq hu hs.1 hs.2 hv
      hk.continuousOn hK₀ hkernel
    have he : |e s - 1| ≤ K₀ * d ^ 2 / 2 :=
      (abs_exp_neg_sub_one_le hq.1).trans hq.2
    have hepos : 0 ≤ e s := (Real.exp_pos _).le
    have hele : e s ≤ 1 := (Real.exp_le_one_iff).2 (neg_nonpos.mpr hq.1)
    have hsrc := hsource (u, s) (hseg s hs)
    have hju := hjet (u, s) (hseg s hs)
    have hqu : |qu s| ≤ K₁ * (v - s) :=
      abs_integral_horizontal_jet_le hu hs.1 hs.2 hv hkjet
    have hfirst : |ju s - m s| ≤ η * (s - u) := by
      have hjuEq : ju s = (s - u) * B (u, s) := hju.2
      rw [hjuEq]
      change |(s - u) * B (u, s) - B (u, u) * (s - u)| ≤ _
      rw [mul_comm (s - u) (B (u, s)), ← sub_mul, abs_mul]
      simpa only [abs_of_nonneg hgap.1] using
        mul_le_mul_of_nonneg_right (hmod s hs) hgap.1
    have hsecond : |ju s * (e s - 1)| ≤
        (J₁ * K₀ / 2) * d ^ 2 * (s - u) := by
      rw [abs_mul]
      have h := mul_le_mul hju.1 he (abs_nonneg _) (mul_nonneg hJ₁ hgap.1)
      nlinarith only [h]
    have hthird : |e s * (j (u, s) * qu s)| ≤
        J₀ * K₁ * d ^ 2 * (s - u) := by
      rw [abs_mul, abs_of_nonneg hepos, abs_mul, abs_of_nonneg hsrc.1]
      have hbound : j (u, s) * |qu s| ≤
          J₀ * K₁ * d ^ 2 * (s - u) := by
        calc
          _ ≤ (J₀ * (s - u) ^ 2) * |qu s| :=
            mul_le_mul_of_nonneg_right hsrc.2 (abs_nonneg _)
          _ ≤ (J₀ * (s - u) ^ 2) * (K₁ * (v - s)) :=
            mul_le_mul_of_nonneg_left hqu (mul_nonneg hJ₀ (sq_nonneg _))
          _ = (J₀ * K₁) * ((s - u) ^ 2 * (v - s)) := by ring
          _ ≤ (J₀ * K₁) * ((s - u) * d ^ 2) :=
            mul_le_mul_of_nonneg_left hprod (mul_nonneg hJ₀ hK₁)
          _ = _ := by ring
      exact (mul_le_of_le_one_left (mul_nonneg hsrc.1 (abs_nonneg _)) hele).trans hbound
    have htri : |g s - m s| ≤
        |ju s - m s| + |ju s * (e s - 1)| +
          |e s * (j (u, s) * qu s)| := by
      have h1 := abs_add_le ((ju s - m s) + ju s * (e s - 1))
        (-(e s * (j (u, s) * qu s)))
      have h2 := abs_add_le (ju s - m s) (ju s * (e s - 1))
      simp only [abs_neg, ← sub_eq_add_neg] at h1
      calc
        _ = |(ju s - m s) + ju s * (e s - 1) -
            e s * (j (u, s) * qu s)| := by
              congr 1
              dsimp [g]
              ring
        _ ≤ _ := by linarith only [h1, h2]
    nlinarith only [htri, hfirst, hsecond, hthird]
  have hint := abs_integral_le_half_sq_of_abs_le_linear huv
    (by positivity : 0 ≤ η + (J₁ * K₀ / 2 + J₀ * K₁) * d ^ 2)
    (hgi.sub hmi) hpoint
  have heq :
      (fderivWithin ℝ (fun p : ℝ × ℝ =>
        attenuatedVolterraIntegral j k p.1 p.2) K (u, v)) (1, 0) -
        B (u, u) * d ^ 2 / 2 = ∫ s in u..v, g s - m s := by
    rw [fderivWithin_attenuatedVolterraIntegral_horizontal hab hj hk hjdiag
      (show (u, v) ∈ K from ⟨hu, huv, hv⟩)]
    rw [intervalIntegral.integral_sub hgi hmi,
      intervalIntegral.integral_const_mul, integral_sub_left_axis]
    simp only [d]
    ring
  rw [heq]
  simpa only [d] using hint

/-- The horizontal quadratic expansion has one error modulus for the whole
compact diagonal, including its vertices. -/
theorem attenuatedVolterraIntegral_uniform_axis_horizontal
    {a b J₀ J₁ K₀ K₁ : ℝ} {j k B : ℝ × ℝ → ℝ}
    (hab : a < b)
    (hj : ContDiffOn ℝ 1 j (closedCoordTriangle a b))
    (hk : ContDiffOn ℝ 1 k (closedCoordTriangle a b))
    (hB : ContinuousOn B (closedCoordTriangle a b))
    (hjdiag : ∀ x ∈ Icc a b, j (x, x) = 0)
    (hJ₀ : 0 ≤ J₀) (hJ₁ : 0 ≤ J₁)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁)
    (hsource : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ j p ∧ j p ≤ J₀ * (p.2 - p.1) ^ 2)
    (hkernel : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ k p ∧ k p ≤ K₀ * (p.2 - p.1))
    (hjet : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ j (closedCoordTriangle a b) p) (1, 0)| ≤
        J₁ * (p.2 - p.1) ∧
      (fderivWithin ℝ j (closedCoordTriangle a b) p) (1, 0) =
        (p.2 - p.1) * B p)
    (hkjet : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ k (closedCoordTriangle a b) p) (1, 0)| ≤ K₁) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b → v - u < δ →
        |(fderivWithin ℝ (fun p : ℝ × ℝ =>
            attenuatedVolterraIntegral j k p.1 p.2)
            (closedCoordTriangle a b) (u, v)) (1, 0) -
          B (u, u) * (v - u) ^ 2 / 2| ≤ ε * (v - u) ^ 2 := by
  intro ε hε
  obtain ⟨δB, hδB, hmod⟩ := uniform_diagonal_continuity hB ε hε
  let C := J₁ * K₀ / 2 + J₀ * K₁
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let δ := min δB (min 1 (ε / (1 + C)))
  have hδ : 0 < δ := lt_min hδB
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
  have hmod' : ∀ s ∈ Icc u v, |B (u, s) - B (u, u)| ≤ ε := by
    intro s hs
    exact (hmod u s hu hs.1 (hs.2.trans hv)
      (lt_of_le_of_lt (sub_le_sub_right hs.2 u)
        (lt_of_lt_of_le hgap (min_le_left _ _)))).le
  have hlocal := abs_fderivWithin_attenuatedVolterraIntegral_horizontal_sub_axis_le
    hab hu huv hv hj hk hjdiag hJ₀ hJ₁ hK₀ hK₁ hε.le
    hsource hkernel hjet hkjet hmod'
  have hcoef : (ε + (J₁ * K₀ / 2 + J₀ * K₁) * (v - u) ^ 2) / 2 ≤ ε := by
    dsimp [C] at hCd
    linarith
  have := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (v - u))
  nlinarith only [hlocal, this]

end intervalIntegral

end
