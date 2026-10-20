module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.AttenuatedVolterraHorizontal
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Quantitative first-jet bounds for attenuated Volterra integrals

These estimates integrate quadratic source and linear source-jet bounds with
the exact half-square and third-cube coefficients.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- A nonnegative quadratic source and nonnegative linear attenuation give
the vertical first-jet bound with the coefficient from the Volterra ODE. -/
theorem abs_fderivWithin_attenuatedVolterraIntegral_vertical_le
    {a b u v J₀ K₀ : ℝ} {j k : ℝ × ℝ → ℝ}
    (hab : a < b) (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b)
    (hsize : b - a ≤ 1)
    (hj : ContDiffOn ℝ 1 j (closedCoordTriangle a b))
    (hk : ContDiffOn ℝ 1 k (closedCoordTriangle a b))
    (hJ₀ : 0 ≤ J₀) (hK₀ : 0 ≤ K₀)
    (hsource : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ j p ∧ j p ≤ J₀ * (p.2 - p.1) ^ 2)
    (hkernel : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ k p ∧ k p ≤ K₀ * (p.2 - p.1)) :
    |(fderivWithin ℝ (fun p : ℝ × ℝ =>
        attenuatedVolterraIntegral j k p.1 p.2)
        (closedCoordTriangle a b) (u, v)) (0, 1)| ≤
      (J₀ + K₀ * (J₀ / 3)) * (v - u) ^ 2 := by
  let K := closedCoordTriangle a b
  let d := v - u
  have hp : (u, v) ∈ K := ⟨hu, huv, hv⟩
  have hd : 0 ≤ d ∧ d ≤ 1 := ⟨sub_nonneg.mpr huv, by dsimp [d]; linarith⟩
  have hd2 : d ^ 2 ≤ 1 := by nlinarith only [hd.1, hd.2]
  have hd4 : d ^ 4 ≤ d ^ 2 := by
    calc
      d ^ 4 = d ^ 2 * d ^ 2 := by ring
      _ ≤ d ^ 2 * 1 := mul_le_mul_of_nonneg_left hd2 (sq_nonneg d)
      _ = d ^ 2 := by ring
  have hJ := attenuatedVolterraIntegral_nonneg_le hu huv hv hj.continuousOn
    hk.continuousOn (fun p hp => (hkernel p hp).1) hsource
  have hjbound : 0 ≤ j (u, v) ∧ j (u, v) ≤ J₀ * d ^ 2 := hsource (u, v) hp
  have hkbound : 0 ≤ k (u, v) ∧ k (u, v) ≤ K₀ * d := hkernel (u, v) hp
  rw [fderivWithin_attenuatedVolterraIntegral_vertical hab hj hk hp]
  have hmul : k (u, v) * attenuatedVolterraIntegral j k u v ≤
      K₀ * (J₀ / 3) * d ^ 2 := by
    calc
      _ ≤ (K₀ * d) * attenuatedVolterraIntegral j k u v :=
        mul_le_mul_of_nonneg_right hkbound.2 hJ.1
      _ ≤ (K₀ * d) * (J₀ * d ^ 3 / 3) :=
        mul_le_mul_of_nonneg_left hJ.2 (mul_nonneg hK₀ hd.1)
      _ = K₀ * (J₀ / 3) * d ^ 4 := by ring
      _ ≤ K₀ * (J₀ / 3) * d ^ 2 :=
        mul_le_mul_of_nonneg_left hd4 (mul_nonneg hK₀ (div_nonneg hJ₀ (by norm_num)))
  change |j (u, v) - k (u, v) * attenuatedVolterraIntegral j k u v| ≤
    (J₀ + K₀ * (J₀ / 3)) * d ^ 2
  have hJpart : 0 ≤ J₀ * d ^ 2 := mul_nonneg hJ₀ (sq_nonneg d)
  have hKpart : 0 ≤ k (u, v) * attenuatedVolterraIntegral j k u v :=
    mul_nonneg hkbound.1 hJ.1
  have hKcoeff : 0 ≤ K₀ * (J₀ / 3) * d ^ 2 := by positivity
  exact abs_le.mpr ⟨by
    nlinarith only [hjbound.1, hmul, hJpart], by
    nlinarith only [hjbound.2, hKpart, hKcoeff]⟩

/-- The horizontal first jet has the sharp half-square bound from the
linear source-jet majorant. -/
theorem abs_fderivWithin_attenuatedVolterraIntegral_horizontal_le
    {a b u v J₀ J₁ K₁ : ℝ} {j k : ℝ × ℝ → ℝ}
    (hab : a < b) (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b)
    (hsize : b - a ≤ 1)
    (hj : ContDiffOn ℝ 1 j (closedCoordTriangle a b))
    (hk : ContDiffOn ℝ 1 k (closedCoordTriangle a b))
    (hjdiag : ∀ x ∈ Icc a b, j (x, x) = 0)
    (hJ₀ : 0 ≤ J₀) (hJ₁ : 0 ≤ J₁) (hK₁ : 0 ≤ K₁)
    (hsource : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ j p ∧ j p ≤ J₀ * (p.2 - p.1) ^ 2)
    (hkpos : ∀ p ∈ closedCoordTriangle a b, 0 ≤ k p)
    (hju : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ j (closedCoordTriangle a b) p) (1, 0)| ≤
        J₁ * (p.2 - p.1))
    (hku : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ k (closedCoordTriangle a b) p) (1, 0)| ≤ K₁) :
    |(fderivWithin ℝ (fun p : ℝ × ℝ =>
        attenuatedVolterraIntegral j k p.1 p.2)
        (closedCoordTriangle a b) (u, v)) (1, 0)| ≤
      (J₁ + J₀ * K₁) * (v - u) ^ 2 / 2 := by
  let K := closedCoordTriangle a b
  let ju : ℝ × ℝ → ℝ := fun p => (fderivWithin ℝ j K p) (1, 0)
  let ku : ℝ × ℝ → ℝ := fun p => (fderivWithin ℝ k K p) (1, 0)
  let q : ℝ → ℝ := fun s => ∫ t in s..v, k (u, t)
  let qu : ℝ → ℝ := fun s => ∫ t in s..v, ku (u, t)
  let g : ℝ → ℝ := fun s => Real.exp (-q s) * (ju (u, s) - j (u, s) * qu s)
  have hseg : ∀ s ∈ Icc u v, (u, s) ∈ K := by
    intro s hs
    exact ⟨hu, hs.1, hs.2.trans hv⟩
  have harg : ContinuousOn (fun s : ℝ => ((u, s), v)) (Icc u v) := by fun_prop
  have hmap : MapsTo (fun s : ℝ => ((u, s), v))
      (Icc u v) (closedVolterraTriple a b) := by
    intro s hs
    exact ⟨hu, hs.1, hs.2, hv⟩
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hjuc : ContinuousOn ju K :=
    (hj.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hkuc : ContinuousOn ku K :=
    (hk.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hqc : ContinuousOn q (Icc u v) :=
    (continuousOn_verticalVolterraPrimitive hk.continuousOn).comp harg hmap
  have hquc : ContinuousOn qu (Icc u v) :=
    (continuousOn_verticalVolterraPrimitive hkuc).comp harg hmap
  have hgc : ContinuousOn g (Icc u v) := by
    exact (Real.continuous_exp.comp_continuousOn hqc.neg).mul
      ((hjuc.comp (continuous_const.prodMk continuous_id).continuousOn hseg).sub
        ((hj.continuousOn.comp
          (continuous_const.prodMk continuous_id).continuousOn hseg).mul hquc))
  have hgi : IntervalIntegrable g volume u v := hgc.intervalIntegrable_of_Icc huv
  have hB : 0 ≤ J₁ + J₀ * K₁ := add_nonneg hJ₁ (mul_nonneg hJ₀ hK₁)
  have hpoint (s : ℝ) (hs : s ∈ Icc u v) :
      |g s| ≤ (J₁ + J₀ * K₁) * (s - u) := by
    have hs₁ : 0 ≤ s - u ∧ s - u ≤ 1 :=
      ⟨sub_nonneg.mpr hs.1, by linarith only [hs.1, hs.2, hu, hv, hsize]⟩
    have hs₂ : 0 ≤ v - s ∧ v - s ≤ 1 :=
      ⟨sub_nonneg.mpr hs.2, by linarith only [hs.1, hs.2, hu, hv, hsize]⟩
    have hprod : (s - u) * (v - s) ≤ 1 := by
      calc
        _ ≤ 1 * (v - s) := mul_le_mul_of_nonneg_right hs₁.2 hs₂.1
        _ ≤ 1 := by simpa only [one_mul] using hs₂.2
    have hsqprod : (s - u) ^ 2 * (v - s) ≤ s - u := by
      calc
        _ = (s - u) * ((s - u) * (v - s)) := by ring
        _ ≤ (s - u) * 1 := mul_le_mul_of_nonneg_left hprod hs₁.1
        _ = s - u := by ring
    have hquabs : |qu s| ≤ K₁ * (v - s) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := s) (b := v) (C := K₁) (f := fun t => ku (u, t)) (by
          intro t ht
          have ht' : t ∈ Icc s v := by
            rw [uIoc_of_le hs.2] at ht
            exact ⟨ht.1.le, ht.2⟩
          simpa only [Real.norm_eq_abs] using
            hku (u, t) ⟨hu, hs.1.trans ht'.1, ht'.2.trans hv⟩)
      simpa only [qu, Real.norm_eq_abs, abs_of_nonneg hs₂.1] using h
    have hjval := hsource (u, s) (hseg s hs)
    have hjuval := hju (u, s) (hseg s hs)
    have hqpos : 0 ≤ q s :=
      intervalIntegral.integral_nonneg hs.2 (fun t ht =>
        hkpos (u, t) ⟨hu, hs.1.trans ht.1, ht.2.trans hv⟩)
    have hepos : 0 ≤ Real.exp (-q s) := (Real.exp_pos _).le
    have hele : Real.exp (-q s) ≤ 1 :=
      (Real.exp_le_one_iff).2 (neg_nonpos.mpr hqpos)
    have hterm : j (u, s) * |qu s| ≤ J₀ * K₁ * (s - u) := by
      calc
        _ ≤ (J₀ * (s - u) ^ 2) * |qu s| :=
          mul_le_mul_of_nonneg_right hjval.2 (abs_nonneg _)
        _ ≤ (J₀ * (s - u) ^ 2) * (K₁ * (v - s)) :=
          mul_le_mul_of_nonneg_left hquabs (mul_nonneg hJ₀ (sq_nonneg _))
        _ = (J₀ * K₁) * ((s - u) ^ 2 * (v - s)) := by ring
        _ ≤ (J₀ * K₁) * (s - u) :=
          mul_le_mul_of_nonneg_left hsqprod (mul_nonneg hJ₀ hK₁)
    have hbracket : |ju (u, s) - j (u, s) * qu s| ≤
        (J₁ + J₀ * K₁) * (s - u) := by
      have h := abs_add_le (ju (u, s)) (-(j (u, s) * qu s))
      simp only [abs_neg, ← sub_eq_add_neg] at h
      rw [abs_mul, abs_of_nonneg hjval.1] at h
      nlinarith only [h, hjuval, hterm]
    change |Real.exp (-q s) * (ju (u, s) - j (u, s) * qu s)| ≤ _
    rw [abs_mul, abs_of_nonneg hepos]
    exact (mul_le_of_le_one_left (abs_nonneg _) hele).trans hbracket
  have h := abs_integral_le_half_sq_of_abs_le_linear huv hB hgi hpoint
  rw [fderivWithin_attenuatedVolterraIntegral_horizontal hab hj hk hjdiag
    (show (u, v) ∈ K from ⟨hu, huv, hv⟩)]
  exact h

end intervalIntegral

end
