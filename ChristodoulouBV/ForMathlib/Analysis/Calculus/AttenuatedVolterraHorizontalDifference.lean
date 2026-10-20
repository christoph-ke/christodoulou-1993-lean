module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.AttenuatedVolterraDifference
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Two-input horizontal jet estimate for attenuated Volterra integrals

The moving-endpoint contribution is zero for diagonal-vanishing sources.
The remaining integrand is compared by separating its exponential and
source-jet bracket.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- The horizontal jet integrand is interval integrable on each admissible
coordinate ray of a closed triangle. -/
theorem horizontal_integrand_intervalIntegrable
    {a b u v : ℝ} (hab : a < b) {j k : ℝ × ℝ → ℝ}
    (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b)
    (hj : ContDiffOn ℝ 1 j (closedCoordTriangle a b))
    (hk : ContDiffOn ℝ 1 k (closedCoordTriangle a b)) :
    IntervalIntegrable (fun s =>
      Real.exp (-(∫ t in s..v, k (u, t))) *
        ((fderivWithin ℝ j (closedCoordTriangle a b) (u, s)) (1, 0) -
          j (u, s) *
            (∫ t in s..v,
              (fderivWithin ℝ k (closedCoordTriangle a b) (u, t)) (1, 0))))
      volume u v := by
  let K := closedCoordTriangle a b
  let ju : ℝ × ℝ → ℝ := fun p => (fderivWithin ℝ j K p) (1, 0)
  let ku : ℝ × ℝ → ℝ := fun p => (fderivWithin ℝ k K p) (1, 0)
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
  have hqc : ContinuousOn (fun s => ∫ t in s..v, k (u, t)) (Icc u v) :=
    (continuousOn_verticalVolterraPrimitive hk.continuousOn).comp harg hmap
  have hquc : ContinuousOn (fun s => ∫ t in s..v, ku (u, t)) (Icc u v) :=
    (continuousOn_verticalVolterraPrimitive hkuc).comp harg hmap
  apply ContinuousOn.intervalIntegrable_of_Icc huv
  exact (Real.continuous_exp.comp_continuousOn hqc.neg).mul
    ((hjuc.comp (continuous_const.prodMk continuous_id).continuousOn hseg).sub
      ((hj.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn hseg).mul hquc))

/-- A uniform bound on a horizontal attenuation-kernel jet gives the exact
length bound for its integral over an admissible upper interval. -/
theorem abs_integral_horizontal_jet_le
    {a b u s v A : ℝ} {k : ℝ × ℝ → ℝ}
    (hu : a ≤ u) (hus : u ≤ s) (hsv : s ≤ v) (hv : v ≤ b)
    (hbound : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ k (closedCoordTriangle a b) p) (1, 0)| ≤ A) :
    |∫ t in s..v,
      (fderivWithin ℝ k (closedCoordTriangle a b) (u, t)) (1, 0)| ≤
      A * (v - s) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := v) (C := A)
    (f := fun t => (fderivWithin ℝ k (closedCoordTriangle a b) (u, t)) (1, 0))
    (by
      intro t ht
      have ht' : t ∈ Icc s v := by
        rw [uIoc_of_le hsv] at ht
        exact ⟨ht.1.le, ht.2⟩
      simpa only [Real.norm_eq_abs] using
        hbound (u, t) ⟨hu, hus.trans ht'.1, ht'.2.trans hv⟩)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hsv)] using h

/-- The difference of horizontal attenuation-kernel jets integrates with
the same exact interval-length factor. -/
theorem abs_integral_horizontal_jet_sub_le
    {a b u s v A D : ℝ} {k₁ k₂ : ℝ × ℝ → ℝ}
    (hab : a < b) (hu : a ≤ u) (hus : u ≤ s) (hsv : s ≤ v) (hv : v ≤ b)
    (hk₁ : ContDiffOn ℝ 1 k₁ (closedCoordTriangle a b))
    (hk₂ : ContDiffOn ℝ 1 k₂ (closedCoordTriangle a b))
    (hbound : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ k₁ (closedCoordTriangle a b) p) (1, 0) -
        (fderivWithin ℝ k₂ (closedCoordTriangle a b) p) (1, 0)| ≤ A * D) :
    |(∫ t in s..v,
        (fderivWithin ℝ k₁ (closedCoordTriangle a b) (u, t)) (1, 0)) -
      (∫ t in s..v,
        (fderivWithin ℝ k₂ (closedCoordTriangle a b) (u, t)) (1, 0))| ≤
      A * (v - s) * D := by
  let K := closedCoordTriangle a b
  let f₁ : ℝ → ℝ := fun t => (fderivWithin ℝ k₁ K (u, t)) (1, 0)
  let f₂ : ℝ → ℝ := fun t => (fderivWithin ℝ k₂ K (u, t)) (1, 0)
  have hseg : ∀ t ∈ Icc s v, (u, t) ∈ K := by
    intro t ht
    exact ⟨hu, hus.trans ht.1, ht.2.trans hv⟩
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hi₁ : IntervalIntegrable f₁ volume s v := by
    apply ContinuousOn.intervalIntegrable_of_Icc hsv
    exact ((hk₁.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const).comp
        (continuous_const.prodMk continuous_id).continuousOn hseg
  have hi₂ : IntervalIntegrable f₂ volume s v := by
    apply ContinuousOn.intervalIntegrable_of_Icc hsv
    exact ((hk₂.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const).comp
        (continuous_const.prodMk continuous_id).continuousOn hseg
  rw [← intervalIntegral.integral_sub hi₁ hi₂]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := v) (C := A * D) (f := fun t => f₁ t - f₂ t) (by
      intro t ht
      have ht' : t ∈ Icc s v := by
        rw [uIoc_of_le hsv] at ht
        exact ⟨ht.1.le, ht.2⟩
      simpa only [Real.norm_eq_abs] using hbound (u, t) (hseg t ht'))
  change |∫ t in s..v, f₁ t - f₂ t| ≤ _
  have h' : |∫ t in s..v, f₁ t - f₂ t| ≤ (A * D) * (v - s) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hsv)] using h
  nlinarith only [h']

/-- The two-input horizontal first-jet estimate, with the exponential
difference and bracket difference coefficients separated exactly as in the
Volterra calculation. -/
theorem abs_fderivWithin_attenuatedVolterraIntegral_horizontal_sub_le
    {a b u v J₀ J₁ K₁ JΔ₀ JΔ₁ KΔ₀ KΔ₁ D : ℝ}
    {j₁ j₂ k₁ k₂ : ℝ × ℝ → ℝ}
    (hab : a < b) (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b)
    (hsize : b - a ≤ 1)
    (hj₁ : ContDiffOn ℝ 1 j₁ (closedCoordTriangle a b))
    (hj₂ : ContDiffOn ℝ 1 j₂ (closedCoordTriangle a b))
    (hk₁ : ContDiffOn ℝ 1 k₁ (closedCoordTriangle a b))
    (hk₂ : ContDiffOn ℝ 1 k₂ (closedCoordTriangle a b))
    (hjdiag₁ : ∀ x ∈ Icc a b, j₁ (x, x) = 0)
    (hjdiag₂ : ∀ x ∈ Icc a b, j₂ (x, x) = 0)
    (hJ₀ : 0 ≤ J₀) (hJ₁ : 0 ≤ J₁) (hK₁ : 0 ≤ K₁)
    (hJΔ₀ : 0 ≤ JΔ₀) (hJΔ₁ : 0 ≤ JΔ₁)
    (hKΔ₀ : 0 ≤ KΔ₀) (hKΔ₁ : 0 ≤ KΔ₁) (hD : 0 ≤ D)
    (hsource₁ : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ j₁ p ∧ j₁ p ≤ J₀ * (p.2 - p.1) ^ 2)
    (hsource₂ : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ j₂ p ∧ j₂ p ≤ J₀ * (p.2 - p.1) ^ 2)
    (hkpos₁ : ∀ p ∈ closedCoordTriangle a b, 0 ≤ k₁ p)
    (hkpos₂ : ∀ p ∈ closedCoordTriangle a b, 0 ≤ k₂ p)
    (hju₁ : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ j₁ (closedCoordTriangle a b) p) (1, 0)| ≤
        J₁ * (p.2 - p.1))
    (hku₁ : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ k₁ (closedCoordTriangle a b) p) (1, 0)| ≤ K₁)
    (hjdifference : ∀ p ∈ closedCoordTriangle a b,
      |j₁ p - j₂ p| ≤ JΔ₀ * (p.2 - p.1) ^ 2 * D)
    (hkDifference : ∀ p ∈ closedCoordTriangle a b,
      |k₁ p - k₂ p| ≤ KΔ₀ * (p.2 - p.1) * D)
    (hjuDifference : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ j₁ (closedCoordTriangle a b) p) (1, 0) -
        (fderivWithin ℝ j₂ (closedCoordTriangle a b) p) (1, 0)| ≤
        JΔ₁ * (p.2 - p.1) * D)
    (hkuDifference : ∀ p ∈ closedCoordTriangle a b,
      |(fderivWithin ℝ k₁ (closedCoordTriangle a b) p) (1, 0) -
        (fderivWithin ℝ k₂ (closedCoordTriangle a b) p) (1, 0)| ≤ KΔ₁ * D) :
    |(fderivWithin ℝ (fun p : ℝ × ℝ =>
          attenuatedVolterraIntegral j₁ k₁ p.1 p.2)
          (closedCoordTriangle a b) (u, v)) (1, 0) -
      (fderivWithin ℝ (fun p : ℝ × ℝ =>
          attenuatedVolterraIntegral j₂ k₂ p.1 p.2)
          (closedCoordTriangle a b) (u, v)) (1, 0)| ≤
      (KΔ₀ * (J₁ + J₀ * K₁) / 4 +
        (JΔ₁ + JΔ₀ * K₁ + J₀ * KΔ₁) / 2) *
        (v - u) ^ 2 * D := by
  let K := closedCoordTriangle a b
  let d := v - u
  let e₁ : ℝ → ℝ := fun s => Real.exp (-(∫ t in s..v, k₁ (u, t)))
  let e₂ : ℝ → ℝ := fun s => Real.exp (-(∫ t in s..v, k₂ (u, t)))
  let q₁u : ℝ → ℝ := fun s =>
    ∫ t in s..v, (fderivWithin ℝ k₁ K (u, t)) (1, 0)
  let q₂u : ℝ → ℝ := fun s =>
    ∫ t in s..v, (fderivWithin ℝ k₂ K (u, t)) (1, 0)
  let A₁ : ℝ → ℝ := fun s =>
    (fderivWithin ℝ j₁ K (u, s)) (1, 0) - j₁ (u, s) * q₁u s
  let A₂ : ℝ → ℝ := fun s =>
    (fderivWithin ℝ j₂ K (u, s)) (1, 0) - j₂ (u, s) * q₂u s
  let B := J₁ + J₀ * K₁
  let C := JΔ₁ + JΔ₀ * K₁ + J₀ * KΔ₁
  have hseg : ∀ s ∈ Icc u v, (u, s) ∈ K := by
    intro s hs
    exact ⟨hu, hs.1, hs.2.trans hv⟩
  have hd : 0 ≤ d ∧ d ≤ 1 := ⟨sub_nonneg.mpr huv, by dsimp [d]; linarith⟩
  have hd2 : d ^ 2 ≤ 1 := by nlinarith only [hd.1, hd.2]
  have hB : 0 ≤ B := add_nonneg hJ₁ (mul_nonneg hJ₀ hK₁)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (s : ℝ) (hs : s ∈ Icc u v) :
      |e₁ s * A₁ s - e₂ s * A₂ s| ≤
        (KΔ₀ * B / 2 + C) * (s - u) * D := by
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
    have hq₁ : 0 ≤ ∫ t in s..v, k₁ (u, t) :=
      intervalIntegral.integral_nonneg hs.2 (fun t ht =>
        hkpos₁ (u, t) ⟨hu, hs.1.trans ht.1, ht.2.trans hv⟩)
    have hq₂ : 0 ≤ ∫ t in s..v, k₂ (u, t) :=
      intervalIntegral.integral_nonneg hs.2 (fun t ht =>
        hkpos₂ (u, t) ⟨hu, hs.1.trans ht.1, ht.2.trans hv⟩)
    have he₁pos : 0 ≤ e₁ s := (Real.exp_pos _).le
    have he₂pos : 0 ≤ e₂ s := (Real.exp_pos _).le
    have he₂le : e₂ s ≤ 1 := (Real.exp_le_one_iff).2 (neg_nonpos.mpr hq₂)
    have hediff : |e₁ s - e₂ s| ≤ KΔ₀ * d ^ 2 * D / 2 :=
      (abs_exp_neg_sub_exp_neg_le hq₁ hq₂).trans
        (abs_attenuationPrimitive_sub_le hu hs.1 hs.2 hv
          hk₁.continuousOn hk₂.continuousOn hKΔ₀ hD hkDifference)
    have hqu₁ : |q₁u s| ≤ K₁ * (v - s) :=
      abs_integral_horizontal_jet_le hu hs.1 hs.2 hv hku₁
    have hqudiff : |q₁u s - q₂u s| ≤ KΔ₁ * (v - s) * D :=
      abs_integral_horizontal_jet_sub_le hab hu hs.1 hs.2 hv
        hk₁ hk₂ hkuDifference
    have hj₁val := hsource₁ (u, s) (hseg s hs)
    have hj₂val := hsource₂ (u, s) (hseg s hs)
    have hju₁val := hju₁ (u, s) (hseg s hs)
    have hjdiff := hjdifference (u, s) (hseg s hs)
    have hjudiff := hjuDifference (u, s) (hseg s hs)
    have hterm₁ : j₁ (u, s) * |q₁u s| ≤ J₀ * K₁ * (s - u) := by
      calc
        _ ≤ (J₀ * (s - u) ^ 2) * |q₁u s| :=
          mul_le_mul_of_nonneg_right hj₁val.2 (abs_nonneg _)
        _ ≤ (J₀ * (s - u) ^ 2) * (K₁ * (v - s)) :=
          mul_le_mul_of_nonneg_left hqu₁ (mul_nonneg hJ₀ (sq_nonneg _))
        _ = (J₀ * K₁) * ((s - u) ^ 2 * (v - s)) := by ring
        _ ≤ (J₀ * K₁) * (s - u) :=
          mul_le_mul_of_nonneg_left hsqprod (mul_nonneg hJ₀ hK₁)
    have hA₁ : |A₁ s| ≤ B * (s - u) := by
      have h := abs_add_le ((fderivWithin ℝ j₁ K (u, s)) (1, 0))
        (-(j₁ (u, s) * q₁u s))
      simp only [abs_neg, ← sub_eq_add_neg] at h
      rw [abs_mul, abs_of_nonneg hj₁val.1] at h
      dsimp [A₁, B]
      nlinarith only [h, hju₁val, hterm₁]
    have htermΔ₁ : |(j₁ (u, s) - j₂ (u, s)) * q₁u s| ≤
        JΔ₀ * K₁ * (s - u) * D := by
      rw [abs_mul]
      calc
        _ ≤ (JΔ₀ * (s - u) ^ 2 * D) * |q₁u s| :=
          mul_le_mul_of_nonneg_right hjdiff (abs_nonneg _)
        _ ≤ (JΔ₀ * (s - u) ^ 2 * D) * (K₁ * (v - s)) :=
          mul_le_mul_of_nonneg_left hqu₁ (by positivity)
        _ = (JΔ₀ * K₁ * D) * ((s - u) ^ 2 * (v - s)) := by ring
        _ ≤ (JΔ₀ * K₁ * D) * (s - u) :=
          mul_le_mul_of_nonneg_left hsqprod (by positivity)
        _ = _ := by ring
    have htermΔ₂ : |j₂ (u, s) * (q₁u s - q₂u s)| ≤
        J₀ * KΔ₁ * (s - u) * D := by
      rw [abs_mul, abs_of_nonneg hj₂val.1]
      calc
        _ ≤ (J₀ * (s - u) ^ 2) * |q₁u s - q₂u s| :=
          mul_le_mul_of_nonneg_right hj₂val.2 (abs_nonneg _)
        _ ≤ (J₀ * (s - u) ^ 2) * (KΔ₁ * (v - s) * D) :=
          mul_le_mul_of_nonneg_left hqudiff (by positivity)
        _ = (J₀ * KΔ₁ * D) * ((s - u) ^ 2 * (v - s)) := by ring
        _ ≤ (J₀ * KΔ₁ * D) * (s - u) :=
          mul_le_mul_of_nonneg_left hsqprod (by positivity)
        _ = _ := by ring
    have hAdiff : |A₁ s - A₂ s| ≤ C * (s - u) * D := by
      have hsplit : A₁ s - A₂ s =
          ((fderivWithin ℝ j₁ K (u, s)) (1, 0) -
            (fderivWithin ℝ j₂ K (u, s)) (1, 0)) -
            ((j₁ (u, s) - j₂ (u, s)) * q₁u s +
              j₂ (u, s) * (q₁u s - q₂u s)) := by
        dsimp [A₁, A₂]
        ring
      rw [hsplit]
      have h := abs_add_le
        ((fderivWithin ℝ j₁ K (u, s)) (1, 0) -
          (fderivWithin ℝ j₂ K (u, s)) (1, 0))
        (-((j₁ (u, s) - j₂ (u, s)) * q₁u s +
          j₂ (u, s) * (q₁u s - q₂u s)))
      simp only [abs_neg, ← sub_eq_add_neg] at h
      have h' := abs_add_le
        ((j₁ (u, s) - j₂ (u, s)) * q₁u s)
        (j₂ (u, s) * (q₁u s - q₂u s))
      dsimp [C]
      nlinarith only [h, h', hjudiff, htermΔ₁, htermΔ₂]
    have hfirst : |(e₁ s - e₂ s) * A₁ s| ≤
        (KΔ₀ * B / 2) * (s - u) * D := by
      rw [abs_mul]
      calc
        _ ≤ (KΔ₀ * d ^ 2 * D / 2) * |A₁ s| :=
          mul_le_mul_of_nonneg_right hediff (abs_nonneg _)
        _ ≤ (KΔ₀ * d ^ 2 * D / 2) * (B * (s - u)) :=
          mul_le_mul_of_nonneg_left hA₁ (by positivity)
        _ = ((KΔ₀ * B / 2) * (s - u) * D) * d ^ 2 := by ring
        _ ≤ ((KΔ₀ * B / 2) * (s - u) * D) * 1 :=
          mul_le_mul_of_nonneg_left hd2
            (mul_nonneg
              (mul_nonneg
                (div_nonneg (mul_nonneg hKΔ₀ hB) (by norm_num)) hs₁.1) hD)
        _ = _ := by ring
    have hsecond : |e₂ s * (A₁ s - A₂ s)| ≤ C * (s - u) * D := by
      rw [abs_mul, abs_of_nonneg he₂pos]
      exact (mul_le_of_le_one_left (abs_nonneg _) he₂le).trans hAdiff
    calc
      _ = |(e₁ s - e₂ s) * A₁ s + e₂ s * (A₁ s - A₂ s)| := by
        congr 1
        ring
      _ ≤ |(e₁ s - e₂ s) * A₁ s| + |e₂ s * (A₁ s - A₂ s)| :=
        abs_add_le _ _
      _ ≤ _ := by nlinarith only [hfirst, hsecond]
  have hi₁ := horizontal_integrand_intervalIntegrable hab hu huv hv hj₁ hk₁
  have hi₂ := horizontal_integrand_intervalIntegrable hab hu huv hv hj₂ hk₂
  have hA : 0 ≤ (KΔ₀ * B / 2 + C) * D :=
    mul_nonneg
      (add_nonneg (div_nonneg (mul_nonneg hKΔ₀ hB) (by norm_num)) hC) hD
  have hbound : ∀ s ∈ Icc u v,
      |e₁ s * A₁ s - e₂ s * A₂ s| ≤
        ((KΔ₀ * B / 2 + C) * D) * (s - u) := by
    intro s hs
    calc
      _ ≤ (KΔ₀ * B / 2 + C) * (s - u) * D := hpoint s hs
      _ = _ := by ring
  have hmain := abs_integral_le_half_sq_of_abs_le_linear
    (A := (KΔ₀ * B / 2 + C) * D) huv hA
    (hi₁.sub hi₂) hbound
  rw [fderivWithin_attenuatedVolterraIntegral_horizontal hab hj₁ hk₁ hjdiag₁
    (show (u, v) ∈ K from ⟨hu, huv, hv⟩),
    fderivWithin_attenuatedVolterraIntegral_horizontal hab hj₂ hk₂ hjdiag₂
    (show (u, v) ∈ K from ⟨hu, huv, hv⟩)]
  rw [← intervalIntegral.integral_sub hi₁ hi₂]
  dsimp only [B, C] at hmain
  nlinarith only [hmain]

end intervalIntegral

end
