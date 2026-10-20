module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMean
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Quantitative estimates for positive weighted diagonal means

The estimates use the normalized vertical interval. They apply on any closed
coordinate triangle and do not depend on a choice of its initial point.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

private theorem integral_one_sub :
    (∫ t in (0 : ℝ)..1, (1 - t)) = 1 / 2 := by
  rw [intervalIntegral.integral_sub]
  · simp [integral_id]
    norm_num
  · exact continuous_const.intervalIntegrable _ _
  · exact continuous_id.intervalIntegrable _ _

private theorem abs_integral_le_mul_half {A : ℝ} {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 1)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, |g t| ≤ A * (1 - t)) :
    |∫ t in (0 : ℝ)..1, g t| ≤ A / 2 := by
  have hmaj : IntervalIntegrable (fun t : ℝ => A * (1 - t)) volume 0 1 := by
    exact (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _
  have hupper : (∫ t in (0 : ℝ)..1, g t) ≤ A / 2 := by
    have h := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
      hg hmaj (fun t ht => (abs_le.mp (hbound t ht)).2)
    simpa [intervalIntegral.integral_const_mul, integral_one_sub, div_eq_mul_inv] using h
  have hlower : -(∫ t in (0 : ℝ)..1, g t) ≤ A / 2 := by
    have h := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
      hg.neg hmaj (fun t ht => by
        have hlt := (abs_le.mp (hbound t ht)).1
        dsimp
        linarith)
    simpa [intervalIntegral.integral_const_mul, integral_one_sub, div_eq_mul_inv] using h
  exact abs_le.mpr ⟨by linarith, hupper⟩

private theorem abs_integral_le_const {D : ℝ} {g : ℝ → ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, |g t| ≤ D) :
    |∫ t in (0 : ℝ)..1, g t| ≤ D := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := D) (f := g) (by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by
        rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
        exact ⟨ht.1.le, ht.2⟩
      simpa only [Real.norm_eq_abs] using hbound t ht')
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h

/-- Stability of a quotient with two positive denominators, in terms of
separate numerator and denominator differences. -/
theorem abs_div_sub_div_le {x₁ x₂ y₁ y₂ c X Y Z : ℝ}
    (hc : 0 < c) (hy₁ : c ≤ y₁) (hy₂ : c ≤ y₂)
    (hx : |x₁ - x₂| ≤ X) (hy : |y₁ - y₂| ≤ Y)
    (hx₂ : |x₂| ≤ Z) :
    |x₁ / y₁ - x₂ / y₂| ≤ X / c + Z * Y / c ^ 2 := by
  have hy₁pos : 0 < y₁ := hc.trans_le hy₁
  have hy₂pos : 0 < y₂ := hc.trans_le hy₂
  have hX : 0 ≤ X := (abs_nonneg _).trans hx
  have hY : 0 ≤ Y := (abs_nonneg _).trans hy
  have hZ : 0 ≤ Z := (abs_nonneg _).trans hx₂
  have hprod : c * c ≤ y₁ * y₂ := by
    calc
      c * c ≤ y₁ * c := mul_le_mul_of_nonneg_right hy₁ hc.le
      _ ≤ y₁ * y₂ := mul_le_mul_of_nonneg_left hy₂ hy₁pos.le
  have hident : x₁ / y₁ - x₂ / y₂ =
      (x₁ - x₂) / y₁ + x₂ * (y₂ - y₁) / (y₁ * y₂) := by
    field_simp
    ring
  rw [hident]
  calc
    |(x₁ - x₂) / y₁ + x₂ * (y₂ - y₁) / (y₁ * y₂)| ≤
        |(x₁ - x₂) / y₁| + |x₂ * (y₂ - y₁) / (y₁ * y₂)| := abs_add_le _ _
    _ = |x₁ - x₂| / y₁ + |x₂| * |y₂ - y₁| / (y₁ * y₂) := by
      rw [abs_div, abs_of_pos hy₁pos, abs_div, abs_mul,
        abs_of_pos (mul_pos hy₁pos hy₂pos)]
    _ ≤ X / c + Z * Y / c ^ 2 := by
      have hfirst : |x₁ - x₂| / y₁ ≤ X / c := by
        calc
          |x₁ - x₂| / y₁ ≤ X / y₁ := by gcongr
          _ ≤ X / c := div_le_div_of_nonneg_left hX hc hy₁
      have hsecond : |x₂| * |y₂ - y₁| / (y₁ * y₂) ≤ Z * Y / c ^ 2 := by
        have hnum : |x₂| * |y₂ - y₁| ≤ Z * Y := by
          exact mul_le_mul hx₂ (by simpa [abs_sub_comm] using hy)
            (abs_nonneg _) hZ
        calc
          |x₂| * |y₂ - y₁| / (y₁ * y₂) ≤ Z * Y / (y₁ * y₂) := by
            gcongr
          _ ≤ Z * Y / (c * c) :=
            div_le_div_of_nonneg_left (mul_nonneg hZ hY) (mul_pos hc hc) hprod
          _ = Z * Y / c ^ 2 := by ring
      exact add_le_add hfirst hsecond

/-- Two positive weighted integrals have a Lipschitz normalized quotient when
the weights and the integrands have the indicated pointwise bounds. The factor
`1/2` comes from integrating the distance to the endpoint on `[0,1]`. -/
theorem abs_weighted_integral_quotient_sub_le
    {w₁ w₂ e₁ e₂ : ℝ → ℝ} {c C B d D : ℝ}
    (hc : 0 < c) (hD : 0 ≤ D)
    (hw₁ : ContinuousOn w₁ (Icc (0 : ℝ) 1))
    (hw₂ : ContinuousOn w₂ (Icc (0 : ℝ) 1))
    (he₁ : ContinuousOn e₁ (Icc (0 : ℝ) 1))
    (he₂ : ContinuousOn e₂ (Icc (0 : ℝ) 1))
    (hweight₁ : ∀ t ∈ Icc (0 : ℝ) 1, c ≤ w₁ t)
    (hweight₂ : ∀ t ∈ Icc (0 : ℝ) 1, c ≤ w₂ t ∧ w₂ t ≤ C)
    (hwdiff : ∀ t ∈ Icc (0 : ℝ) 1, |w₁ t - w₂ t| ≤ D)
    (he₁bound : ∀ t ∈ Icc (0 : ℝ) 1, |e₁ t| ≤ B * d * (1 - t))
    (he₂bound : ∀ t ∈ Icc (0 : ℝ) 1, |e₂ t| ≤ B * d * (1 - t))
    (hediff : ∀ t ∈ Icc (0 : ℝ) 1, |e₁ t - e₂ t| ≤ D * d * (1 - t)) :
    |(∫ t in (0 : ℝ)..1, w₁ t * e₁ t) / (∫ t in (0 : ℝ)..1, w₁ t) -
      (∫ t in (0 : ℝ)..1, w₂ t * e₂ t) / (∫ t in (0 : ℝ)..1, w₂ t)| ≤
      ((B + C) / (2 * c) + C * B / (2 * c ^ 2)) * d * D := by
  have hw₁i : IntervalIntegrable w₁ volume 0 1 :=
    hw₁.intervalIntegrable_of_Icc (by norm_num)
  have hw₂i : IntervalIntegrable w₂ volume 0 1 :=
    hw₂.intervalIntegrable_of_Icc (by norm_num)
  have hn₁i : IntervalIntegrable (fun t => w₁ t * e₁ t) volume 0 1 :=
    (hw₁.mul he₁).intervalIntegrable_of_Icc (by norm_num)
  have hn₂i : IntervalIntegrable (fun t => w₂ t * e₂ t) volume 0 1 :=
    (hw₂.mul he₂).intervalIntegrable_of_Icc (by norm_num)
  have hden₁ : c ≤ ∫ t in (0 : ℝ)..1, w₁ t := by
    have h := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
      (by exact continuous_const.intervalIntegrable _ _) hw₁i hweight₁
    simpa using h
  have hden₂ : c ≤ ∫ t in (0 : ℝ)..1, w₂ t := by
    have h := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
      (by exact continuous_const.intervalIntegrable _ _) hw₂i
      (fun t ht => (hweight₂ t ht).1)
    simpa using h
  have hC : 0 ≤ C := (hc.le.trans (hweight₂ 0 (by norm_num)).1).trans
    (hweight₂ 0 (by norm_num)).2
  have hdenDiff : |(∫ t in (0 : ℝ)..1, w₁ t) -
      (∫ t in (0 : ℝ)..1, w₂ t)| ≤ D := by
    rw [← intervalIntegral.integral_sub hw₁i hw₂i]
    exact abs_integral_le_const hwdiff
  have hnum₂ : |∫ t in (0 : ℝ)..1, w₂ t * e₂ t| ≤ C * B * d / 2 := by
    apply abs_integral_le_mul_half hn₂i
    intro t ht
    have ht₁ : 0 ≤ 1 - t := by linarith [ht.2]
    have hwt : 0 ≤ w₂ t := (hc.le.trans (hweight₂ t ht).1)
    rw [abs_mul, abs_of_nonneg hwt]
    calc
      w₂ t * |e₂ t| ≤ C * (B * d * (1 - t)) :=
        mul_le_mul (hweight₂ t ht).2 (he₂bound t ht)
          (abs_nonneg _) hC
      _ = (C * B * d) * (1 - t) := by ring
  have hnumDiff : |(∫ t in (0 : ℝ)..1, w₁ t * e₁ t) -
      (∫ t in (0 : ℝ)..1, w₂ t * e₂ t)| ≤ (B + C) * d * D / 2 := by
    rw [← intervalIntegral.integral_sub hn₁i hn₂i]
    apply abs_integral_le_mul_half (hn₁i.sub hn₂i)
    intro t ht
    have ht₁ : 0 ≤ 1 - t := by linarith [ht.2]
    have hwt : 0 ≤ w₂ t := hc.le.trans (hweight₂ t ht).1
    have hid : w₁ t * e₁ t - w₂ t * e₂ t =
        (w₁ t - w₂ t) * e₁ t + w₂ t * (e₁ t - e₂ t) := by ring
    rw [hid]
    calc
      |(w₁ t - w₂ t) * e₁ t + w₂ t * (e₁ t - e₂ t)| ≤
          |w₁ t - w₂ t| * |e₁ t| + |w₂ t| * |e₁ t - e₂ t| := by
            simpa [abs_mul] using abs_add_le ((w₁ t - w₂ t) * e₁ t)
              (w₂ t * (e₁ t - e₂ t))
      _ ≤ D * (B * d * (1 - t)) + C * (D * d * (1 - t)) := by
        apply add_le_add
        · exact mul_le_mul (hwdiff t ht) (he₁bound t ht) (abs_nonneg _) hD
        · rw [abs_of_nonneg hwt]
          exact mul_le_mul (hweight₂ t ht).2 (hediff t ht) (abs_nonneg _) hC
      _ = ((B + C) * d * D) * (1 - t) := by ring
  have hq := abs_div_sub_div_le hc hden₁ hden₂ hnumDiff hdenDiff hnum₂
  convert hq using 1; ring

/-- The normalized formula for the weighted diagonal error, valid up to the
diagonal whenever the weight has a positive lower bound. -/
theorem weightedDiagonalError_eq_normalized_integral
    {a b c : ℝ} {w f : ℝ × ℝ → ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    weightedDiagonalError w f p =
      (∫ t in (0 : ℝ)..1,
        w (diagonalSegment p t) * (f p - f (diagonalSegment p t))) /
      (∫ t in (0 : ℝ)..1, w (diagonalSegment p t)) := by
  have hmap : MapsTo (fun t : ℝ => diagonalSegment p t)
      (Icc (0 : ℝ) 1) (closedCoordTriangle a b) :=
    fun t ht => diagonalSegment_mem_closedCoordTriangle hp ht
  have hseg : ContinuousOn (fun t : ℝ => diagonalSegment p t) (Icc 0 1) := by
    unfold diagonalSegment
    fun_prop
  have hwseg := hw.comp hseg hmap
  have hfseg := hf.comp hseg hmap
  have hwint : IntervalIntegrable (fun t => w (diagonalSegment p t)) volume 0 1 :=
    hwseg.intervalIntegrable_of_Icc (by norm_num)
  have hwfint : IntervalIntegrable
      (fun t => w (diagonalSegment p t) * f (diagonalSegment p t)) volume 0 1 :=
    (hwseg.mul hfseg).intervalIntegrable_of_Icc (by norm_num)
  have hwconst : IntervalIntegrable
      (fun t => w (diagonalSegment p t) * f p) volume 0 1 :=
    hwint.mul_const _
  have hden : 0 < ∫ t in (0 : ℝ)..1, w (diagonalSegment p t) :=
    hc.trans_le (integral_diagonalSegment_weight_ge hw hweight hp)
  have hnum : (∫ t in (0 : ℝ)..1,
        w (diagonalSegment p t) * (f p - f (diagonalSegment p t))) =
      (∫ t in (0 : ℝ)..1, w (diagonalSegment p t)) * f p -
      (∫ t in (0 : ℝ)..1,
        w (diagonalSegment p t) * f (diagonalSegment p t)) := by
    simp only [mul_sub, intervalIntegral.integral_sub hwconst hwfint,
      intervalIntegral.integral_mul_const]
  rw [hnum]
  unfold weightedDiagonalError weightedDiagonalMean
  field_simp [hden.ne']

/-- The difference of two weighted diagonal errors is bounded by the sum of
the differences of their weights and vertical first jets. The coefficient is
the exact normalized-integral coefficient. -/
theorem abs_weightedDiagonalError_sub_le_of_jets
    {a b c C B D : ℝ} {w₁ w₂ f₁ f₂ : ℝ × ℝ → ℝ}
    {G₁ G₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hc : 0 < c) (hD : 0 ≤ D)
    (hw₁ : ContinuousOn w₁ (closedCoordTriangle a b))
    (hw₂ : ContinuousOn w₂ (closedCoordTriangle a b))
    (hf₁ : ContinuousOn f₁ (closedCoordTriangle a b))
    (hf₂ : ContinuousOn f₂ (closedCoordTriangle a b))
    (hweight₁ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₁ p)
    (hweight₂ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₂ p ∧ w₂ p ≤ C)
    (hwdiff : ∀ p ∈ closedCoordTriangle a b, |w₁ p - w₂ p| ≤ D)
    (hjet₁ : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt f₁ (G₁ p) (closedCoordTriangle a b) p)
    (hjet₂ : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt f₂ (G₂ p) (closedCoordTriangle a b) p)
    (hvertical₁ : ∀ p ∈ closedCoordTriangle a b, |G₁ p (0, 1)| ≤ B)
    (hvertical₂ : ∀ p ∈ closedCoordTriangle a b, |G₂ p (0, 1)| ≤ B)
    (hverticalDiff : ∀ p ∈ closedCoordTriangle a b,
      |G₁ p (0, 1) - G₂ p (0, 1)| ≤ D)
    {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) :
    |weightedDiagonalError w₁ f₁ (u, v) -
      weightedDiagonalError w₂ f₂ (u, v)| ≤
      ((B + C) / (2 * c) + C * B / (2 * c ^ 2)) * (v - u) * D := by
  let p : ℝ × ℝ := (u, v)
  let s (t : ℝ) : ℝ := u + t * (v - u)
  let e₁ (t : ℝ) : ℝ := f₁ p - f₁ (diagonalSegment p t)
  let e₂ (t : ℝ) : ℝ := f₂ p - f₂ (diagonalSegment p t)
  have hp : p ∈ closedCoordTriangle a b := by
    simpa only [p, closedCoordTriangle, Set.mem_ofPred_eq] using
      (show a ≤ u ∧ u ≤ v ∧ v ≤ b from ⟨hu, huv, hv⟩)
  have hseg : ContinuousOn (fun t : ℝ => diagonalSegment p t) (Icc 0 1) := by
    unfold diagonalSegment
    fun_prop
  have hmap : MapsTo (fun t : ℝ => diagonalSegment p t)
      (Icc (0 : ℝ) 1) (closedCoordTriangle a b) :=
    fun t ht => diagonalSegment_mem_closedCoordTriangle hp ht
  have he₁ : ContinuousOn e₁ (Icc (0 : ℝ) 1) := by
    exact continuousOn_const.sub (hf₁.comp hseg hmap)
  have he₂ : ContinuousOn e₂ (Icc (0 : ℝ) 1) := by
    exact continuousOn_const.sub (hf₂.comp hseg hmap)
  have hlocation (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      u ≤ s t ∧ s t ≤ v ∧ v - s t = (v - u) * (1 - t) := by
    have hd : 0 ≤ v - u := sub_nonneg.mpr huv
    have h₁ := mul_nonneg ht.1 hd
    have h₂ := mul_nonneg (sub_nonneg.mpr ht.2) hd
    dsimp [s]
    constructor
    · linarith
    constructor
    · nlinarith
    · ring
  have hseg_eq (t : ℝ) : diagonalSegment p t = (u, s t) := rfl
  have he₁bound : ∀ t ∈ Icc (0 : ℝ) 1,
      |e₁ t| ≤ B * (v - u) * (1 - t) := by
    intro t ht
    obtain ⟨hus, hsv, hdist⟩ := hlocation t ht
    have h := norm_sub_vertical_le_of_jet hjet₁
      (fun p hp => by simpa only [Real.norm_eq_abs] using hvertical₁ p hp)
      hu hus hsv hv
    rw [← hseg_eq t] at h
    simpa only [e₁, p, Real.norm_eq_abs, hdist, mul_assoc] using h
  have he₂bound : ∀ t ∈ Icc (0 : ℝ) 1,
      |e₂ t| ≤ B * (v - u) * (1 - t) := by
    intro t ht
    obtain ⟨hus, hsv, hdist⟩ := hlocation t ht
    have h := norm_sub_vertical_le_of_jet hjet₂
      (fun p hp => by simpa only [Real.norm_eq_abs] using hvertical₂ p hp)
      hu hus hsv hv
    rw [← hseg_eq t] at h
    simpa only [e₂, p, Real.norm_eq_abs, hdist, mul_assoc] using h
  let Gdiff : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun p => G₁ p - G₂ p
  have hjetdiff : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt (f₁ - f₂) (Gdiff p) (closedCoordTriangle a b) p := by
    intro z hz
    exact (hjet₁ z hz).sub (hjet₂ z hz)
  have hbounddiff : ∀ p ∈ closedCoordTriangle a b,
      ‖Gdiff p (0, 1)‖ ≤ D := by
    intro z hz
    simpa only [Gdiff, sub_apply, Real.norm_eq_abs] using
      hverticalDiff z hz
  have hediff : ∀ t ∈ Icc (0 : ℝ) 1,
      |e₁ t - e₂ t| ≤ D * (v - u) * (1 - t) := by
    intro t ht
    obtain ⟨hus, hsv, hdist⟩ := hlocation t ht
    have h := norm_sub_vertical_le_of_jet hjetdiff hbounddiff hu hus hsv hv
    rw [← hseg_eq t] at h
    have hid : e₁ t - e₂ t = (f₁ - f₂) p - (f₁ - f₂) (diagonalSegment p t) := by
      dsimp [e₁, e₂]
      ring
    rw [hid]
    simpa only [p, Pi.sub_apply, Real.norm_eq_abs, hdist, mul_assoc] using h
  have hmean₁ := weightedDiagonalError_eq_normalized_integral hw₁ hf₁
    hweight₁ hc hp
  have hmean₂ := weightedDiagonalError_eq_normalized_integral hw₂ hf₂
    (fun z hz => (hweight₂ z hz).1) hc hp
  rw [hmean₁, hmean₂]
  exact abs_weighted_integral_quotient_sub_le hc hD
    (hw₁.comp hseg hmap) (hw₂.comp hseg hmap) he₁ he₂
    (fun t ht => hweight₁ _ (hmap ht))
    (fun t ht => hweight₂ _ (hmap ht))
    (fun t ht => hwdiff _ (hmap ht))
    he₁bound he₂bound hediff

/-- An upper bound on a weight gives the corresponding upper bound on its
vertical radius. -/
theorem weightedDiagonalRadius_le_mul_sub
    {a b C : ℝ} {w : ℝ × ℝ → ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hupper : ∀ p ∈ closedCoordTriangle a b, w p ≤ C)
    {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) :
    weightedDiagonalRadius w (u, v) ≤ C * (v - u) := by
  have hint : IntervalIntegrable (fun s => w (u, s)) volume u v := by
    apply ContinuousOn.intervalIntegrable_of_Icc huv
    apply hw.comp (continuous_const.prodMk continuous_id).continuousOn
    intro s hs
    simpa only [closedCoordTriangle, Set.mem_ofPred_eq, id_eq] using
      (show a ≤ u ∧ u ≤ s ∧ s ≤ b from ⟨hu, hs.1, hs.2.trans hv⟩)
  have h := intervalIntegral.integral_mono_on huv hint
    (by exact continuous_const.intervalIntegrable _ _)
    (fun s hs => hupper (u, s) (by
      simpa only [closedCoordTriangle, Set.mem_ofPred_eq] using
        (show a ≤ u ∧ u ≤ s ∧ s ≤ b from ⟨hu, hs.1, hs.2.trans hv⟩)))
  simpa [weightedDiagonalRadius, mul_comm] using h

/-- Uniformly close weights have uniformly close vertical radii, with one
factor of the vertical interval length. -/
theorem abs_weightedDiagonalRadius_sub_le
    {a b D : ℝ} {w₁ w₂ : ℝ × ℝ → ℝ}
    (hw₁ : ContinuousOn w₁ (closedCoordTriangle a b))
    (hw₂ : ContinuousOn w₂ (closedCoordTriangle a b))
    (hwdiff : ∀ p ∈ closedCoordTriangle a b, |w₁ p - w₂ p| ≤ D)
    {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) :
    |weightedDiagonalRadius w₁ (u, v) -
      weightedDiagonalRadius w₂ (u, v)| ≤ D * (v - u) := by
  rw [weightedDiagonalRadius_eq_mul_integral,
    weightedDiagonalRadius_eq_mul_integral]
  have hp : (u, v) ∈ closedCoordTriangle a b := by
    simpa only [closedCoordTriangle, Set.mem_ofPred_eq] using
      (show a ≤ u ∧ u ≤ v ∧ v ≤ b from ⟨hu, huv, hv⟩)
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1,
      diagonalSegment (u, v) t ∈ closedCoordTriangle a b :=
    fun t ht => diagonalSegment_mem_closedCoordTriangle hp ht
  have hdiff : |(∫ t in (0 : ℝ)..1, w₁ (diagonalSegment (u, v) t)) -
      (∫ t in (0 : ℝ)..1, w₂ (diagonalSegment (u, v) t))| ≤ D := by
    have hcontseg : ContinuousOn (fun t : ℝ => diagonalSegment (u, v) t)
        (Icc (0 : ℝ) 1) := by
      unfold diagonalSegment
      fun_prop
    have hcont₁ : ContinuousOn (fun t => w₁ (diagonalSegment (u, v) t))
        (Icc (0 : ℝ) 1) := by
      exact hw₁.comp hcontseg hseg
    have hcont₂ : ContinuousOn (fun t => w₂ (diagonalSegment (u, v) t))
        (Icc (0 : ℝ) 1) := by
      exact hw₂.comp hcontseg hseg
    rw [← intervalIntegral.integral_sub
      (hcont₁.intervalIntegrable_of_Icc (by norm_num))
      (hcont₂.intervalIntegrable_of_Icc (by norm_num))]
    exact abs_integral_le_const (fun t ht => hwdiff _ (hseg t ht))
  rw [← mul_sub]
  rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr huv)]
  calc
    (v - u) * |(∫ t in (0 : ℝ)..1, w₁ (diagonalSegment (u, v) t)) -
        (∫ t in (0 : ℝ)..1, w₂ (diagonalSegment (u, v) t))| ≤
        (v - u) * D := mul_le_mul_of_nonneg_left hdiff (sub_nonneg.mpr huv)
    _ = D * (v - u) := mul_comm _ _
end intervalIntegral

end
