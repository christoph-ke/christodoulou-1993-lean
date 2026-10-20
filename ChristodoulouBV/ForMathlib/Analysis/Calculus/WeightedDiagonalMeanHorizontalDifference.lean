module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMeanHorizontalEstimates
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Two-input horizontal bounds for weighted diagonal means

The estimates use the unit-interval representation and the lower-endpoint
formula for the horizontal derivative.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

private theorem abs_integral_le_mul_half_id {A : ℝ} {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 1)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, |g t| ≤ A * t) :
    |∫ t in (0 : ℝ)..1, g t| ≤ A / 2 := by
  have hmaj : IntervalIntegrable (fun t : ℝ => A * t) volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hhalf : (∫ t in (0 : ℝ)..1, t) = 1 / 2 := by
    norm_num [integral_id]
  have hupper : (∫ t in (0 : ℝ)..1, g t) ≤ A / 2 := by
    have h := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
      hg hmaj (fun t ht => (abs_le.mp (hbound t ht)).2)
    rw [intervalIntegral.integral_const_mul, hhalf] at h
    simpa [div_eq_mul_inv] using h
  have hlower : -(∫ t in (0 : ℝ)..1, g t) ≤ A / 2 := by
    have h := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
      hg.neg hmaj (fun t ht => by
        have hlt := (abs_le.mp (hbound t ht)).1
        change -g t ≤ A * t
        linarith)
    rw [intervalIntegral.integral_const_mul, hhalf] at h
    simpa [div_eq_mul_inv] using h
  exact abs_le.mpr ⟨by linarith, hupper⟩

/-- Subtracting an arbitrary anchor from a positive normalized mean centers
the numerator of its integral representation. -/
theorem weightedDiagonalMean_sub_anchor_eq_integral
    {a b c : ℝ} {w f : ℝ × ℝ → ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (z : ℝ) :
    weightedDiagonalMean w f p - z =
      (∫ t in (0 : ℝ)..1,
        w (diagonalSegment p t) * (f (diagonalSegment p t) - z)) /
        (∫ t in (0 : ℝ)..1, w (diagonalSegment p t)) := by
  have hseg : ContinuousOn (fun t : ℝ => diagonalSegment p t) (Icc 0 1) := by
    unfold diagonalSegment
    fun_prop
  have hmap : MapsTo (diagonalSegment p) (Icc (0 : ℝ) 1)
      (closedCoordTriangle a b) :=
    fun t ht => diagonalSegment_mem_closedCoordTriangle hp ht
  have hwseg : ContinuousOn (fun t => w (diagonalSegment p t)) (Icc (0 : ℝ) 1) :=
    hw.comp hseg hmap
  have hfseg : ContinuousOn (fun t => f (diagonalSegment p t)) (Icc (0 : ℝ) 1) :=
    hf.comp hseg hmap
  have hwi : IntervalIntegrable (fun t => w (diagonalSegment p t)) volume 0 1 :=
    hwseg.intervalIntegrable_of_Icc (by norm_num)
  have hn : IntervalIntegrable
      (fun t => w (diagonalSegment p t) * f (diagonalSegment p t)) volume 0 1 :=
    (hwseg.mul hfseg).intervalIntegrable_of_Icc (by norm_num)
  have hden : (∫ t in (0 : ℝ)..1, w (diagonalSegment p t)) ≠ 0 :=
    ne_of_gt (hc.trans_le (integral_diagonalSegment_weight_ge hw hweight hp))
  have hnum : (∫ t in (0 : ℝ)..1,
      w (diagonalSegment p t) * (f (diagonalSegment p t) - z)) =
      (∫ t in (0 : ℝ)..1,
        w (diagonalSegment p t) * f (diagonalSegment p t)) -
      z * (∫ t in (0 : ℝ)..1, w (diagonalSegment p t)) := by
    simp_rw [mul_sub, mul_comm (w _) z]
    rw [intervalIntegral.integral_sub hn (hwi.const_mul z),
      intervalIntegral.integral_const_mul]
  rw [hnum]
  simp only [weightedDiagonalMean]
  field_simp [hden]

/-- Two positive normalized weighted integrals are stable when their
integrands vanish linearly at the *left* endpoint. -/
theorem abs_weighted_integral_quotient_sub_le_left
    {w₁ w₂ e₁ e₂ : ℝ → ℝ} {c C B d D : ℝ}
    (hc : 0 < c) (hD : 0 ≤ D)
    (hw₁ : ContinuousOn w₁ (Icc (0 : ℝ) 1))
    (hw₂ : ContinuousOn w₂ (Icc (0 : ℝ) 1))
    (he₁ : ContinuousOn e₁ (Icc (0 : ℝ) 1))
    (he₂ : ContinuousOn e₂ (Icc (0 : ℝ) 1))
    (hweight₁ : ∀ t ∈ Icc (0 : ℝ) 1, c ≤ w₁ t)
    (hweight₂ : ∀ t ∈ Icc (0 : ℝ) 1, c ≤ w₂ t ∧ w₂ t ≤ C)
    (hwdiff : ∀ t ∈ Icc (0 : ℝ) 1, |w₁ t - w₂ t| ≤ D)
    (he₁bound : ∀ t ∈ Icc (0 : ℝ) 1, |e₁ t| ≤ B * d * t)
    (he₂bound : ∀ t ∈ Icc (0 : ℝ) 1, |e₂ t| ≤ B * d * t)
    (hediff : ∀ t ∈ Icc (0 : ℝ) 1, |e₁ t - e₂ t| ≤ D * d * t) :
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
      (continuous_const.intervalIntegrable _ _) hw₁i hweight₁
    simpa using h
  have hden₂ : c ≤ ∫ t in (0 : ℝ)..1, w₂ t := by
    have h := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
      (continuous_const.intervalIntegrable _ _) hw₂i
      (fun t ht => (hweight₂ t ht).1)
    simpa using h
  have hC : 0 ≤ C :=
    (hc.le.trans (hweight₂ 0 (by norm_num)).1).trans (hweight₂ 0 (by norm_num)).2
  have hdenDiff : |(∫ t in (0 : ℝ)..1, w₁ t) -
      (∫ t in (0 : ℝ)..1, w₂ t)| ≤ D := by
    rw [← intervalIntegral.integral_sub hw₁i hw₂i]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := D)
      (f := fun t => w₁ t - w₂ t) (fun t ht => by
        have ht' : t ∈ Icc (0 : ℝ) 1 := by
          rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
          exact ⟨ht.1.le, ht.2⟩
        simpa only [Real.norm_eq_abs] using hwdiff t ht')
    simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h
  have hnum₂ : |∫ t in (0 : ℝ)..1, w₂ t * e₂ t| ≤ C * B * d / 2 := by
    apply abs_integral_le_mul_half_id hn₂i
    intro t ht
    have hwt : 0 ≤ w₂ t := hc.le.trans (hweight₂ t ht).1
    rw [abs_mul, abs_of_nonneg hwt]
    calc
      w₂ t * |e₂ t| ≤ C * (B * d * t) :=
        mul_le_mul (hweight₂ t ht).2 (he₂bound t ht) (abs_nonneg _) hC
      _ = (C * B * d) * t := by ring
  have hnumDiff : |(∫ t in (0 : ℝ)..1, w₁ t * e₁ t) -
      (∫ t in (0 : ℝ)..1, w₂ t * e₂ t)| ≤ (B + C) * d * D / 2 := by
    rw [← intervalIntegral.integral_sub hn₁i hn₂i]
    apply abs_integral_le_mul_half_id (hn₁i.sub hn₂i)
    intro t ht
    have hwt : 0 ≤ w₂ t := hc.le.trans (hweight₂ t ht).1
    have hid : w₁ t * e₁ t - w₂ t * e₂ t =
        (w₁ t - w₂ t) * e₁ t + w₂ t * (e₁ t - e₂ t) := by ring
    rw [hid]
    calc
      |(w₁ t - w₂ t) * e₁ t + w₂ t * (e₁ t - e₂ t)| ≤
          |w₁ t - w₂ t| * |e₁ t| + |w₂ t| * |e₁ t - e₂ t| := by
            simpa [abs_mul] using abs_add_le ((w₁ t - w₂ t) * e₁ t)
              (w₂ t * (e₁ t - e₂ t))
      _ ≤ D * (B * d * t) + C * (D * d * t) := by
        apply add_le_add
        · exact mul_le_mul (hwdiff t ht) (he₁bound t ht) (abs_nonneg _) hD
        · rw [abs_of_nonneg hwt]
          exact mul_le_mul (hweight₂ t ht).2 (hediff t ht) (abs_nonneg _) hC
      _ = ((B + C) * d * D) * t := by ring
  have hq := abs_div_sub_div_le hc hden₁ hden₂ hnumDiff hdenDiff hnum₂
  convert hq using 1 <;> ring

/-- Two weighted means, each centered at its lower endpoint, have the same
two-input difference coefficient as errors centered at the upper endpoint. -/
theorem abs_weightedDiagonalMean_sub_lower_sub_le_of_jets
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
    |(weightedDiagonalMean w₁ f₁ (u, v) - f₁ (u, u)) -
      (weightedDiagonalMean w₂ f₂ (u, v) - f₂ (u, u))| ≤
      ((B + C) / (2 * c) + C * B / (2 * c ^ 2)) * (v - u) * D := by
  let p : ℝ × ℝ := (u, v)
  let s (t : ℝ) : ℝ := u + t * (v - u)
  let e₁ (t : ℝ) : ℝ := f₁ (diagonalSegment p t) - f₁ (u, u)
  let e₂ (t : ℝ) : ℝ := f₂ (diagonalSegment p t) - f₂ (u, u)
  have hp : p ∈ closedCoordTriangle a b := ⟨hu, huv, hv⟩
  have hseg : ContinuousOn (fun t : ℝ => diagonalSegment p t) (Icc 0 1) := by
    unfold diagonalSegment
    fun_prop
  have hmap : MapsTo (diagonalSegment p) (Icc (0 : ℝ) 1)
      (closedCoordTriangle a b) :=
    fun t ht => diagonalSegment_mem_closedCoordTriangle hp ht
  have he₁ : ContinuousOn e₁ (Icc (0 : ℝ) 1) :=
    (hf₁.comp hseg hmap).sub continuousOn_const
  have he₂ : ContinuousOn e₂ (Icc (0 : ℝ) 1) :=
    (hf₂.comp hseg hmap).sub continuousOn_const
  have hlocation (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      u ≤ s t ∧ s t ≤ v ∧ s t - u = (v - u) * t := by
    have hd : 0 ≤ v - u := sub_nonneg.mpr huv
    have h₁ := mul_nonneg ht.1 hd
    have h₂ := mul_nonneg (sub_nonneg.mpr ht.2) hd
    dsimp [s]
    constructor
    · linarith
    constructor
    · nlinarith
    · ring
  have he₁bound : ∀ t ∈ Icc (0 : ℝ) 1,
      |e₁ t| ≤ B * (v - u) * t := by
    intro t ht
    obtain ⟨hus, hsv, hdist⟩ := hlocation t ht
    have h := norm_sub_vertical_le_of_jet hjet₁
      (fun z hz => by simpa only [Real.norm_eq_abs] using hvertical₁ z hz)
      hu le_rfl hus (hsv.trans hv)
    simpa only [e₁, p, diagonalSegment, s, Real.norm_eq_abs, hdist,
      mul_assoc] using h
  have he₂bound : ∀ t ∈ Icc (0 : ℝ) 1,
      |e₂ t| ≤ B * (v - u) * t := by
    intro t ht
    obtain ⟨hus, hsv, hdist⟩ := hlocation t ht
    have h := norm_sub_vertical_le_of_jet hjet₂
      (fun z hz => by simpa only [Real.norm_eq_abs] using hvertical₂ z hz)
      hu le_rfl hus (hsv.trans hv)
    simpa only [e₂, p, diagonalSegment, s, Real.norm_eq_abs, hdist,
      mul_assoc] using h
  let Gdiff : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun z => G₁ z - G₂ z
  have hjetdiff : ∀ z ∈ closedCoordTriangle a b,
      HasFDerivWithinAt (f₁ - f₂) (Gdiff z) (closedCoordTriangle a b) z := by
    intro z hz
    exact (hjet₁ z hz).sub (hjet₂ z hz)
  have hbounddiff : ∀ z ∈ closedCoordTriangle a b,
      ‖Gdiff z (0, 1)‖ ≤ D := by
    intro z hz
    simpa only [Gdiff, sub_apply, Real.norm_eq_abs] using hverticalDiff z hz
  have hediff : ∀ t ∈ Icc (0 : ℝ) 1,
      |e₁ t - e₂ t| ≤ D * (v - u) * t := by
    intro t ht
    obtain ⟨hus, hsv, hdist⟩ := hlocation t ht
    have h := norm_sub_vertical_le_of_jet hjetdiff hbounddiff
      hu le_rfl hus (hsv.trans hv)
    have hid : e₁ t - e₂ t =
        (f₁ - f₂) (diagonalSegment p t) - (f₁ - f₂) (u, u) := by
      dsimp [e₁, e₂]
      ring
    rw [hid]
    simpa only [p, diagonalSegment, s, Pi.sub_apply, Real.norm_eq_abs,
      hdist, mul_assoc] using h
  rw [weightedDiagonalMean_sub_anchor_eq_integral hw₁ hf₁ hweight₁ hc hp (f₁ (u, u)),
    weightedDiagonalMean_sub_anchor_eq_integral hw₂ hf₂
      (fun z hz => (hweight₂ z hz).1) hc hp (f₂ (u, u))]
  exact abs_weighted_integral_quotient_sub_le_left hc hD
    (hw₁.comp hseg hmap) (hw₂.comp hseg hmap) he₁ he₂
    (fun t ht => hweight₁ _ (hmap ht))
    (fun t ht => hweight₂ _ (hmap ht))
    (fun t ht => hwdiff _ (hmap ht))
    he₁bound he₂bound hediff

/-- A two-input error bound controls the difference of the two centered
integrands at every point of the normalized vertical segment. -/
theorem abs_centered_weightedDiagonalMean_sub_segment_sub_le
    {a b M D : ℝ} {w₁ w₂ f₁ f₂ : ℝ × ℝ → ℝ}
    {Gdiff : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hD : 0 ≤ D)
    (hjetdiff : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt (f₁ - f₂) (Gdiff p) (closedCoordTriangle a b) p)
    (hvertical : ∀ p ∈ closedCoordTriangle a b, |Gdiff p (0, 1)| ≤ D)
    {u v t : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hH : |weightedDiagonalError w₁ f₁ (u, v) -
      weightedDiagonalError w₂ f₂ (u, v)| ≤ M * (v - u) * D) :
    |(f₁ (diagonalSegment (u, v) t) - weightedDiagonalMean w₁ f₁ (u, v)) -
      (f₂ (diagonalSegment (u, v) t) - weightedDiagonalMean w₂ f₂ (u, v))| ≤
      (1 + M) * (v - u) * D := by
  let s := u + t * (v - u)
  have hd : 0 ≤ v - u := sub_nonneg.mpr huv
  have hus : u ≤ s := by dsimp [s]; nlinarith [mul_nonneg ht.1 hd]
  have hsv : s ≤ v := by
    dsimp [s]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hd]
  have hfv := norm_sub_vertical_le_of_jet hjetdiff
    (fun z hz => by simpa only [Real.norm_eq_abs] using hvertical z hz)
    hu hus hsv hv
  have hfv' : |(f₁ - f₂) (u, s) - (f₁ - f₂) (u, v)| ≤
      D * (v - u) := by
    have hbound : D * (v - s) ≤ D * (v - u) :=
      mul_le_mul_of_nonneg_left (by linarith [hus]) hD
    have h := hfv.trans hbound
    simpa only [Real.norm_eq_abs, abs_sub_comm] using h
  have hid :
      (f₁ (diagonalSegment (u, v) t) - weightedDiagonalMean w₁ f₁ (u, v)) -
        (f₂ (diagonalSegment (u, v) t) - weightedDiagonalMean w₂ f₂ (u, v)) =
      ((f₁ - f₂) (u, s) - (f₁ - f₂) (u, v)) +
        (weightedDiagonalError w₁ f₁ (u, v) -
          weightedDiagonalError w₂ f₂ (u, v)) := by
    simp only [diagonalSegment, s, weightedDiagonalError, Pi.sub_apply]
    ring
  rw [hid]
  calc
    _ ≤ |(f₁ - f₂) (u, s) - (f₁ - f₂) (u, v)| +
        |weightedDiagonalError w₁ f₁ (u, v) -
          weightedDiagonalError w₂ f₂ (u, v)| := abs_add_le _ _
    _ ≤ D * (v - u) + M * (v - u) * D := add_le_add hfv' hH
    _ = (1 + M) * (v - u) * D := by ring

end intervalIntegral

end
