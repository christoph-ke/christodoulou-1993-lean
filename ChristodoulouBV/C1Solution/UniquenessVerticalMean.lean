module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMeanEstimates
import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMeanDerivativeEstimates
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Weighted diagonal comparison on one outgoing ray

The unrestricted uniqueness seminorm is taken at a fixed outgoing
coordinate. These estimates use differences only on that ray; no incoming
jet difference is assumed.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- At an interior point of a closed coordinate triangle, the relative
outgoing jet is the ordinary derivative along the outgoing ray. -/
theorem fderivWithin_vertical_eq_deriv_on_ray
    {a b : ℝ} (hab : a < b)
    {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle a b))
    {u v : ℝ} (hau : a < u) (huv : u < v) (hvb : v < b) :
    (fderivWithin ℝ F (closedCoordTriangle a b) (u, v)) (0, 1) =
      deriv (fun x => F (u, x)) v := by
  let K := closedCoordTriangle a b
  have hstrict : (u, v) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact ⟨hau, huv, hvb⟩
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hab)
  have hK : K ∈ 𝓝 (u, v) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hstrict) interior_subset
  have hdiffAt : DifferentiableAt ℝ F (u, v) :=
    (hF.differentiableOn (by norm_num) (u, v) (interior_subset hstrict))
      |>.differentiableAt hK
  have hwithin : fderivWithin ℝ F K (u, v) = fderiv ℝ F (u, v) :=
    fderivWithin_eq_fderiv (hunique (u, v) (interior_subset hstrict)) hdiffAt
  have hpair : HasDerivAt (fun x : ℝ => (u, x)) (0, 1) v :=
    (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
  have hverticalHas : HasDerivAt (fun x => F (u, x))
      (fderiv ℝ F (u, v) (0, 1)) v := by
    simpa only [Function.comp_def] using
      hdiffAt.hasFDerivAt.comp_hasDerivAt v hpair
  rw [hwithin]
  exact hverticalHas.deriv.symm

/-- A relative jet bound restricted to one vertical segment gives a
Lipschitz bound on that segment. -/
theorem norm_sub_vertical_le_of_jet_on_ray
    {a b D : ℝ} {f : ℝ × ℝ → ℝ}
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hjet : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt f (G p) (closedCoordTriangle a b) p)
    {u s v : ℝ} (hu : a ≤ u) (hus : u ≤ s) (hsv : s ≤ v) (hv : v ≤ b)
    (hbound : ∀ t ∈ Icc s v, ‖G (u, t) (0, 1)‖ ≤ D) :
    ‖f (u, v) - f (u, s)‖ ≤ D * (v - s) := by
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc s v)
      (closedCoordTriangle a b) := by
    intro t ht
    exact ⟨hu, hus.trans ht.1, ht.2.trans hv⟩
  have hderiv : ∀ t ∈ Icc s v,
      HasDerivWithinAt (fun t : ℝ => f (u, t))
        (G (u, t) (0, 1)) (Icc s v) t := by
    intro t ht
    have hpair : HasDerivAt (fun x : ℝ => (u, x)) (0, 1) t :=
      (hasDerivAt_const t u).prodMk (hasDerivAt_id' t)
    simpa only [Function.comp_def] using
      (hjet (u, t) (hmap ht)).comp_hasDerivWithinAt t
        hpair.hasDerivWithinAt hmap
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (convex_Icc s v) ⟨le_rfl, hsv⟩ ⟨hsv, le_rfl⟩
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hsv)] using h

/-- Radius differences on an outgoing ray need only the weight difference
on that same ray. -/
theorem abs_weightedDiagonalRadius_sub_le_on_ray
    {a b D : ℝ} {w₁ w₂ : ℝ × ℝ → ℝ}
    (hw₁ : ContinuousOn w₁ (closedCoordTriangle a b))
    (hw₂ : ContinuousOn w₂ (closedCoordTriangle a b))
    {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b)
    (hwdiff : ∀ t ∈ Icc u v, |w₁ (u, t) - w₂ (u, t)| ≤ D) :
    |weightedDiagonalRadius w₁ (u, v) -
      weightedDiagonalRadius w₂ (u, v)| ≤ D * (v - u) := by
  rw [weightedDiagonalRadius_eq_mul_integral,
    weightedDiagonalRadius_eq_mul_integral]
  have hp : (u, v) ∈ closedCoordTriangle a b := ⟨hu, huv, hv⟩
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
        (Icc (0 : ℝ) 1) := hw₁.comp hcontseg hseg
    have hcont₂ : ContinuousOn (fun t => w₂ (diagonalSegment (u, v) t))
        (Icc (0 : ℝ) 1) := hw₂.comp hcontseg hseg
    rw [← intervalIntegral.integral_sub
      (hcont₁.intervalIntegrable_of_Icc (by norm_num))
      (hcont₂.intervalIntegrable_of_Icc (by norm_num))]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := D)
      (f := fun t => w₁ (diagonalSegment (u, v) t) -
        w₂ (diagonalSegment (u, v) t)) (by
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := by
          rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
          exact ⟨ht.1.le, ht.2⟩
        have htu : u ≤ u + t * (v - u) := by
          have h := mul_nonneg ht'.1 (sub_nonneg.mpr huv)
          linarith
        have htv : u + t * (v - u) ≤ v := by
          have h := mul_nonneg (sub_nonneg.mpr ht'.2)
            (sub_nonneg.mpr huv)
          nlinarith
        simpa only [diagonalSegment, Real.norm_eq_abs] using
          hwdiff (u + t * (v - u)) ⟨htu, htv⟩)
    simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h
  rw [← mul_sub, abs_mul, abs_of_nonneg (sub_nonneg.mpr huv)]
  calc
    (v - u) * |(∫ t in (0 : ℝ)..1, w₁ (diagonalSegment (u, v) t)) -
      (∫ t in (0 : ℝ)..1, w₂ (diagonalSegment (u, v) t))| ≤
        (v - u) * D := mul_le_mul_of_nonneg_left hdiff (sub_nonneg.mpr huv)
    _ = D * (v - u) := mul_comm _ _

/-- The weighted diagonal error difference at `(u,v)` needs value and
outgoing-jet differences only along the one ray from `(u,u)` to `(u,v)`. -/
theorem abs_weightedDiagonalError_sub_le_on_ray
    {a b c C B D : ℝ} {w₁ w₂ f₁ f₂ : ℝ × ℝ → ℝ}
    {G₁ G₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hc : 0 < c) (hD : 0 ≤ D)
    (hw₁ : ContinuousOn w₁ (closedCoordTriangle a b))
    (hw₂ : ContinuousOn w₂ (closedCoordTriangle a b))
    (hf₁ : ContinuousOn f₁ (closedCoordTriangle a b))
    (hf₂ : ContinuousOn f₂ (closedCoordTriangle a b))
    (hweight₁ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₁ p)
    (hweight₂ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₂ p ∧ w₂ p ≤ C)
    (hjet₁ : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt f₁ (G₁ p) (closedCoordTriangle a b) p)
    (hjet₂ : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt f₂ (G₂ p) (closedCoordTriangle a b) p)
    (hvertical₁ : ∀ p ∈ closedCoordTriangle a b, |G₁ p (0, 1)| ≤ B)
    (hvertical₂ : ∀ p ∈ closedCoordTriangle a b, |G₂ p (0, 1)| ≤ B)
    {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b)
    (hwdiff : ∀ t ∈ Icc u v, |w₁ (u, t) - w₂ (u, t)| ≤ D)
    (hverticalDiff : ∀ t ∈ Icc u v,
      |G₁ (u, t) (0, 1) - G₂ (u, t) (0, 1)| ≤ D) :
    |weightedDiagonalError w₁ f₁ (u, v) -
      weightedDiagonalError w₂ f₂ (u, v)| ≤
      ((B + C) / (2 * c) + C * B / (2 * c ^ 2)) * (v - u) * D := by
  let p : ℝ × ℝ := (u, v)
  let s (t : ℝ) : ℝ := u + t * (v - u)
  let e₁ (t : ℝ) : ℝ := f₁ p - f₁ (diagonalSegment p t)
  let e₂ (t : ℝ) : ℝ := f₂ p - f₂ (diagonalSegment p t)
  have hp : p ∈ closedCoordTriangle a b := ⟨hu, huv, hv⟩
  have hseg : ContinuousOn (fun t : ℝ => diagonalSegment p t) (Icc 0 1) := by
    unfold diagonalSegment
    fun_prop
  have hmap : MapsTo (fun t : ℝ => diagonalSegment p t)
      (Icc (0 : ℝ) 1) (closedCoordTriangle a b) :=
    fun t ht => diagonalSegment_mem_closedCoordTriangle hp ht
  have he₁ : ContinuousOn e₁ (Icc (0 : ℝ) 1) :=
    continuousOn_const.sub (hf₁.comp hseg hmap)
  have he₂ : ContinuousOn e₂ (Icc (0 : ℝ) 1) :=
    continuousOn_const.sub (hf₂.comp hseg hmap)
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
      (fun q hq => by simpa only [Real.norm_eq_abs] using hvertical₁ q hq)
      hu hus hsv hv
    rw [← hseg_eq t] at h
    simpa only [e₁, p, Real.norm_eq_abs, hdist, mul_assoc] using h
  have he₂bound : ∀ t ∈ Icc (0 : ℝ) 1,
      |e₂ t| ≤ B * (v - u) * (1 - t) := by
    intro t ht
    obtain ⟨hus, hsv, hdist⟩ := hlocation t ht
    have h := norm_sub_vertical_le_of_jet hjet₂
      (fun q hq => by simpa only [Real.norm_eq_abs] using hvertical₂ q hq)
      hu hus hsv hv
    rw [← hseg_eq t] at h
    simpa only [e₂, p, Real.norm_eq_abs, hdist, mul_assoc] using h
  let Gdiff : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun q => G₁ q - G₂ q
  have hjetdiff : ∀ q ∈ closedCoordTriangle a b,
      HasFDerivWithinAt (f₁ - f₂) (Gdiff q)
        (closedCoordTriangle a b) q := by
    intro q hq
    exact (hjet₁ q hq).sub (hjet₂ q hq)
  have hediff : ∀ t ∈ Icc (0 : ℝ) 1,
      |e₁ t - e₂ t| ≤ D * (v - u) * (1 - t) := by
    intro t ht
    obtain ⟨hus, hsv, hdist⟩ := hlocation t ht
    have hbound : ∀ x ∈ Icc (s t) v,
        ‖Gdiff (u, x) (0, 1)‖ ≤ D := by
      intro x hx
      simpa only [Gdiff, sub_apply, Real.norm_eq_abs] using
        hverticalDiff x ⟨hus.trans hx.1, hx.2⟩
    have h := norm_sub_vertical_le_of_jet_on_ray hjetdiff
      hu hus hsv hv hbound
    rw [← hseg_eq t] at h
    have hid : e₁ t - e₂ t =
        (f₁ - f₂) p - (f₁ - f₂) (diagonalSegment p t) := by
      dsimp [e₁, e₂]
      ring
    rw [hid]
    simpa only [p, Pi.sub_apply, Real.norm_eq_abs, hdist, mul_assoc] using h
  have hmean₁ := weightedDiagonalError_eq_normalized_integral hw₁ hf₁
    hweight₁ hc hp
  have hmean₂ := weightedDiagonalError_eq_normalized_integral hw₂ hf₂
    (fun q hq => (hweight₂ q hq).1) hc hp
  rw [hmean₁, hmean₂]
  exact abs_weighted_integral_quotient_sub_le hc hD
    (hw₁.comp hseg hmap) (hw₂.comp hseg hmap) he₁ he₂
    (fun t ht => hweight₁ _ (hmap ht))
    (fun t ht => hweight₂ _ (hmap ht))
    (fun t ht => by
      obtain ⟨hus, hsv, _⟩ := hlocation t ht
      simpa only [hseg_eq] using hwdiff (s t) ⟨hus, hsv⟩)
    he₁bound he₂bound hediff

/-- In the triangle interior, the outgoing derivative comparison of the
weighted error uses only the same fixed ray differences. -/
theorem abs_deriv_weightedDiagonalError_vertical_sub_le_on_ray
    {a b c C B D : ℝ}
    {w₁ w₂ f₁ f₂ : ℝ × ℝ → ℝ}
    {G₁ G₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw₁ : ContinuousOn w₁ (closedCoordTriangle a b))
    (hw₂ : ContinuousOn w₂ (closedCoordTriangle a b))
    (hf₁ : ContinuousOn f₁ (closedCoordTriangle a b))
    (hf₂ : ContinuousOn f₂ (closedCoordTriangle a b))
    (hdf₁ : DifferentiableOn ℝ f₁ (interior (closedCoordTriangle a b)))
    (hdf₂ : DifferentiableOn ℝ f₂ (interior (closedCoordTriangle a b)))
    (hderiv₁ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f₁ p = G₁ p)
    (hderiv₂ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f₂ p = G₂ p)
    (hjet₁ : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt f₁ (G₁ p) (closedCoordTriangle a b) p)
    (hjet₂ : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt f₂ (G₂ p) (closedCoordTriangle a b) p)
    (hweight₁ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₁ p ∧ w₁ p ≤ C)
    (hweight₂ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₂ p ∧ w₂ p ≤ C)
    (hvertical₁ : ∀ p ∈ closedCoordTriangle a b, |G₁ p (0, 1)| ≤ B)
    (hvertical₂ : ∀ p ∈ closedCoordTriangle a b, |G₂ p (0, 1)| ≤ B)
    (hc : 0 < c) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {u v : ℝ} (hau : a < u) (huv : u < v) (hvb : v < b)
    (hwdiff : ∀ t ∈ Icc u v, |w₁ (u, t) - w₂ (u, t)| ≤ D)
    (hverticalDiff : ∀ t ∈ Icc u v,
      |G₁ (u, t) (0, 1) - G₂ (u, t) (0, 1)| ≤ D) :
    |deriv (fun x => weightedDiagonalError w₁ f₁ (u, x)) v -
      deriv (fun x => weightedDiagonalError w₂ f₂ (u, x)) v| ≤
      (1 + (B + C * ((B + C) / (2 * c) + C * B / (2 * c ^ 2))) / c +
        C * B / c ^ 2) * D := by
  let d := v - u
  let M := (B + C) / (2 * c) + C * B / (2 * c ^ 2)
  let H₁ := weightedDiagonalError w₁ f₁ (u, v)
  let H₂ := weightedDiagonalError w₂ f₂ (u, v)
  let r₁ := weightedDiagonalRadius w₁ (u, v)
  let r₂ := weightedDiagonalRadius w₂ (u, v)
  have hp : (u, v) ∈ closedCoordTriangle a b :=
    ⟨hau.le, huv.le, hvb.le⟩
  have hd : 0 < d := sub_pos.mpr huv
  have hC : 0 ≤ C := (hc.le.trans (hweight₂ _ hp).1).trans
    (hweight₂ _ hp).2
  have hH₁ : |H₁| ≤ B * d :=
    abs_weightedDiagonalError_le_of_jet hw₁ hf₁
      (fun p hp => (hweight₁ p hp).1) hc hB hjet₁
      (fun p hp => by simpa only [Real.norm_eq_abs] using hvertical₁ p hp)
      hau.le huv.le hvb.le
  have hH₂ : |H₂| ≤ B * d :=
    abs_weightedDiagonalError_le_of_jet hw₂ hf₂
      (fun p hp => (hweight₂ p hp).1) hc hB hjet₂
      (fun p hp => by simpa only [Real.norm_eq_abs] using hvertical₂ p hp)
      hau.le huv.le hvb.le
  have hHdiff : |H₁ - H₂| ≤ M * d * D :=
    abs_weightedDiagonalError_sub_le_on_ray hc hD
      hw₁ hw₂ hf₁ hf₂ (fun p hp => (hweight₁ p hp).1)
      hweight₂ hjet₁ hjet₂ hvertical₁ hvertical₂
      hau.le huv.le hvb.le hwdiff hverticalDiff
  have hr₁ : c * d ≤ r₁ :=
    mul_sub_le_weightedDiagonalRadius hw₁
      (fun p hp => (hweight₁ p hp).1) hau.le huv.le hvb.le
  have hr₂ : c * d ≤ r₂ :=
    mul_sub_le_weightedDiagonalRadius hw₂
      (fun p hp => (hweight₂ p hp).1) hau.le huv.le hvb.le
  have hrdiff : |r₁ - r₂| ≤ d * D := by
    have h := abs_weightedDiagonalRadius_sub_le_on_ray hw₁ hw₂
      hau.le huv.le hvb.le hwdiff
    simpa only [d, mul_comm] using h
  have hnum₂ : |w₂ (u, v) * H₂| ≤ C * B * d := by
    rw [abs_mul, abs_of_nonneg (hc.le.trans (hweight₂ _ hp).1)]
    calc
      w₂ (u, v) * |H₂| ≤ C * (B * d) :=
        mul_le_mul (hweight₂ _ hp).2 hH₂ (abs_nonneg _) hC
      _ = C * B * d := by ring
  have hnumdiff : |w₁ (u, v) * H₁ - w₂ (u, v) * H₂| ≤
      (B + C * M) * d * D := by
    have hid : w₁ (u, v) * H₁ - w₂ (u, v) * H₂ =
        (w₁ (u, v) - w₂ (u, v)) * H₁ + w₂ (u, v) * (H₁ - H₂) := by ring
    rw [hid]
    calc
      |(w₁ (u, v) - w₂ (u, v)) * H₁ + w₂ (u, v) * (H₁ - H₂)| ≤
          |w₁ (u, v) - w₂ (u, v)| * |H₁| +
            |w₂ (u, v)| * |H₁ - H₂| := by
              simpa only [abs_mul] using abs_add_le
                ((w₁ (u, v) - w₂ (u, v)) * H₁)
                (w₂ (u, v) * (H₁ - H₂))
      _ ≤ D * (B * d) + C * (M * d * D) := by
        apply add_le_add
        · exact mul_le_mul (hwdiff v ⟨huv.le, le_rfl⟩) hH₁
            (abs_nonneg _) hD
        · rw [abs_of_nonneg (hc.le.trans (hweight₂ _ hp).1)]
          exact mul_le_mul (hweight₂ _ hp).2 hHdiff (abs_nonneg _) hC
      _ = (B + C * M) * d * D := by ring
  have hq := abs_div_sub_div_le (mul_pos hc hd) hr₁ hr₂
    hnumdiff hrdiff hnum₂
  have hq' : |w₁ (u, v) * H₁ / r₁ - w₂ (u, v) * H₂ / r₂| ≤
      ((B + C * M) / c + C * B / c ^ 2) * D := by
    calc
      |w₁ (u, v) * H₁ / r₁ - w₂ (u, v) * H₂ / r₂| ≤
          ((B + C * M) * d * D) / (c * d) +
            (C * B * d) * (d * D) / (c * d) ^ 2 := hq
      _ = ((B + C * M) / c + C * B / c ^ 2) * D := by
        field_simp [hc.ne', hd.ne']
  rw [(hasDerivAt_weightedDiagonalError_vertical hw₁ hf₁ hdf₁ hderiv₁
    (fun p hp => (hweight₁ p hp).1) hc hau huv hvb).deriv,
    (hasDerivAt_weightedDiagonalError_vertical hw₂ hf₂ hdf₂ hderiv₂
    (fun p hp => (hweight₂ p hp).1) hc hau huv hvb).deriv]
  have htri : |(G₁ (u, v) (0, 1) - w₁ (u, v) * H₁ / r₁) -
      (G₂ (u, v) (0, 1) - w₂ (u, v) * H₂ / r₂)| ≤
      |G₁ (u, v) (0, 1) - G₂ (u, v) (0, 1)| +
      |w₁ (u, v) * H₁ / r₁ - w₂ (u, v) * H₂ / r₂| := by
    have hid : (G₁ (u, v) (0, 1) - w₁ (u, v) * H₁ / r₁) -
        (G₂ (u, v) (0, 1) - w₂ (u, v) * H₂ / r₂) =
        (G₁ (u, v) (0, 1) - G₂ (u, v) (0, 1)) -
          (w₁ (u, v) * H₁ / r₁ - w₂ (u, v) * H₂ / r₂) := by ring
    rw [hid]
    simpa only [sub_zero, zero_sub, abs_neg] using
      abs_sub_le (G₁ (u, v) (0, 1) - G₂ (u, v) (0, 1)) 0
        (w₁ (u, v) * H₁ / r₁ - w₂ (u, v) * H₂ / r₂)
  calc
    |(G₁ (u, v) (0, 1) - w₁ (u, v) * H₁ / r₁) -
        (G₂ (u, v) (0, 1) - w₂ (u, v) * H₂ / r₂)| ≤
      |G₁ (u, v) (0, 1) - G₂ (u, v) (0, 1)| +
        |w₁ (u, v) * H₁ / r₁ - w₂ (u, v) * H₂ / r₂| := htri
    _ ≤ D + ((B + C * M) / c + C * B / c ^ 2) * D :=
      add_le_add (hverticalDiff v ⟨huv.le, le_rfl⟩) hq'
    _ = (1 + (B + C * ((B + C) / (2 * c) + C * B / (2 * c ^ 2))) / c +
      C * B / c ^ 2) * D := by dsimp [M]; ring

end intervalIntegral

end
