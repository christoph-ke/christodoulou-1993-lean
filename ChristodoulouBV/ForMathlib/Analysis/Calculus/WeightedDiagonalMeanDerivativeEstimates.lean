module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMeanEstimates
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# First derivative estimates for positive weighted diagonal means

The vertical derivative is controlled first in the triangle interior and then
on its boundary through the continuous closed-domain jet.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- The vertical derivative of a weighted diagonal error above the diagonal. -/
theorem hasDerivAt_weightedDiagonalError_vertical {a b c : ℝ} {w f : ℝ × ℝ → ℝ}
    {Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) {u v : ℝ} (hau : a < u) (huv : u < v) (hvb : v < b) :
    HasDerivAt (fun x => weightedDiagonalError w f (u, x))
      (Gf (u, v) (0, 1) -
        w (u, v) * weightedDiagonalError w f (u, v) /
          weightedDiagonalRadius w (u, v)) v := by
  have hp : (u, v) ∈ interior (closedCoordTriangle a b) := by
    rw [interior_closedCoordTriangle]
    exact ⟨hau, huv, hvb⟩
  have hpK : (u, v) ∈ closedCoordTriangle a b := interior_subset hp
  have hmaps : MapsTo (fun s : ℝ => (u, s)) (Icc u v)
      (closedCoordTriangle a b) := by
    intro s hs
    change a ≤ u ∧ u ≤ s ∧ s ≤ b
    exact ⟨hau.le, hs.1, hs.2.trans hvb.le⟩
  have hwi : IntervalIntegrable (fun s => w (u, s)) volume u v := by
    exact (hw.comp (continuous_const.prodMk continuous_id).continuousOn hmaps)
      |>.intervalIntegrable_of_Icc huv.le
  have hn : IntervalIntegrable (fun s => w (u, s) * f (u, s)) volume u v := by
    exact ((hw.mul hf).comp (continuous_const.prodMk continuous_id).continuousOn hmaps)
      |>.intervalIntegrable_of_Icc huv.le
  have hmapsOpen : MapsTo (fun s : ℝ => (u, s)) (Ioo u b)
      (closedCoordTriangle a b) := by
    intro s hs
    change a ≤ u ∧ u ≤ s ∧ s ≤ b
    exact ⟨hau.le, hs.1.le, hs.2.le⟩
  have hwOpen : ContinuousOn (fun s => w (u, s)) (Ioo u b) :=
    hw.comp (continuous_const.prodMk continuous_id).continuousOn hmapsOpen
  have hnOpen : ContinuousOn (fun s => w (u, s) * f (u, s)) (Ioo u b) :=
    (hw.mul hf).comp (continuous_const.prodMk continuous_id).continuousOn hmapsOpen
  have hvi : v ∈ Ioo u b := ⟨huv, hvb⟩
  have hwat : ContinuousAt (fun s => w (u, s)) v :=
    (hwOpen v hvi).continuousAt (isOpen_Ioo.mem_nhds hvi)
  have hnat : ContinuousAt (fun s => w (u, s) * f (u, s)) v :=
    (hnOpen v hvi).continuousAt (isOpen_Ioo.mem_nhds hvi)
  have hwm : StronglyMeasurableAtFilter (fun s => w (u, s)) (𝓝 v) volume :=
    hwOpen.stronglyMeasurableAtFilter isOpen_Ioo v hvi
  have hnm : StronglyMeasurableAtFilter (fun s => w (u, s) * f (u, s)) (𝓝 v) volume :=
    hnOpen.stronglyMeasurableAtFilter isOpen_Ioo v hvi
  have hR := integral_hasDerivAt_right hwi hwm hwat
  have hN := integral_hasDerivAt_right hn hnm hnat
  have hF : HasDerivAt (fun x => f (u, x)) (Gf (u, v) (0, 1)) v := by
    have hfp : HasFDerivAt f (Gf (u, v)) (u, v) := by
      rw [← hderivf (u, v) hp]
      exact (hdf (u, v) hp).differentiableAt (isOpen_interior.mem_nhds hp) |>.hasFDerivAt
    have hpair : HasDerivAt (fun x : ℝ => (u, x)) (0, 1) v :=
      (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
    simpa only [Function.comp_def] using hfp.comp_hasDerivAt v hpair
  have hr : 0 < weightedDiagonalRadius w (u, v) :=
    weightedDiagonalRadius_pos hw hweight hc hau.le huv hvb.le
  have hR' : 0 < ∫ s in u..v, w (u, s) := hr
  have hderiv := hF.sub (hN.div hR hR'.ne')
  have heq : (fun x => weightedDiagonalError w f (u, x)) =ᶠ[𝓝 v]
      (fun x => f (u, x) -
        (∫ s in u..x, w (u, s) * f (u, s)) /
          (∫ s in u..x, w (u, s))) := by
    filter_upwards [Ioi_mem_nhds huv] with x hx
    simp only [weightedDiagonalError]
    rw [weightedDiagonalMean_eq_div (ne_of_lt hx)]
    rfl
  have hcoeff : Gf (u, v) (0, 1) -
      (w (u, v) * f (u, v) * (∫ s in u..v, w (u, s)) -
        (∫ s in u..v, w (u, s) * f (u, s)) * w (u, v)) /
        (∫ s in u..v, w (u, s)) ^ 2 =
      Gf (u, v) (0, 1) -
        w (u, v) * weightedDiagonalError w f (u, v) /
          weightedDiagonalRadius w (u, v) := by
    rw [weightedDiagonalError, weightedDiagonalMean_eq_div (ne_of_lt huv)]
    dsimp [weightedDiagonalRadius, weightedDiagonalNumerator]
    field_simp [hR'.ne']
  exact hcoeff ▸ hderiv.congr_of_eventuallyEq heq

/-- The vertical derivative obeys the exact box bound above the diagonal. -/
theorem abs_deriv_weightedDiagonalError_vertical_le {a b c C B : ℝ} {w f : ℝ × ℝ → ℝ}
    {Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hjet : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt f (Gf p) (closedCoordTriangle a b) p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p ∧ w p ≤ C)
    (hvertical : ∀ p ∈ closedCoordTriangle a b, |Gf p (0, 1)| ≤ B)
    (hc : 0 < c) (hB : 0 ≤ B)
    {u v : ℝ} (hau : a < u) (huv : u < v) (hvb : v < b) :
    |deriv (fun x => weightedDiagonalError w f (u, x)) v| ≤
      B + C * B / c := by
  have hderiv := (hasDerivAt_weightedDiagonalError_vertical hw hf hdf hderivf
    (fun p hp => (hweight p hp).1) hc hau huv hvb).deriv
  rw [hderiv]
  have hH := abs_weightedDiagonalError_le_of_jet hw hf
    (fun p hp => (hweight p hp).1) hc hB hjet
    (fun p hp => by simpa only [Real.norm_eq_abs] using hvertical p hp)
    hau.le huv.le hvb.le
  have hr : c * (v - u) ≤ weightedDiagonalRadius w (u, v) :=
    mul_sub_le_weightedDiagonalRadius hw (fun p hp => (hweight p hp).1)
      hau.le huv.le hvb.le
  have hd : 0 < v - u := sub_pos.mpr huv
  have hrpos : 0 < weightedDiagonalRadius w (u, v) :=
    (mul_pos hc hd).trans_le hr
  have hp : (u, v) ∈ closedCoordTriangle a b := by
    change a ≤ u ∧ u ≤ v ∧ v ≤ b
    exact ⟨hau.le, huv.le, hvb.le⟩
  have hwpos : 0 ≤ w (u, v) := hc.le.trans (hweight (u, v) hp).1
  have hC : 0 ≤ C := hwpos.trans (hweight (u, v) hp).2
  have hratio : |weightedDiagonalError w f (u, v)| /
      weightedDiagonalRadius w (u, v) ≤ B / c := by
    calc
      |weightedDiagonalError w f (u, v)| /
          weightedDiagonalRadius w (u, v) ≤
        (B * (v - u)) / weightedDiagonalRadius w (u, v) := by gcongr
      _ ≤ (B * (v - u)) / (c * (v - u)) :=
        div_le_div_of_nonneg_left (mul_nonneg hB hd.le) (mul_pos hc hd) hr
      _ = B / c := by field_simp
  have hterm : |w (u, v) * weightedDiagonalError w f (u, v) /
      weightedDiagonalRadius w (u, v)| ≤ C * B / c := by
    rw [abs_div, abs_mul, abs_of_pos hrpos, abs_of_nonneg hwpos]
    calc
      w (u, v) * |weightedDiagonalError w f (u, v)| /
          weightedDiagonalRadius w (u, v) =
        w (u, v) * (|weightedDiagonalError w f (u, v)| /
          weightedDiagonalRadius w (u, v)) := by ring
      _ ≤ C * (B / c) :=
        mul_le_mul (hweight (u, v) hp).2 hratio
          (div_nonneg (abs_nonneg _) hrpos.le) hC
      _ = C * B / c := by ring
  calc
    |Gf (u, v) (0, 1) -
        w (u, v) * weightedDiagonalError w f (u, v) /
          weightedDiagonalRadius w (u, v)| ≤
      |Gf (u, v) (0, 1)| +
        |w (u, v) * weightedDiagonalError w f (u, v) /
          weightedDiagonalRadius w (u, v)| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              abs_sub_le (Gf (u, v) (0, 1)) 0
                (w (u, v) * weightedDiagonalError w f (u, v) /
                  weightedDiagonalRadius w (u, v))
    _ ≤ B + C * B / c := add_le_add (hvertical _ hp) hterm

/-- The vertical first jet obeys the exact box bound on the closed triangle. -/
theorem abs_fderivWithin_weightedDiagonalError_vertical_le {a b c C B : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p ∧ w p ≤ C)
    (hvertical : ∀ p ∈ closedCoordTriangle a b, |Gf p (0, 1)| ≤ B)
    (hc : 0 < c) (hB : 0 ≤ B) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) :
    |(fderivWithin ℝ (weightedDiagonalError w f)
      (closedCoordTriangle a b) p) (0, 1)| ≤ B + C * B / c := by
  let K := closedCoordTriangle a b
  have hC1 := contDiffOn_weightedDiagonalError hab hw hf hGw hGf
    hdw hdf hderivw hderivf (fun z hz => (hweight z hz).1) hc
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hcont : ContinuousOn
      (fun z => |(fderivWithin ℝ (weightedDiagonalError w f) K z) (0, 1)|) K := by
    have h := ((hC1.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      (show ContinuousOn (fun _ : ℝ × ℝ => ((0 : ℝ), (1 : ℝ))) K from
        continuousOn_const)).norm
    simpa only [Real.norm_eq_abs] using h
  have hjet : ∀ z ∈ K, HasFDerivWithinAt f (Gf z) K z := by
    intro z hz
    exact (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
      (isClosed_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      hf hGf hdf hderivf hz
  have hopen : ∀ z ∈ interior K,
      |(fderivWithin ℝ (weightedDiagonalError w f) K z) (0, 1)| ≤
        B + C * B / c := by
    rintro ⟨u, v⟩ hz
    have hstrict : (u, v) ∈ openCoordTriangle a b := by
      rwa [interior_closedCoordTriangle] at hz
    have hparts : a < u ∧ u < v ∧ v < b := hstrict
    have hK : K ∈ 𝓝 (u, v) :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hz) interior_subset
    have hdiffAt : DifferentiableAt ℝ (weightedDiagonalError w f) (u, v) :=
      (hC1.differentiableOn (by norm_num) (u, v) (interior_subset hz)).differentiableAt hK
    have hwithin : fderivWithin ℝ (weightedDiagonalError w f) K (u, v) =
        fderiv ℝ (weightedDiagonalError w f) (u, v) :=
      fderivWithin_eq_fderiv (hunique (u, v) (interior_subset hz)) hdiffAt
    have hpair : HasDerivAt (fun x : ℝ => (u, x)) (0, 1) v :=
      (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
    have hverticalHas : HasDerivAt
        (fun x => weightedDiagonalError w f (u, x))
        (fderiv ℝ (weightedDiagonalError w f) (u, v) (0, 1)) v := by
      simpa only [Function.comp_def] using hdiffAt.hasFDerivAt.comp_hasDerivAt v hpair
    rw [hwithin, ← hverticalHas.deriv]
    exact abs_deriv_weightedDiagonalError_vertical_le hw hf hdf hderivf hjet hweight hvertical hc hB
      hparts.1 hparts.2.1 hparts.2.2
  have hclosure : closure (interior K) = K := by
    rw [interior_closedCoordTriangle, closure_openCoordTriangle hab]
  have hconst : ContinuousOn (fun _ : ℝ × ℝ => B + C * B / c)
      (closure (interior K)) := continuousOn_const
  have hcont' : ContinuousOn
      (fun z => |(fderivWithin ℝ (weightedDiagonalError w f) K z) (0, 1)|)
      (closure (interior K)) := by
    rw [hclosure]
    exact hcont
  change p ∈ K at hp
  rw [← hclosure] at hp
  exact le_on_closure hopen hcont' hconst hp

/-- The two-input vertical derivative difference has the exact coefficient above the diagonal. -/
theorem abs_deriv_weightedDiagonalError_vertical_sub_le {a b c C B D : ℝ}
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
    (hwdiff : ∀ p ∈ closedCoordTriangle a b, |w₁ p - w₂ p| ≤ D)
    (hvertical₁ : ∀ p ∈ closedCoordTriangle a b, |G₁ p (0, 1)| ≤ B)
    (hvertical₂ : ∀ p ∈ closedCoordTriangle a b, |G₂ p (0, 1)| ≤ B)
    (hverticalDiff : ∀ p ∈ closedCoordTriangle a b,
      |G₁ p (0, 1) - G₂ p (0, 1)| ≤ D)
    (hc : 0 < c) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {u v : ℝ} (hau : a < u) (huv : u < v) (hvb : v < b) :
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
  have hp : (u, v) ∈ closedCoordTriangle a b := by
    change a ≤ u ∧ u ≤ v ∧ v ≤ b
    exact ⟨hau.le, huv.le, hvb.le⟩
  have hd : 0 < d := sub_pos.mpr huv
  have hC : 0 ≤ C := (hc.le.trans (hweight₂ _ hp).1).trans (hweight₂ _ hp).2
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
  have hHdiff : |H₁ - H₂| ≤ M * d * D := by
    exact abs_weightedDiagonalError_sub_le_of_jets hc hD
      hw₁ hw₂ hf₁ hf₂
      (fun p hp => (hweight₁ p hp).1) hweight₂ hwdiff
      hjet₁ hjet₂ hvertical₁ hvertical₂ hverticalDiff
      hau.le huv.le hvb.le
  have hr₁ : c * d ≤ r₁ :=
    mul_sub_le_weightedDiagonalRadius hw₁
      (fun p hp => (hweight₁ p hp).1) hau.le huv.le hvb.le
  have hr₂ : c * d ≤ r₂ :=
    mul_sub_le_weightedDiagonalRadius hw₂
      (fun p hp => (hweight₂ p hp).1) hau.le huv.le hvb.le
  have hrdiff : |r₁ - r₂| ≤ d * D := by
    have h := abs_weightedDiagonalRadius_sub_le hw₁ hw₂ hwdiff
      hau.le huv.le hvb.le
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
        · exact mul_le_mul (hwdiff _ hp) hH₁ (abs_nonneg _) hD
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
      add_le_add (hverticalDiff _ hp) hq'
    _ = (1 + (B + C * ((B + C) / (2 * c) + C * B / (2 * c ^ 2))) / c +
      C * B / c ^ 2) * D := by dsimp [M]; ring

/-- An interior vertical-derivative difference bound extends to the closed triangle. -/
theorem abs_fderivWithin_vertical_sub_le_of_interior_deriv {a b D : ℝ} (hab : a < b)
    {F₁ F₂ : ℝ × ℝ → ℝ}
    (hC1₁ : ContDiffOn ℝ 1 F₁ (closedCoordTriangle a b))
    (hC1₂ : ContDiffOn ℝ 1 F₂ (closedCoordTriangle a b))
    (hinterior : ∀ u v, a < u → u < v → v < b →
      |deriv (fun x => F₁ (u, x)) v - deriv (fun x => F₂ (u, x)) v| ≤ D)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |(fderivWithin ℝ F₁ (closedCoordTriangle a b) p) (0, 1) -
      (fderivWithin ℝ F₂ (closedCoordTriangle a b) p) (0, 1)| ≤ D := by
  let K := closedCoordTriangle a b
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hcont₁ : ContinuousOn
      (fun z => (fderivWithin ℝ F₁ K z) (0, 1)) K :=
    (hC1₁.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      (show ContinuousOn (fun _ : ℝ × ℝ => ((0 : ℝ), (1 : ℝ))) K from
        continuousOn_const)
  have hcont₂ : ContinuousOn
      (fun z => (fderivWithin ℝ F₂ K z) (0, 1)) K :=
    (hC1₂.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      (show ContinuousOn (fun _ : ℝ × ℝ => ((0 : ℝ), (1 : ℝ))) K from
        continuousOn_const)
  have hcont : ContinuousOn (fun z =>
      |(fderivWithin ℝ F₁ K z) (0, 1) -
        (fderivWithin ℝ F₂ K z) (0, 1)|) K :=
    (hcont₁.sub hcont₂).abs
  have hinside (F : ℝ × ℝ → ℝ) (hC1 : ContDiffOn ℝ 1 F K)
      {u v : ℝ} (hstrict : (u, v) ∈ interior K) :
      (fderivWithin ℝ F K (u, v)) (0, 1) = deriv (fun x => F (u, x)) v := by
    have hK : K ∈ 𝓝 (u, v) :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hstrict) interior_subset
    have hdiffAt : DifferentiableAt ℝ F (u, v) :=
      (hC1.differentiableOn (by norm_num) (u, v) (interior_subset hstrict))
        |>.differentiableAt hK
    have hwithin : fderivWithin ℝ F K (u, v) = fderiv ℝ F (u, v) :=
      fderivWithin_eq_fderiv (hunique (u, v) (interior_subset hstrict)) hdiffAt
    have hpair : HasDerivAt (fun x : ℝ => (u, x)) (0, 1) v :=
      (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
    have hverticalHas : HasDerivAt (fun x => F (u, x))
        (fderiv ℝ F (u, v) (0, 1)) v := by
      simpa only [Function.comp_def] using hdiffAt.hasFDerivAt.comp_hasDerivAt v hpair
    rw [hwithin]
    exact hverticalHas.deriv.symm
  have hopen : ∀ z ∈ interior K,
      |(fderivWithin ℝ F₁ K z) (0, 1) -
        (fderivWithin ℝ F₂ K z) (0, 1)| ≤ D := by
    rintro ⟨u, v⟩ hz
    have hstrict : (u, v) ∈ openCoordTriangle a b := by
      rwa [interior_closedCoordTriangle] at hz
    have hparts : a < u ∧ u < v ∧ v < b := hstrict
    rw [hinside F₁ hC1₁ hz, hinside F₂ hC1₂ hz]
    exact hinterior u v hparts.1 hparts.2.1 hparts.2.2
  have hclosure : closure (interior K) = K := by
    rw [interior_closedCoordTriangle, closure_openCoordTriangle hab]
  have hcont' : ContinuousOn (fun z =>
      |(fderivWithin ℝ F₁ K z) (0, 1) -
        (fderivWithin ℝ F₂ K z) (0, 1)|) (closure (interior K)) := by
    rw [hclosure]
    exact hcont
  have hconst : ContinuousOn (fun _ : ℝ × ℝ => D)
      (closure (interior K)) := continuousOn_const
  change p ∈ K at hp
  rw [← hclosure] at hp
  exact le_on_closure hopen hcont' hconst hp

/-- The exact two-input vertical first-jet difference bound holds on the entire closed triangle. -/
theorem abs_fderivWithin_weightedDiagonalError_vertical_sub_le {a b c C B D : ℝ} (hab : a < b)
    {w₁ w₂ f₁ f₂ : ℝ × ℝ → ℝ}
    {Gw₁ Gw₂ G₁ G₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw₁ : ContinuousOn w₁ (closedCoordTriangle a b))
    (hw₂ : ContinuousOn w₂ (closedCoordTriangle a b))
    (hf₁ : ContinuousOn f₁ (closedCoordTriangle a b))
    (hf₂ : ContinuousOn f₂ (closedCoordTriangle a b))
    (hGw₁ : ContinuousOn Gw₁ (closedCoordTriangle a b))
    (hGw₂ : ContinuousOn Gw₂ (closedCoordTriangle a b))
    (hG₁ : ContinuousOn G₁ (closedCoordTriangle a b))
    (hG₂ : ContinuousOn G₂ (closedCoordTriangle a b))
    (hdw₁ : DifferentiableOn ℝ w₁ (interior (closedCoordTriangle a b)))
    (hdw₂ : DifferentiableOn ℝ w₂ (interior (closedCoordTriangle a b)))
    (hdf₁ : DifferentiableOn ℝ f₁ (interior (closedCoordTriangle a b)))
    (hdf₂ : DifferentiableOn ℝ f₂ (interior (closedCoordTriangle a b)))
    (hderivw₁ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w₁ p = Gw₁ p)
    (hderivw₂ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w₂ p = Gw₂ p)
    (hderiv₁ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f₁ p = G₁ p)
    (hderiv₂ : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f₂ p = G₂ p)
    (hweight₁ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₁ p ∧ w₁ p ≤ C)
    (hweight₂ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₂ p ∧ w₂ p ≤ C)
    (hwdiff : ∀ p ∈ closedCoordTriangle a b, |w₁ p - w₂ p| ≤ D)
    (hvertical₁ : ∀ p ∈ closedCoordTriangle a b, |G₁ p (0, 1)| ≤ B)
    (hvertical₂ : ∀ p ∈ closedCoordTriangle a b, |G₂ p (0, 1)| ≤ B)
    (hverticalDiff : ∀ p ∈ closedCoordTriangle a b,
      |G₁ p (0, 1) - G₂ p (0, 1)| ≤ D)
    (hc : 0 < c) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |(fderivWithin ℝ (weightedDiagonalError w₁ f₁) (closedCoordTriangle a b) p) (0, 1) -
      (fderivWithin ℝ (weightedDiagonalError w₂ f₂) (closedCoordTriangle a b) p) (0, 1)| ≤
      (1 + (B + C * ((B + C) / (2 * c) + C * B / (2 * c ^ 2))) / c +
        C * B / c ^ 2) * D := by
  have hC1₁ := contDiffOn_weightedDiagonalError hab hw₁ hf₁ hGw₁ hG₁
    hdw₁ hdf₁ hderivw₁ hderiv₁ (fun z hz => (hweight₁ z hz).1) hc
  have hC1₂ := contDiffOn_weightedDiagonalError hab hw₂ hf₂ hGw₂ hG₂
    hdw₂ hdf₂ hderivw₂ hderiv₂ (fun z hz => (hweight₂ z hz).1) hc
  have hjet₁ : ∀ z ∈ closedCoordTriangle a b,
      HasFDerivWithinAt f₁ (G₁ z) (closedCoordTriangle a b) z := by
    intro z hz
    exact (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
      (isClosed_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      hf₁ hG₁ hdf₁ hderiv₁ hz
  have hjet₂ : ∀ z ∈ closedCoordTriangle a b,
      HasFDerivWithinAt f₂ (G₂ z) (closedCoordTriangle a b) z := by
    intro z hz
    exact (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
      (isClosed_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      hf₂ hG₂ hdf₂ hderiv₂ hz
  apply abs_fderivWithin_vertical_sub_le_of_interior_deriv hab hC1₁ hC1₂
  · intro u v hau huv hvb
    exact abs_deriv_weightedDiagonalError_vertical_sub_le hw₁ hw₂ hf₁ hf₂
      hdf₁ hdf₂ hderiv₁ hderiv₂ hjet₁ hjet₂ hweight₁ hweight₂
      hwdiff hvertical₁ hvertical₂ hverticalDiff hc hB hD hau huv hvb
  · exact hp

end intervalIntegral

end
