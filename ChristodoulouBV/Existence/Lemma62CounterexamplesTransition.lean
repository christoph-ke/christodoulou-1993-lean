module

public import ChristodoulouBV.Existence.Lemma62CounterexamplesHypotheses
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A smooth transition with zero weighted variation

For `s > 0`, `rise s` changes from zero to one in `[s,2s]`.
The smooth function `dip s` equals zero throughout that interval and equals
one outside `(s/2,3s)`. Thus its integration-by-parts primitive against
`rise s` is identically zero. This implements the moving-transition sketch
with a jump at the left endpoint of the closed variation interval.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

namespace ChristodoulouBV.Lemma62Counterexamples

/-- A smooth dip, with a plateau containing the transition interval. -/
noncomputable def dip (s x : ℝ) : ℝ :=
  1 - Real.smoothTransition (2 * x / s - 1) * Real.smoothTransition (6 - 2 * x / s)

/-- A smooth increasing transition in `[s,2s]`. -/
noncomputable def rise (s x : ℝ) : ℝ := Real.smoothTransition (x / s - 1)

theorem dip_smooth (s : ℝ) : ContDiff ℝ 1 (dip s) := by
  exact contDiff_const.sub
    ((Real.smoothTransition.contDiff.comp
      (((contDiff_const.mul contDiff_id).div_const s).sub contDiff_const)).mul
      (Real.smoothTransition.contDiff.comp
        (contDiff_const.sub ((contDiff_const.mul contDiff_id).div_const s))))

theorem rise_smooth (s : ℝ) : ContDiff ℝ 1 (rise s) := by
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.div_const s).sub contDiff_const)

theorem dip_eq_one_left {s x : ℝ} (hs : 0 < s) (hx : x < s / 2) : dip s x = 1 := by
  have h : 2 * x / s - 1 ≤ 0 := by
    have := (div_lt_iff₀ hs).2 (show 2 * x < 1 * s by linarith)
    linarith
  simp [dip, Real.smoothTransition.zero_of_nonpos h]

theorem dip_eq_one_right {s x : ℝ} (hs : 0 < s) (hx : 3 * s < x) : dip s x = 1 := by
  have h : 6 - 2 * x / s ≤ 0 := by
    have := (lt_div_iff₀ hs).2 (show 6 * s < 2 * x by linarith)
    linarith
  simp [dip, Real.smoothTransition.zero_of_nonpos h]

theorem dip_deriv_left {s x : ℝ} (hs : 0 < s) (hx : x < s / 2) : deriv (dip s) x = 0 := by
  have he : dip s =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) :=
    (gt_mem_nhds hx).mono fun t ht => dip_eq_one_left hs ht
  simpa using he.deriv_eq

theorem dip_deriv_right {s x : ℝ} (hs : 0 < s) (hx : 3 * s < x) : deriv (dip s) x = 0 := by
  have he : dip s =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) :=
    (lt_mem_nhds hx).mono fun t ht => dip_eq_one_right hs ht
  simpa using he.deriv_eq

theorem dip_eq_zero {s x : ℝ} (hs : 0 < s) (hlo : s ≤ x) (hhi : x ≤ 2 * s) :
    dip s x = 0 := by
  have h₁ : 1 ≤ 2 * x / s - 1 := by
    have := (le_div_iff₀ hs).2 (show 2 * s ≤ 2 * x by linarith)
    linarith
  have h₂ : 1 ≤ 6 - 2 * x / s := by
    have := (div_le_iff₀ hs).2 (show 2 * x ≤ 4 * s by linarith)
    linarith
  simp [dip, Real.smoothTransition.one_of_one_le h₁,
    Real.smoothTransition.one_of_one_le h₂]

theorem rise_eq_zero {s x : ℝ} (hs : 0 < s) (hx : x ≤ s) : rise s x = 0 := by
  have h : x / s - 1 ≤ 0 := by
    have := (div_le_iff₀ hs).2 (show x ≤ 1 * s by simpa using hx)
    linarith
  exact Real.smoothTransition.zero_of_nonpos h

theorem rise_eq_one {s x : ℝ} (hs : 0 < s) (hx : 2 * s ≤ x) : rise s x = 1 := by
  have h : 1 ≤ x / s - 1 := by
    have := (le_div_iff₀ hs).2 hx
    linarith
  exact Real.smoothTransition.one_of_one_le h

theorem rise_deriv_left {s x : ℝ} (hs : 0 < s) (hx : x < s) : deriv (rise s) x = 0 := by
  have he : rise s =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) :=
    (gt_mem_nhds hx).mono fun t ht => rise_eq_zero hs ht.le
  simpa using he.deriv_eq

theorem rise_deriv_right {s x : ℝ} (hs : 0 < s) (hx : 2 * s < x) : deriv (rise s) x = 0 := by
  have he : rise s =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) :=
    (lt_mem_nhds hx).mono fun t ht => rise_eq_one hs ht.le
  simpa using he.deriv_eq

theorem dip_mul_deriv_rise {s : ℝ} (hs : 0 < s) (x : ℝ) :
    dip s x * deriv (rise s) x = 0 := by
  rcases lt_or_ge x s with hx | hx
  · rw [rise_deriv_left hs hx, mul_zero]
  rcases le_or_gt x (2 * s) with hx' | hx'
  · rw [dip_eq_zero hs hx hx', zero_mul]
  · rw [rise_deriv_right hs hx', mul_zero]

theorem dip_primitive_zero {s : ℝ} (hs : 0 < s) :
    intervalIntegral.productPrimitive (dip s) (rise s) (deriv (dip s)) (fun _ => 0) =
      fun _ => 0 := by
  have hf := (dip_smooth s).differentiable (by norm_num)
  have hg := (rise_smooth s).differentiable (by norm_num)
  have hd (x : ℝ) : HasDerivAt (fun x => dip s x * rise s x)
      (rise s x * deriv (dip s) x) x := by
    convert (hf x).hasDerivAt.mul (hg x).hasDerivAt using 1
    rw [dip_mul_deriv_rise hs x]
    ring
  have hi : Continuous (fun x => rise s x * deriv (dip s) x) :=
    (rise_smooth s).continuous.mul ((dip_smooth s).continuous_deriv (by norm_num))
  funext x
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hi.intervalIntegrable 0 x)
  simp only [intervalIntegral.productPrimitive, add_zero]
  linarith

theorem dip_bound (s x : ℝ) : |dip s x| ≤ 1 := by
  have ha := Real.smoothTransition.nonneg (2 * x / s - 1)
  have hb := Real.smoothTransition.nonneg (6 - 2 * x / s)
  have hc := Real.smoothTransition.le_one (2 * x / s - 1)
  have hd := Real.smoothTransition.le_one (6 - 2 * x / s)
  rw [dip, abs_le]
  constructor <;> nlinarith [mul_nonneg ha hb]

theorem rise_monotone {s : ℝ} (hs : 0 < s) : Monotone (rise s) := by
  intro x z hxz
  exact Real.smoothTransition.monotone (sub_le_sub_right (div_le_div_of_nonneg_right hxz hs.le) _)

theorem rise_variation_le {s : ℝ} (hs : 0 < s) :
    eVariationOn (rise s) (Icc (0 : ℝ) 1) ≤ 1 := by
  have h := (rise_monotone hs).monotoneOn (Icc (0 : ℝ) 1)
  have he := h.eVariationOn_eq (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  rw [inter_self] at he
  rw [he]
  exact (ENNReal.ofReal_le_ofReal (sub_le_self _ (Real.smoothTransition.nonneg _))).trans
    (by simpa [rise] using ENNReal.ofReal_le_ofReal (Real.smoothTransition.le_one (1 / s - 1)))

end ChristodoulouBV.Lemma62Counterexamples
