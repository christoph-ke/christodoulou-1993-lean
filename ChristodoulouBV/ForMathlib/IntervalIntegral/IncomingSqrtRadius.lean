module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.MixedPartial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Incoming integration in a square-root radius coordinate

The integrable singularity `-r_u / √r` has an exact primitive whenever the
radius stays positive on the incoming segment.
-/

public section

open Set MeasureTheory
open scoped Interval

namespace intervalIntegral

/-- The square-root radius primitive on a positive incoming segment. -/
theorem integral_neg_deriv_div_sqrt_eq
    {a b : ℝ} (hab : a ≤ b) {R N : ℝ → ℝ}
    (hR : ContinuousOn R (Icc a b))
    (hN : ContinuousOn N (Icc a b))
    (hpos : ∀ s ∈ Icc a b, 0 < R s)
    (hD : ∀ s ∈ Ioo a b, HasDerivAt R (N s) s) :
    (∫ s in a..b, (-N s) / Real.sqrt (R s)) =
      2 * (Real.sqrt (R a) - Real.sqrt (R b)) := by
  let F : ℝ → ℝ := fun s => -2 * Real.sqrt (R s)
  let G : ℝ → ℝ := fun s => (-N s) / Real.sqrt (R s)
  have hF : ContinuousOn F (Icc a b) :=
    continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn hR)
  have hG : ContinuousOn G (Icc a b) :=
    hN.neg.div
      (Real.continuous_sqrt.comp_continuousOn hR)
      (fun s hs => ne_of_gt (Real.sqrt_pos.2 (hpos s hs)))
  have hGint : IntervalIntegrable G volume a b :=
    hG.intervalIntegrable_of_Icc hab
  have hderiv : ∀ s ∈ Ioo a b, HasDerivAt F (G s) s := by
    intro s hs
    have hp := hpos s ⟨hs.1.le, hs.2.le⟩
    have h := (Real.hasDerivAt_sqrt hp.ne').comp s (hD s hs)
    have h' := h.const_mul (-2)
    convert h' using 1
    · dsimp [F]
    · dsimp [G]
      field_simp [ne_of_gt (Real.sqrt_pos.2 hp)]
  have hFTC := intervalIntegral.integral_eq_sub_of_continuousOn_hasDerivAt
    hab hF hG hderiv
  dsimp [F, G] at hFTC ⊢
  linarith only [hFTC]

/-- The square-root radius integral is bounded by its initial radius. -/
theorem integral_neg_deriv_div_sqrt_le
    {a b : ℝ} (hab : a ≤ b) {R N : ℝ → ℝ}
    (hR : ContinuousOn R (Icc a b))
    (hN : ContinuousOn N (Icc a b))
    (hpos : ∀ s ∈ Icc a b, 0 < R s)
    (hD : ∀ s ∈ Ioo a b, HasDerivAt R (N s) s) :
    (∫ s in a..b, (-N s) / Real.sqrt (R s)) ≤
      2 * Real.sqrt (R a) := by
  rw [integral_neg_deriv_div_sqrt_eq hab hR hN hpos hD]
  have hb := Real.sqrt_nonneg (R b)
  linarith only [hb]

/-- A derivative controlled by the square-root radius loss stays uniformly
bounded all the way to a positive-radius endpoint of the incoming segment.
The comparison with `√R` avoids requiring an integral of the derivative. -/
theorem abs_le_initial_add_sqrt_radius_of_deriv_bound
    {a b C : ℝ} (hab : a < b) (hC : 0 ≤ C)
    {R N F D : ℝ → ℝ}
    (hR : ContinuousOn R (Icc a b))
    (hF : ContinuousOn F (Icc a b))
    (hpos : ∀ s ∈ Icc a b, 0 < R s)
    (hRd : ∀ s ∈ Ioo a b, HasDerivAt R (N s) s)
    (hFd : ∀ s ∈ Ioo a b, HasDerivAt F (D s) s)
    (hDbound : ∀ s ∈ Ioo a b,
      |D s| ≤ C * ((-N s) / Real.sqrt (R s))) :
    |F b| ≤ |F a| + 2 * C * Real.sqrt (R a) := by
  let T : ℝ → ℝ := fun s => 2 * C * Real.sqrt (R s)
  have hT : ContinuousOn T (Icc a b) :=
    continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn hR)
  have hTd : ∀ s ∈ Ioo a b,
      HasDerivAt T (C * N s / Real.sqrt (R s)) s := by
    intro s hs
    have hp := hpos s ⟨hs.1.le, hs.2.le⟩
    have h := (Real.hasDerivAt_sqrt hp.ne').comp s (hRd s hs)
    have h' := h.const_mul (2 * C)
    convert h' using 1
    · dsimp [T]
    · field_simp [ne_of_gt (Real.sqrt_pos.2 hp)]
  have hplusC : ContinuousOn (fun s => F s + T s) (Icc a b) := hF.add hT
  have hminusC : ContinuousOn (fun s => -F s + T s) (Icc a b) := hF.neg.add hT
  have hplusD : ∀ s ∈ Ioo a b,
      HasDerivAt (fun t => F t + T t)
        (D s + C * N s / Real.sqrt (R s)) s := by
    intro s hs
    exact (hFd s hs).add (hTd s hs)
  have hminusD : ∀ s ∈ Ioo a b,
      HasDerivAt (fun t => -F t + T t)
        (-D s + C * N s / Real.sqrt (R s)) s := by
    intro s hs
    exact (hFd s hs).neg.add (hTd s hs)
  have hplusBound : ∀ s ∈ Ioo a b,
      D s + C * N s / Real.sqrt (R s) ≤ 0 := by
    intro s hs
    have h := hDbound s hs
    have hle := le_abs_self (D s)
    have heq : C * ((-N s) / Real.sqrt (R s)) =
        -(C * N s / Real.sqrt (R s)) := by ring
    rw [heq] at h
    linarith only [h, hle]
  have hminusBound : ∀ s ∈ Ioo a b,
      -D s + C * N s / Real.sqrt (R s) ≤ 0 := by
    intro s hs
    have h := hDbound s hs
    have hle := neg_le_abs (D s)
    have heq : C * ((-N s) / Real.sqrt (R s)) =
        -(C * N s / Real.sqrt (R s)) := by ring
    rw [heq] at h
    linarith only [h, hle]
  have hInt : interior (Icc a b) = Ioo a b := by
    rw [interior_Icc]
  have hplusAnti : AntitoneOn (fun s => F s + T s) (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hplusC
    · intro s hs
      exact (hplusD s (by simpa only [hInt] using hs)).hasDerivWithinAt
    · intro s hs
      exact hplusBound s (by simpa only [hInt] using hs)
  have hminusAnti : AntitoneOn (fun s => -F s + T s) (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hminusC
    · intro s hs
      exact (hminusD s (by simpa only [hInt] using hs)).hasDerivWithinAt
    · intro s hs
      exact hminusBound s (by simpa only [hInt] using hs)
  have hp := hplusAnti (left_mem_Icc.mpr hab.le)
    (right_mem_Icc.mpr hab.le) hab.le
  have hm := hminusAnti (left_mem_Icc.mpr hab.le)
    (right_mem_Icc.mpr hab.le) hab.le
  have hTb : 0 ≤ T b := mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hFa := le_abs_self (F a)
  have hFa' := neg_le_abs (F a)
  apply abs_le.mpr
  constructor <;> dsimp [T] at hp hm hTb ⊢ <;> linarith only [hp, hm, hTb, hFa, hFa']

end intervalIntegral

end
