module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.IntervalC1Extension
import Mathlib.Tactic

/-!
# Derivative and value bounds for first-order interval continuation

The derivative of the continuation takes only values already attained by
the relative derivative on the original interval. Consequently its optimal
uniform derivative bound is unchanged.
-/

public section

noncomputable section

open Set Filter
open scoped Topology

namespace ChristodoulouBV

/-- First-order continuation with explicitly prescribed one-sided endpoint
slopes. The slopes must agree with the relative derivatives of the data. -/
@[expose] def intervalC1ExtensionWithSlopes (f : ℝ → ℝ)
    (a c da dc x : ℝ) : ℝ :=
  if x < a then f a + da * (x - a)
  else if x ≤ c then f x
  else f c + dc * (x - c)

/-- A first-order continuation with compatible prescribed one-sided slopes
is globally `C¹` and preserves the original values. -/
theorem intervalC1ExtensionWithSlopes_c1 {f : ℝ → ℝ} {a c da dc : ℝ}
    (hac : a < c) (hf : ContDiffOn ℝ 1 f (Icc a c))
    (hda : HasDerivWithinAt f da (Icc a c) a)
    (hdc : HasDerivWithinAt f dc (Icc a c) c) :
    ContDiff ℝ 1 (intervalC1ExtensionWithSlopes f a c da dc) := by
  have hdaEq : derivWithin f (Icc a c) a = da :=
    hda.derivWithin ((uniqueDiffOn_Icc hac) a ⟨le_rfl, hac.le⟩)
  have hdcEq : derivWithin f (Icc a c) c = dc :=
    hdc.derivWithin ((uniqueDiffOn_Icc hac) c ⟨hac.le, le_rfl⟩)
  have hEq : intervalC1ExtensionWithSlopes f a c da dc =
      intervalC1Extension f a c := by
    funext x
    simp only [intervalC1Extension, intervalC1ExtensionWithSlopes,
      hdaEq, hdcEq]
  rw [hEq]
  exact intervalC1Extension_c1 hac hf

/-- The prescribed-slope continuation agrees with the data on its interval. -/
theorem intervalC1ExtensionWithSlopes_eq {f : ℝ → ℝ} {a c da dc x : ℝ}
    (hx : x ∈ Icc a c) : intervalC1ExtensionWithSlopes f a c da dc x = f x := by
  simp [intervalC1ExtensionWithSlopes, not_lt.mpr hx.1, hx.2]

/-- On the original interval, the ordinary derivative of the extension is
the relative derivative of the supplied function. -/
theorem deriv_intervalC1Extension_eq {f : ℝ → ℝ} {a c x : ℝ}
    (hac : a < c) (hf : ContDiffOn ℝ 1 f (Icc a c))
    (hx : x ∈ Icc a c) :
    deriv (intervalC1Extension f a c) x = derivWithin f (Icc a c) x := by
  have hF := intervalC1Extension_c1 hac hf
  have hfd : HasDerivWithinAt (intervalC1Extension f a c)
      (deriv (intervalC1Extension f a c) x) (Icc a c) x :=
    ((hF.differentiable (by norm_num) x).hasDerivAt).hasDerivWithinAt
  have hEq : EqOn (intervalC1Extension f a c) f (Icc a c) :=
    fun _ hy => intervalC1Extension_eq hy
  have hderiv := hfd.derivWithin ((uniqueDiffOn_Icc hac) x hx)
  rw [derivWithin_congr hEq (hEq hx)] at hderiv
  exact hderiv.symm

/-- The ordinary endpoint derivatives of the prescribed-slope continuation
are exactly the two supplied one-sided slopes. -/
theorem intervalC1ExtensionWithSlopes_endpoint_deriv
    {f : ℝ → ℝ} {a c da dc : ℝ}
    (hac : a < c) (hf : ContDiffOn ℝ 1 f (Icc a c))
    (hda : HasDerivWithinAt f da (Icc a c) a)
    (hdc : HasDerivWithinAt f dc (Icc a c) c) :
    deriv (intervalC1ExtensionWithSlopes f a c da dc) a = da ∧
      deriv (intervalC1ExtensionWithSlopes f a c da dc) c = dc := by
  have hdaEq : derivWithin f (Icc a c) a = da :=
    hda.derivWithin ((uniqueDiffOn_Icc hac) a ⟨le_rfl, hac.le⟩)
  have hdcEq : derivWithin f (Icc a c) c = dc :=
    hdc.derivWithin ((uniqueDiffOn_Icc hac) c ⟨hac.le, le_rfl⟩)
  have hEq : intervalC1ExtensionWithSlopes f a c da dc =
      intervalC1Extension f a c := by
    funext x
    simp only [intervalC1Extension, intervalC1ExtensionWithSlopes,
      hdaEq, hdcEq]
  rw [hEq]
  exact ⟨(deriv_intervalC1Extension_eq hac hf ⟨le_rfl, hac.le⟩).trans hdaEq,
    (deriv_intervalC1Extension_eq hac hf ⟨hac.le, le_rfl⟩).trans hdcEq⟩

/-- To the left of the interval, the extension has the prescribed left
endpoint slope. -/
theorem deriv_intervalC1Extension_left {f : ℝ → ℝ} {a c x : ℝ}
    (hac : a < c) (hf : ContDiffOn ℝ 1 f (Icc a c))
    (hx : x ≤ a) :
    deriv (intervalC1Extension f a c) x = derivWithin f (Icc a c) a := by
  rcases eq_or_lt_of_le hx with rfl | hxa
  · exact deriv_intervalC1Extension_eq hac hf ⟨le_rfl, hac.le⟩
  · let d := derivWithin f (Icc a c) a
    have hlin : HasDerivAt (fun t : ℝ => f a + d * (t - a)) d x := by
      convert (hasDerivAt_const x (f a)).add
        (((hasDerivAt_id' x).sub_const a).const_mul d) using 1; ring
    have hEq : intervalC1Extension f a c =ᶠ[𝓝 x]
        (fun t => f a + d * (t - a)) := by
      filter_upwards [Iio_mem_nhds hxa] with y hy
      have hya : y < a := hy
      simp [intervalC1Extension, hya, d]
    exact (hlin.congr_of_eventuallyEq hEq).deriv

/-- To the right of the interval, the extension has the prescribed right
endpoint slope. -/
theorem deriv_intervalC1Extension_right {f : ℝ → ℝ} {a c x : ℝ}
    (hac : a < c) (hf : ContDiffOn ℝ 1 f (Icc a c))
    (hx : c ≤ x) :
    deriv (intervalC1Extension f a c) x = derivWithin f (Icc a c) c := by
  rcases eq_or_lt_of_le hx with rfl | hcx
  · exact deriv_intervalC1Extension_eq hac hf ⟨hac.le, le_rfl⟩
  · let d := derivWithin f (Icc a c) c
    have hlin : HasDerivAt (fun t : ℝ => f c + d * (t - c)) d x := by
      convert (hasDerivAt_const x (f c)).add
        (((hasDerivAt_id' x).sub_const c).const_mul d) using 1; ring
    have hEq : intervalC1Extension f a c =ᶠ[𝓝 x]
        (fun t => f c + d * (t - c)) := by
      filter_upwards [Ioi_mem_nhds hcx] with y hy
      have hay : ¬ y < a := not_lt.mpr (hac.le.trans hy.le)
      simp [intervalC1Extension, hay, not_le.mpr hy, d]
    exact (hlin.congr_of_eventuallyEq hEq).deriv

/-- Every slope of the extension is a slope from the original interval. -/
theorem exists_derivWithin_eq_deriv_intervalC1Extension
    {f : ℝ → ℝ} {a c x : ℝ}
    (hac : a < c) (hf : ContDiffOn ℝ 1 f (Icc a c)) :
    ∃ y ∈ Icc a c,
      deriv (intervalC1Extension f a c) x = derivWithin f (Icc a c) y := by
  rcases lt_trichotomy x a with hxa | hxa | hax
  · exact ⟨a, ⟨le_rfl, hac.le⟩,
      deriv_intervalC1Extension_left hac hf hxa.le⟩
  · subst x
    exact ⟨a, ⟨le_rfl, hac.le⟩,
      deriv_intervalC1Extension_eq hac hf ⟨le_rfl, hac.le⟩⟩
  · rcases le_total x c with hxc | hcx
    · exact ⟨x, ⟨hax.le, hxc⟩,
        deriv_intervalC1Extension_eq hac hf ⟨hax.le, hxc⟩⟩
    · exact ⟨c, ⟨hac.le, le_rfl⟩,
        deriv_intervalC1Extension_right hac hf hcx⟩

/-- A uniform bound for the relative derivative is exactly a uniform
bound for the derivative of the global continuation. -/
theorem intervalC1Extension_deriv_bound_iff {f : ℝ → ℝ} {a c M : ℝ}
    (hac : a < c) (hf : ContDiffOn ℝ 1 f (Icc a c)) :
    (∀ x, |deriv (intervalC1Extension f a c) x| ≤ M) ↔
      (∀ x ∈ Icc a c, |derivWithin f (Icc a c) x| ≤ M) := by
  constructor
  · intro h x hx
    rw [← deriv_intervalC1Extension_eq hac hf hx]
    exact h x
  · intro h x
    obtain ⟨y, hy, hxy⟩ :=
      exists_derivWithin_eq_deriv_intervalC1Extension hac hf (x := x)
    rw [hxy]
    exact h y hy

/-- The global derivative and the original relative derivative have exactly
the same supremum of absolute values. -/
theorem intervalC1Extension_deriv_sSup_eq {f : ℝ → ℝ} {a c : ℝ}
    (hac : a < c) (hf : ContDiffOn ℝ 1 f (Icc a c)) :
    sSup (range (fun x : ℝ => |deriv (intervalC1Extension f a c) x|)) =
      sSup ((fun x => |derivWithin f (Icc a c) x|) '' Icc a c) := by
  congr 1
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy, hxy⟩ :=
      exists_derivWithin_eq_deriv_intervalC1Extension hac hf (x := x)
    exact ⟨y, hy, by simpa only using congrArg (fun z : ℝ => |z|) hxy.symm⟩
  · rintro ⟨x, hx, rfl⟩
    have h := congrArg (fun z : ℝ => |z|)
      (deriv_intervalC1Extension_eq hac hf hx)
    exact ⟨x, by simpa only using h⟩

/-- On any bounded window, the continued value is controlled by its value
at the left endpoint and by the original interval's derivative bound. -/
theorem intervalC1Extension_value_bound {f : ℝ → ℝ} {a c x M R : ℝ}
    (hac : a < c) (hf : ContDiffOn ℝ 1 f (Icc a c))
    (hM : ∀ y ∈ Icc a c, |derivWithin f (Icc a c) y| ≤ M)
    (hR : |x - a| ≤ R) :
    |intervalC1Extension f a c x| ≤ |f a| + M * R := by
  have hM0 : 0 ≤ M := by
    have h := hM a ⟨le_rfl, hac.le⟩
    exact (abs_nonneg _).trans h
  have hF := intervalC1Extension_c1 hac hf
  have hderiv : ∀ y, ‖deriv (intervalC1Extension f a c) y‖ ≤ M := by
    intro y
    simpa only [Real.norm_eq_abs] using
      (intervalC1Extension_deriv_bound_iff hac hf).2 hM y
  have hLip := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (x := a) (y := x)
    (fun y _ => hF.differentiable (by norm_num) y)
    (fun y _ => hderiv y) (mem_univ a) (mem_univ x)
  have hfa : intervalC1Extension f a c a = f a :=
    intervalC1Extension_eq ⟨le_rfl, hac.le⟩
  rw [hfa, Real.norm_eq_abs, Real.norm_eq_abs] at hLip
  calc
    |intervalC1Extension f a c x| ≤
        |intervalC1Extension f a c x - f a| + |f a| := by
          simpa only [sub_add_cancel] using
            (abs_add_le (intervalC1Extension f a c x - f a) (f a))
    _ ≤ |f a| + M * R := by
      have hMR : M * |x - a| ≤ M * R := mul_le_mul_of_nonneg_left hR hM0
      linarith only [hLip, hMR]

end ChristodoulouBV

end
