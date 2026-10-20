module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Order.Interval.Set.ProjIcc

/-!
# Constant extension from a closed real interval

A real function is extended by projecting its argument onto `[a,b]`. This module
records its values, exact variation, bounded variation, and right continuity.
-/

public section

open Set
open scoped Topology

namespace Function

/-- Extend a real function constantly to the two sides of `[a,b]`. -/
@[expose] noncomputable def extendIcc (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) : ℝ → ℝ :=
  fun x => f (Set.projIcc a b hab x)

/-- The constant extension is Mathlib's interval extension of the restricted function. -/
theorem extendIcc_eq_IccExtend (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    extendIcc f hab = Set.IccExtend hab (fun x : Icc a b => f x) := rfl

end Function

namespace BoundedVariationOn

variable {f : ℝ → ℝ}

/-- The constant extension agrees with the original function on `[a,b]`. -/
theorem extendIcc_of_mem {f : ℝ → ℝ} {a b x : ℝ} (hab : a ≤ b)
    (hx : x ∈ Icc a b) : Function.extendIcc f hab x = f x := by
  simp only [Function.extendIcc, Set.projIcc_of_mem hab hx]

/-- The constant extension is `f a` to the left of the interval. -/
theorem extendIcc_of_le_left {f : ℝ → ℝ} {a b x : ℝ} (hab : a ≤ b)
    (hx : x ≤ a) : Function.extendIcc f hab x = f a := by
  simp only [Function.extendIcc, Set.projIcc_of_le_left hab hx]

/-- The constant extension is `f b` to the right of the interval. -/
theorem extendIcc_of_right_le {f : ℝ → ℝ} {a b x : ℝ} (hab : a ≤ b)
    (hx : b ≤ x) : Function.extendIcc f hab x = f b := by
  simp only [Function.extendIcc, Set.projIcc_of_right_le hab hx]

/-- Constant extension preserves exactly the variation on the closed interval. -/
theorem eVariationOn_extendIcc {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    eVariationOn (Function.extendIcc f hab) univ = eVariationOn f (Icc a b) := by
  let p : ℝ → ℝ := fun x => (Set.projIcc a b hab x : ℝ)
  have hp : Monotone p := fun x y hxy => Set.monotone_projIcc hab hxy
  have hr : p '' univ = Icc a b := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact (Set.projIcc a b hab y).property
    · intro hx
      exact ⟨x, mem_univ x, by simp [p, Set.projIcc_of_mem hab hx]⟩
  have heq : Function.extendIcc f hab = f ∘ p := rfl
  rw [heq, eVariationOn.comp_eq_of_monotoneOn f p (hp.monotoneOn univ), hr]

/-- A function locally BV on `[a,b]` has a globally BV constant extension. -/
theorem extendIcc_boundedVariationOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) :
    BoundedVariationOn (Function.extendIcc f hab) univ := by
  simpa only [BoundedVariationOn, eVariationOn_extendIcc hab] using hf

/-- Right continuity on `[a,b)` extends to right continuity of the constant extension on
the whole line. -/
theorem right_continuous_extendIcc {a b : ℝ} (hab : a ≤ b)
    (hr : ∀ x ∈ Ico a b, ContinuousWithinAt f (Ici x) x) (x : ℝ) :
    ContinuousWithinAt (Function.extendIcc f hab) (Ici x) x := by
  let g := Function.extendIcc f hab
  rcases lt_trichotomy x a with hxa | hxa | hax
  · have heq : g =ᶠ[𝓝[Ici x] x] fun _ => f a := by
      filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Iio_mem_nhds hxa)] with z hz
      simp only [g, Function.extendIcc]
      rw [Set.projIcc_of_le_left hab hz.le]
    have hx : g x = f a := by
      simp only [g, Function.extendIcc]
      rw [Set.projIcc_of_le_left hab hxa.le]
    change Filter.Tendsto g (𝓝[Ici x] x) (𝓝 (g x))
    rw [hx]
    exact heq.tendsto
  · subst x
    by_cases hab' : a < b
    · have heq : g =ᶠ[𝓝[Ici a] a] f := by
        filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (Iio_mem_nhds hab'), self_mem_nhdsWithin] with z hzb haz
        simp only [g, Function.extendIcc]
        rw [Set.projIcc_of_mem hab ⟨haz, hzb.le⟩]
      have hx : g a = f a := by
        simp only [g, Function.extendIcc]
        rw [Set.projIcc_left]
      change Filter.Tendsto g (𝓝[Ici a] a) (𝓝 (g a))
      rw [hx]
      exact (hr a ⟨le_rfl, hab'⟩).tendsto.congr' heq.symm
    · have hab'' : a = b := le_antisymm hab (le_of_not_gt hab')
      subst b
      have heq : g = fun _ => f a := by
        funext z
        simp only [g, Function.extendIcc]
        exact congrArg f (le_antisymm (Set.projIcc a a hab z).2.2
          (Set.projIcc a a hab z).2.1)
      change ContinuousWithinAt g (Ici a) a
      rw [heq]
      exact continuousWithinAt_const
  · by_cases hxb : x < b
    · have heq : g =ᶠ[𝓝[Ici x] x] f := by
        filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (Iio_mem_nhds hxb), self_mem_nhdsWithin] with z hzb hxz
        simp only [g, Function.extendIcc]
        rw [Set.projIcc_of_mem hab ⟨hax.le.trans hxz, hzb.le⟩]
      have hx : g x = f x := by
        simp only [g, Function.extendIcc]
        rw [Set.projIcc_of_mem hab ⟨hax.le, hxb.le⟩]
      change Filter.Tendsto g (𝓝[Ici x] x) (𝓝 (g x))
      rw [hx]
      exact (hr x ⟨hax.le, hxb⟩).tendsto.congr' heq.symm
    · have hbx : b ≤ x := le_of_not_gt hxb
      have heq : g =ᶠ[𝓝[Ici x] x] fun _ => f b := by
        filter_upwards [self_mem_nhdsWithin] with z hxz
        simp only [g, Function.extendIcc]
        rw [Set.projIcc_of_right_le hab (hbx.trans hxz)]
      have hx : g x = f b := by
        simp only [g, Function.extendIcc]
        rw [Set.projIcc_of_right_le hab hbx]
      change Filter.Tendsto g (𝓝[Ici x] x) (𝓝 (g x))
      rw [hx]
      exact heq.tendsto

end BoundedVariationOn
