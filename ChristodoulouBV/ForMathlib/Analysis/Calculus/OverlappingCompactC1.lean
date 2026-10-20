module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.IntervalC1Extension
import Mathlib.Tactic.Linarith

/-!
# Gluing C¹ functions on overlapping compact intervals

The overlap has positive length. Tangent-line continuations agree there, so
their piecewise splice is globally C¹.
-/

public section

noncomputable section

open Set ChristodoulouBV

/-- Two compact `C¹` functions that agree on a nontrivial overlap have a
single globally `C¹` representative agreeing with both. -/
theorem exists_contDiff_one_of_overlapping_compact_intervals
    {a s t b : ℝ} (has : a < s) (hst : s < t) (htb : t < b)
    {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc a t))
    (hg : ContDiffOn ℝ 1 g (Icc s b))
    (heq : ∀ x ∈ Icc s t, f x = g x) :
    ∃ F : ℝ → ℝ, ContDiff ℝ 1 F ∧
      (∀ x ∈ Icc a t, F x = f x) ∧
      ∀ x ∈ Icc s b, F x = g x := by
  let f₁ := intervalC1Extension f a t
  let g₁ := intervalC1Extension g s b
  have hf₁ : ContDiff ℝ 1 f₁ := intervalC1Extension_c1 (has.trans hst) hf
  have hg₁ : ContDiff ℝ 1 g₁ := intervalC1Extension_c1 (hst.trans htb) hg
  let F : ℝ → ℝ := fun x => if x < t then f₁ x else g₁ x
  have hEqOverlap : ∀ x ∈ Icc s t, f₁ x = g₁ x := by
    intro x hx
    change intervalC1Extension f a t x = intervalC1Extension g s b x
    rw [intervalC1Extension_eq ⟨has.le.trans hx.1, hx.2⟩,
      intervalC1Extension_eq ⟨hx.1, hx.2.trans htb.le⟩]
    exact heq x hx
  have hleft : ContDiffOn ℝ 1 F (Iio t) :=
    hf₁.contDiffOn.congr (by
      intro x hx
      change (if x < t then f₁ x else g₁ x) = f₁ x
      have hxt : x < t := hx
      rw [ite_eq_left hxt])
  have hright : ContDiffOn ℝ 1 F (Ioi s) :=
    hg₁.contDiffOn.congr (by
      intro x hx
      change (if x < t then f₁ x else g₁ x) = g₁ x
      by_cases hxt : x < t
      · rw [ite_eq_left hxt, hEqOverlap x ⟨hx.le, hxt.le⟩]
      · rw [ite_eq_right hxt])
  have hcover : Iio t ∪ Ioi s = (univ : Set ℝ) := by
    ext x
    simp only [mem_union, mem_Iio, mem_Ioi, mem_univ, iff_true]
    rcases lt_or_ge x t with hxt | hxt
    · exact Or.inl hxt
    · exact Or.inr (hst.trans_le hxt)
  have hF : ContDiff ℝ 1 F :=
    contDiff_of_contDiffOn_union_of_isOpen hleft hright hcover
      isOpen_Iio isOpen_Ioi
  refine ⟨F, hF, ?_, ?_⟩
  · intro x hx
    by_cases hxt : x < t
    · change (if x < t then f₁ x else g₁ x) = f x
      rw [ite_eq_left hxt]
      change intervalC1Extension f a t x = f x
      exact intervalC1Extension_eq hx
    · have hxeq : x = t := le_antisymm hx.2 (le_of_not_gt hxt)
      subst x
      change (if t < t then f₁ t else g₁ t) = f t
      rw [ite_eq_right (lt_irrefl t),
        ← hEqOverlap t ⟨hst.le, le_rfl⟩]
      exact intervalC1Extension_eq ⟨has.le.trans hst.le, le_rfl⟩
  · intro x hx
    by_cases hxt : x < t
    · change (if x < t then f₁ x else g₁ x) = g x
      rw [ite_eq_left hxt, hEqOverlap x ⟨hx.1, hxt.le⟩]
      change intervalC1Extension g s b x = g x
      exact intervalC1Extension_eq hx
    · change (if x < t then f₁ x else g₁ x) = g x
      rw [ite_eq_right hxt]
      change intervalC1Extension g s b x = g x
      exact intervalC1Extension_eq hx

end
