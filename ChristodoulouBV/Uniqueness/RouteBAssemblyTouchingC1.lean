module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.ClosedConvexJet
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.IntervalC1ExtensionBounds
import Mathlib.Tactic.Linarith

/-!
# Joining first-order traces at one endpoint

Two globally C¹ continuations with a common value and first jet at a point
glue to a globally C¹ function, preserving each continuation on its side.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Two globally C¹ real functions with matching value and derivative at a
common endpoint yield one globally C¹ left/right splice. -/
theorem exists_contDiff_one_of_touching_c1
    {s : ℝ} {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hvalue : f s = g s)
    (hjet : fderiv ℝ f s = fderiv ℝ g s) :
    ∃ F : ℝ → ℝ, ContDiff ℝ 1 F ∧
      (∀ x ≤ s, F x = f x) ∧
      ∀ x, s ≤ x → F x = g x := by
  let K : Bool → Set ℝ := fun i => if i then Ici s else Iic s
  let q : Bool → ℝ → ℝ := fun i => if i then g else f
  let D : Bool → ℝ → ℝ →L[ℝ] ℝ := fun i x => fderiv ℝ (q i) x
  have hconv : ∀ i ∈ (Finset.univ : Finset Bool), Convex ℝ (K i) := by
    intro i _
    cases i
    · exact convex_Iic s
    · exact convex_Ici s
  have hclosed : ∀ i ∈ (Finset.univ : Finset Bool), IsClosed (K i) := by
    intro i _
    cases i
    · exact isClosed_Iic
    · exact isClosed_Ici
  have hinterior : ∀ i ∈ (Finset.univ : Finset Bool),
      (interior (K i)).Nonempty := by
    intro i _
    cases i
    · rw [show K false = Iic s from rfl, interior_Iic]
      exact ⟨s - 1, by simp⟩
    · rw [show K true = Ici s from rfl, interior_Ici]
      exact ⟨s + 1, by simp⟩
  have hq (i : Bool) : ContDiff ℝ 1 (q i) := by
    cases i
    · exact hf
    · exact hg
  have hvalueAgree : ∀ i ∈ (Finset.univ : Finset Bool),
      ∀ j ∈ (Finset.univ : Finset Bool),
        EqOn (q i) (q j) (K i ∩ K j) := by
    intro i _ j _ x hx
    cases i <;> cases j
    · rfl
    · have hxs : x = s := le_antisymm hx.1 hx.2
      subst x
      exact hvalue
    · have hxs : x = s := le_antisymm hx.2 hx.1
      subst x
      exact hvalue.symm
    · rfl
  have hjetAgree : ∀ i ∈ (Finset.univ : Finset Bool),
      ∀ j ∈ (Finset.univ : Finset Bool),
        EqOn (D i) (D j) (K i ∩ K j) := by
    intro i _ j _ x hx
    cases i <;> cases j
    · rfl
    · have hxs : x = s := le_antisymm hx.1 hx.2
      subst x
      exact hjet
    · have hxs : x = s := le_antisymm hx.2 hx.1
      subst x
      exact hjet.symm
    · rfl
  obtain ⟨F, _, hF, hEq, _⟩ :=
    Convex.exists_contDiffOn_one_finset_glue
      (Finset.univ : Finset Bool) K hconv hclosed hinterior q D
      (fun i _ => (hq i).continuous.continuousOn)
      (fun i _ => ((hq i).continuous_fderiv (by norm_num)).continuousOn)
      (fun i _ => (hq i).differentiable (by norm_num) |>.differentiableOn)
      (fun i _ x _ => rfl)
      hvalueAgree hjetAgree
  have hUnion : (⋃ i ∈ (Finset.univ : Finset Bool), K i) = (univ : Set ℝ) := by
    ext x
    simp only [mem_iUnion, Finset.mem_univ, mem_univ, iff_true]
    by_cases hx : x ≤ s
    · exact ⟨false, trivial, hx⟩
    · exact ⟨true, trivial, le_of_not_ge hx⟩
  have hFglobal : ContDiff ℝ 1 F := by
    rw [hUnion, contDiffOn_univ] at hF
    exact hF
  refine ⟨F, hFglobal, ?_, ?_⟩
  · intro x hx
    exact hEq false (Finset.mem_univ _) (show x ∈ K false from hx)
  · intro x hx
    exact hEq true (Finset.mem_univ _) (show x ∈ K true from hx)

/-- Adjacent compact C¹ intervals glue when their relative one-sided
derivatives match at the common endpoint. -/
theorem exists_contDiff_one_of_touching_compact_intervals
    {a s b : ℝ} {f g : ℝ → ℝ}
    (has : a < s) (hsb : s < b)
    (hf : ContDiffOn ℝ 1 f (Icc a s))
    (hg : ContDiffOn ℝ 1 g (Icc s b))
    (hvalue : f s = g s)
    (hjet : derivWithin f (Icc a s) s = derivWithin g (Icc s b) s) :
    ∃ F : ℝ → ℝ, ContDiff ℝ 1 F ∧
      (∀ x ∈ Icc a s, F x = f x) ∧
      ∀ x ∈ Icc s b, F x = g x := by
  let f₁ := intervalC1Extension f a s
  let g₁ := intervalC1Extension g s b
  have hf₁ : ContDiff ℝ 1 f₁ := intervalC1Extension_c1 has hf
  have hg₁ : ContDiff ℝ 1 g₁ := intervalC1Extension_c1 hsb hg
  have hv : f₁ s = g₁ s := by
    change intervalC1Extension f a s s = intervalC1Extension g s b s
    rw [intervalC1Extension_eq ⟨has.le, le_rfl⟩,
      intervalC1Extension_eq ⟨le_rfl, hsb.le⟩]
    exact hvalue
  have hd : fderiv ℝ f₁ s = fderiv ℝ g₁ s := by
    have hfderiv := deriv_intervalC1Extension_eq has hf ⟨has.le, le_rfl⟩
    have hgderiv := deriv_intervalC1Extension_eq hsb hg ⟨le_rfl, hsb.le⟩
    have hscalar : deriv f₁ s = deriv g₁ s := hfderiv.trans (hjet.trans hgderiv.symm)
    apply ContinuousLinearMap.ext_ring
    rw [fderiv_eq_deriv_mul, fderiv_eq_deriv_mul, hscalar]
  obtain ⟨F, hF, hleft, hright⟩ :=
    exists_contDiff_one_of_touching_c1 hf₁ hg₁ hv hd
  refine ⟨F, hF, ?_, ?_⟩
  · intro x hx
    exact (hleft x hx.2).trans (intervalC1Extension_eq hx)
  · intro x hx
    exact (hright x hx.1).trans (intervalC1Extension_eq hx)

end ChristodoulouBV.Uniqueness

end
