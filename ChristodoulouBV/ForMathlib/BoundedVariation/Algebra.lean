module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Algebraic bounds for variation of real functions

Variation estimates for sums, products, quotients, logarithms, and exponentials on an
arbitrary subset of a linearly ordered domain.
-/

public section

open Set

variable {α : Type*} [LinearOrder α] {s : Set α} {f g : α → ℝ}

namespace eVariationOn

/-- A pointwise real Lipschitz bound gives a bound on variation. -/
theorem le_of_dist_le {h k : α → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hh : ∀ x ∈ s, ∀ y ∈ s, dist (h x) (h y) ≤ C * dist (k x) (k y)) :
    eVariationOn h s ≤ ENNReal.ofReal C * eVariationOn k s := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  calc
    (∑ i ∈ Finset.range n, edist (h (u (i + 1))) (h (u i)))
        ≤ ∑ i ∈ Finset.range n,
            ENNReal.ofReal C * edist (k (u (i + 1))) (k (u i)) := by
          apply Finset.sum_le_sum
          intro i _
          rw [edist_dist, edist_dist, ← ENNReal.ofReal_mul hC]
          exact ENNReal.ofReal_le_ofReal (hh _ (hus _) _ (hus _))
    _ = ENNReal.ofReal C *
          ∑ i ∈ Finset.range n, edist (k (u (i + 1))) (k (u i)) := by
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal C * eVariationOn k s := by
        gcongr
        exact sum_le hu hus

/-- The variation of a sum is at most the sum of the variations. -/
theorem add_le (f g : α → ℝ) (s : Set α) :
    eVariationOn (f + g) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  calc
    (∑ i ∈ Finset.range n,
        edist ((f + g) (u (i + 1))) ((f + g) (u i)))
        ≤ ∑ i ∈ Finset.range n,
            (edist (f (u (i + 1))) (f (u i)) +
              edist (g (u (i + 1))) (g (u i))) := by
          apply Finset.sum_le_sum
          intro i _
          exact edist_add_add_le _ _ _ _
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
          ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) :=
        Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (sum_le hu hus) (sum_le hu hus)

/-- Negation preserves variation. -/
@[simp] theorem neg (f : α → ℝ) (s : Set α) :
    eVariationOn (-f) s = eVariationOn f s := by
  unfold eVariationOn
  congr 1 with p
  congr 1 with i
  exact edist_neg_neg _ _

/-- The variation of a difference is at most the sum of the variations. -/
theorem sub_le (f g : α → ℝ) (s : Set α) :
    eVariationOn (f - g) s ≤ eVariationOn f s + eVariationOn g s := by
  simpa only [sub_eq_add_neg, Pi.add_apply, Pi.neg_apply, neg] using add_le f (-g) s

/-- Adding a constant on the left preserves variation. -/
@[simp] theorem const_add (c : ℝ) (f : α → ℝ) (s : Set α) :
    eVariationOn (fun x => c + f x) s = eVariationOn f s := by
  unfold eVariationOn
  congr 1 with p
  congr 1 with i
  exact edist_add_left _ _ _

/-- Adding a constant on the right preserves variation. -/
@[simp] theorem add_const (f : α → ℝ) (c : ℝ) (s : Set α) :
    eVariationOn (fun x => f x + c) s = eVariationOn f s := by
  simpa only [add_comm c] using const_add c f s

/-- A product estimate with ordinary real bounds on the two factors. -/
theorem mul_le_of_abs_le {C D : ℝ} (hf : ∀ x ∈ s, |f x| ≤ C)
    (hg : ∀ x ∈ s, |g x| ≤ D) :
    eVariationOn (f * g) s ≤ ENNReal.ofReal C * eVariationOn g s +
      ENNReal.ofReal D * eVariationOn f s := by
  apply eVariation_mul_le
  · intro x hx
    simpa only [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal (hf x hx)
  · intro x hx
    simpa only [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal (hg x hx)

/-- If the absolute value of a function stays away from zero, its reciprocal's variation
is bounded by the original variation. -/
theorem inv_le_of_abs_ge {c : ℝ} (hc : 0 < c)
    (hg : ∀ x ∈ s, c ≤ |g x|) :
    eVariationOn (fun x => (g x)⁻¹) s ≤
      ENNReal.ofReal (1 / c ^ 2) * eVariationOn g s := by
  apply le_of_dist_le (by positivity)
  intro x hx y hy
  have hx0 : g x ≠ 0 := by
    intro he
    have := hg x hx
    simp [he] at this
    linarith
  have hy0 : g y ≠ 0 := by
    intro he
    have := hg y hy
    simp [he] at this
    linarith
  rw [dist_inv_inv₀ hx0 hy0]
  have hden : c ^ 2 ≤ ‖g x‖ * ‖g y‖ := by
    calc
      c ^ 2 = c * c := pow_two c
      _ ≤ |g x| * |g y| :=
        mul_le_mul (hg x hx) (hg y hy) hc.le (abs_nonneg _)
      _ = ‖g x‖ * ‖g y‖ := by simp only [Real.norm_eq_abs]
  have hdiv : 1 / (‖g x‖ * ‖g y‖) ≤ 1 / c ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hc) hden
  rw [div_eq_mul_inv]
  simpa only [one_div, mul_comm] using
    mul_le_mul_of_nonneg_left hdiv dist_nonneg

/-- The variation of a quotient, assuming a lower bound on its denominator and an upper
bound on its numerator. -/
theorem div_le_of_abs_ge {c M : ℝ} (hc : 0 < c)
    (hg : ∀ x ∈ s, c ≤ |g x|) (hf : ∀ x ∈ s, |f x| ≤ M) :
    eVariationOn (fun x => f x / g x) s ≤
      ENNReal.ofReal (1 / c) * eVariationOn f s +
        ENNReal.ofReal (M / c ^ 2) * eVariationOn g s := by
  rcases s.eq_empty_or_nonempty with hs | ⟨x₀, hx₀⟩
  · subst s
    simp
  have hprod := mul_le_of_abs_le (s := s) (f := fun x => (g x)⁻¹) (g := f)
    (fun x hx => by
      rw [abs_inv]
      exact inv_anti₀ hc (hg x hx)) hf
  have hinv := inv_le_of_abs_ge hc hg
  have hM : 0 ≤ M := (abs_nonneg _).trans (hf x₀ hx₀)
  have hstep : eVariationOn (fun x => f x / g x) s ≤
      ENNReal.ofReal (1 / c) * eVariationOn f s +
        ENNReal.ofReal M * (ENNReal.ofReal (1 / c ^ 2) * eVariationOn g s) := by
    calc
      eVariationOn (fun x => f x / g x) s =
          eVariationOn ((fun x => (g x)⁻¹) * f) s := by
        congr 1
        funext x
        simp only [Pi.mul_apply, div_eq_mul_inv, mul_comm]
      _ ≤ ENNReal.ofReal (1 / c) * eVariationOn f s +
          ENNReal.ofReal M * eVariationOn (fun x => (g x)⁻¹) s := by
            simpa only [one_div] using hprod
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hinv bot_le)
  convert hstep using 1
  rw [← mul_assoc, ← ENNReal.ofReal_mul hM]
  congr 1
  field_simp

/-- A positive lower bound controls variation after taking logarithms. -/
theorem log_comp_le {c : ℝ} (hc : 0 < c) (hg : ∀ x ∈ s, c ≤ g x) :
    eVariationOn (Real.log ∘ g) s ≤
      ENNReal.ofReal (1 / c) * eVariationOn g s := by
  apply le_of_dist_le (by positivity)
  intro x hx y hy
  have hbound (z : ℝ) (hz : z ∈ Ici c) : ‖deriv Real.log z‖ ≤ 1 / c := by
    rw [Real.deriv_log, Real.norm_eq_abs, abs_inv, abs_of_pos (hc.trans_le hz)]
    simpa only [one_div] using one_div_le_one_div_of_le hc hz
  have hdiff (z : ℝ) (hz : z ∈ Ici c) : DifferentiableAt ℝ Real.log z :=
    (Real.hasDerivAt_log (ne_of_gt (hc.trans_le hz))).differentiableAt
  simpa only [Function.comp_apply, dist_eq_norm] using
    (convex_Ici c).norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (hg y hy) (hg x hx)

/-- An upper bound on the exponent controls variation after exponentiation. -/
theorem exp_comp_le {K : ℝ} (hg : ∀ x ∈ s, g x ≤ K) :
    eVariationOn (Real.exp ∘ g) s ≤
      ENNReal.ofReal (Real.exp K) * eVariationOn g s := by
  apply le_of_dist_le (Real.exp_nonneg _)
  intro x hx y hy
  have hbound (z : ℝ) (hz : z ∈ Iic K) : ‖deriv Real.exp z‖ ≤ Real.exp K := by
    rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos z)]
    exact Real.exp_le_exp.mpr hz
  simpa only [Function.comp_apply, dist_eq_norm] using
    (convex_Iic K).norm_image_sub_le_of_norm_deriv_le
      (fun z _ => Real.differentiable_exp z) hbound (hg y hy) (hg x hx)

end eVariationOn

namespace BoundedVariationOn

/-- A sum of two functions of bounded variation has bounded variation. -/
theorem add (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (f + g) s :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) (eVariationOn.add_le f g s)

/-- A difference of two functions of bounded variation has bounded variation. -/
theorem sub (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (f - g) s :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) (eVariationOn.sub_le f g s)

/-- Negation preserves bounded variation. -/
theorem neg (hf : BoundedVariationOn f s) : BoundedVariationOn (-f) s := by
  simpa only [BoundedVariationOn, eVariationOn.neg] using hf

/-- Adding a constant preserves bounded variation. -/
theorem const_add (hf : BoundedVariationOn f s) (c : ℝ) :
    BoundedVariationOn (fun x => c + f x) s := by
  simpa only [BoundedVariationOn, eVariationOn.const_add] using hf

end BoundedVariationOn

namespace LocallyBoundedVariationOn

/-- A sum of locally bounded variation functions has locally bounded variation. -/
theorem add (hf : LocallyBoundedVariationOn f s) (hg : LocallyBoundedVariationOn g s) :
    LocallyBoundedVariationOn (f + g) s :=
  fun a b ha hb => (hf a b ha hb).add (hg a b ha hb)

/-- A difference of locally bounded variation functions has locally bounded variation. -/
theorem sub (hf : LocallyBoundedVariationOn f s) (hg : LocallyBoundedVariationOn g s) :
    LocallyBoundedVariationOn (f - g) s :=
  fun a b ha hb => (hf a b ha hb).sub (hg a b ha hb)

/-- Negation preserves locally bounded variation. -/
theorem neg (hf : LocallyBoundedVariationOn f s) :
    LocallyBoundedVariationOn (-f) s :=
  fun a b ha hb => (hf a b ha hb).neg

/-- Adding a constant preserves locally bounded variation. -/
theorem const_add (hf : LocallyBoundedVariationOn f s) (c : ℝ) :
    LocallyBoundedVariationOn (fun x => c + f x) s :=
  fun a b ha hb => (hf a b ha hb).const_add c

end LocallyBoundedVariationOn
