module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Lower semicontinuity of variation for integral representations

The variation estimate itself is in Mathlib. This file packages it with dominated
convergence for primitives represented by a product and an ordinary integral.

These theorems concern the pointwise variation of the primitive. The vector measure
associated with a BV function can discard isolated anomalous point values, so its
measure variation need not equal this pointwise variation without a normalized
representative and matching endpoint convention.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

namespace eVariationOn

/-- Pointwise convergence on a set gives the lower limit inequality for variation. -/
theorem le_liminf_of_tendsto_pointwise {α M : Type*} [LinearOrder α]
    [PseudoEMetricSpace M] {ι : Type*} {p : Filter ι} [p.NeBot]
    {F : ι → α → M} {f : α → M} {s : Set α}
    (hF : ∀ x ∈ s, Tendsto (fun i => F i x) p (𝓝 (f x))) :
    eVariationOn f s ≤ liminf (fun i => eVariationOn (F i) s) p := by
  refine (le_liminf_iff).2 fun v hv => ?_
  exact lowerSemicontinuous_aux hF hv

end eVariationOn

namespace BoundedVariationOn

/-- A sequence with uniformly bounded interval variation and a convergent value at the left
endpoint is uniformly bounded on the interval. -/
theorem exists_uniform_bound_of_variation_le_of_tendsto_left
    {g : ℕ → ℝ → ℝ} {g₀ : ℝ} {V : ℝ≥0∞} (hV : V ≠ ∞)
    (hvar : ∀ n, eVariationOn (g n) (Icc (0 : ℝ) 1) ≤ V)
    (hg₀ : Tendsto (fun n => g n 0) atTop (𝓝 g₀)) :
    ∃ C : ℝ, ∀ n t, t ∈ Icc (0 : ℝ) 1 → |g n t| ≤ C := by
  obtain ⟨C₀, hC₀⟩ :=
    (Metric.isBounded_range_of_tendsto (fun n => g n 0) hg₀).exists_norm_le
  refine ⟨V.toReal + C₀, fun n t ht => ?_⟩
  have hvn : BoundedVariationOn (g n) (Icc (0 : ℝ) 1) :=
    ne_top_of_le_ne_top hV (hvar n)
  have hd := hvn.dist_le ht (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  have hVn : (eVariationOn (g n) (Icc (0 : ℝ) 1)).toReal ≤ V.toReal :=
    ENNReal.toReal_mono hV (hvar n)
  have h₀ : |g n 0| ≤ C₀ := by
    simpa only [Real.norm_eq_abs] using hC₀ (g n 0) ⟨n, rfl⟩
  calc
    |g n t| = |(g n t - g n 0) + g n 0| := by simp only [sub_add_cancel]
    _ ≤ |g n t - g n 0| + |g n 0| := abs_add_le _ _
    _ ≤ V.toReal + C₀ := by
      rw [Real.dist_eq] at hd
      exact add_le_add (hd.trans hVn) h₀

end BoundedVariationOn

namespace intervalIntegral

/-- Uniform interval variation and bounded factors give a common bound for the product
integrand. -/
theorem exists_bound_product_of_uniform_variation
    {g p h : ℕ → ℝ → ℝ} {g₀ : ℝ → ℝ} {V : ℝ≥0∞}
    (hV : V ≠ ∞)
    (hvar : ∀ n, eVariationOn (g n) (Icc (0 : ℝ) 1) ≤ V)
    (hg₀ : Tendsto (fun n => g n 0) atTop (𝓝 (g₀ 0)))
    (hp_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n t, t ∈ Icc (0 : ℝ) 1 → |p n t| ≤ C)
    (hh_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n t, t ∈ Icc (0 : ℝ) 1 → |h n t| ≤ C) :
    ∃ C : ℝ, ∀ n t, t ∈ Icc (0 : ℝ) 1 → |g n t * p n t + h n t| ≤ C := by
  obtain ⟨Cg, hCg⟩ :=
    BoundedVariationOn.exists_uniform_bound_of_variation_le_of_tendsto_left
      hV hvar hg₀
  obtain ⟨Cp, _, hCp⟩ := hp_bound
  obtain ⟨Ch, _, hCh⟩ := hh_bound
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hCg₀ : 0 ≤ Cg := (abs_nonneg (g 0 0)).trans (hCg 0 0 hzero)
  refine ⟨Cg * Cp + Ch, fun n t ht => ?_⟩
  calc
    |g n t * p n t + h n t| ≤ |g n t * p n t| + |h n t| := abs_add_le _ _
    _ = |g n t| * |p n t| + |h n t| := by rw [abs_mul]
    _ ≤ Cg * Cp + Ch :=
      add_le_add (mul_le_mul (hCg n t ht) (hCp n t ht) (abs_nonneg _) hCg₀)
        (hCh n t ht)

/-- The integration-by-parts primitive built from four real functions. When `p = f'`,
it represents the cumulative expression `∫ f dg - h dx`, subject to the chosen Stieltjes
endpoint convention. -/
@[expose] noncomputable def productPrimitive (f g p h : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x * g x - f 0 * g 0 - ∫ t in (0 : ℝ)..x, (g t * p t + h t)

/-- Pointwise convergence and a common bound on a compact interval imply convergence of all
initial-segment integrals. -/
theorem tendsto_integral_of_pointwise_of_bounded
    {q : ℕ → ℝ → ℝ} {r : ℝ → ℝ} (hq_meas : ∀ n, Measurable (q n))
    (hq_bound : ∃ C : ℝ, ∀ n t, t ∈ Icc (0 : ℝ) 1 → |q n t| ≤ C)
    (hq_lim : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => q n t) atTop (𝓝 (r t)))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..x, q n t) atTop
      (𝓝 (∫ t in (0 : ℝ)..x, r t)) := by
  obtain ⟨C, hC⟩ := hq_bound
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (bound := fun _ => C)
  · exact Filter.Eventually.of_forall fun n => (hq_meas n).aestronglyMeasurable.restrict
  · refine Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun t ht => ?_
    have htx : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le hx.1] at ht
      exact ⟨ht.1.le, ht.2.trans hx.2⟩
    simpa only [Real.norm_eq_abs] using hC n t htx
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun t ht => ?_
    have htx : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le hx.1] at ht
      exact ⟨ht.1.le, ht.2.trans hx.2⟩
    exact hq_lim t htx

/-- Pointwise convergence of the four factors, together with a dominated product integrand,
gives pointwise convergence of their integration-by-parts primitives. -/
theorem tendsto_productPrimitive_of_bounded_integrand
    {f g p h : ℕ → ℝ → ℝ} {f₀ g₀ p₀ h₀ : ℝ → ℝ}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => f n t) atTop (𝓝 (f₀ t)))
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => g n t) atTop (𝓝 (g₀ t)))
    (hp : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => p n t) atTop (𝓝 (p₀ t)))
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => h n t) atTop (𝓝 (h₀ t)))
    (hq_meas : ∀ n, Measurable (fun t => g n t * p n t + h n t))
    (hq_bound : ∃ C : ℝ, ∀ n t, t ∈ Icc (0 : ℝ) 1 →
      |g n t * p n t + h n t| ≤ C)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => productPrimitive (f n) (g n) (p n) (h n) x) atTop
      (𝓝 (productPrimitive f₀ g₀ p₀ h₀ x)) := by
  have hq : ∀ t ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => g n t * p n t + h n t) atTop
        (𝓝 (g₀ t * p₀ t + h₀ t)) := by
    intro t ht
    exact ((hg t ht).mul (hp t ht)).add (hh t ht)
  have hi := tendsto_integral_of_pointwise_of_bounded hq_meas hq_bound hq hx
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  simpa only [productPrimitive] using
    (((hf x hx).mul (hg x hx)).sub ((hf 0 hzero).mul (hg 0 hzero))).sub hi

end intervalIntegral

namespace eVariationOn

/-- Variation of an integration-by-parts primitive is lower semicontinuous under pointwise
convergence of the factors and a common integrable bound for their product integrands. -/
theorem productPrimitive_le_liminf
    {f g p h : ℕ → ℝ → ℝ} {f₀ g₀ p₀ h₀ : ℝ → ℝ}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => f n t) atTop (𝓝 (f₀ t)))
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => g n t) atTop (𝓝 (g₀ t)))
    (hp : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => p n t) atTop (𝓝 (p₀ t)))
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => h n t) atTop (𝓝 (h₀ t)))
    (hq_meas : ∀ n, Measurable (fun t => g n t * p n t + h n t))
    (hq_bound : ∃ C : ℝ, ∀ n t, t ∈ Icc (0 : ℝ) 1 →
      |g n t * p n t + h n t| ≤ C) :
    eVariationOn (intervalIntegral.productPrimitive f₀ g₀ p₀ h₀) (Icc (0 : ℝ) 1) ≤
      liminf (fun n => eVariationOn
        (intervalIntegral.productPrimitive (f n) (g n) (p n) (h n))
        (Icc (0 : ℝ) 1)) atTop :=
  le_liminf_of_tendsto_pointwise fun _ hx =>
    intervalIntegral.tendsto_productPrimitive_of_bounded_integrand
      hf hg hp hh hq_meas hq_bound hx

/-- The dominated-integrand assumption follows from uniform variation of `g`, convergence
at the left endpoint, and separate sup-norm bounds on `p` and `h`. In applications `p` is
the derivative of `f`. -/
theorem productPrimitive_le_liminf_of_uniform_variation
    {f g p h : ℕ → ℝ → ℝ} {f₀ g₀ p₀ h₀ : ℝ → ℝ} {V : ℝ≥0∞}
    (hV : V ≠ ∞)
    (hvar : ∀ n, eVariationOn (g n) (Icc (0 : ℝ) 1) ≤ V)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => f n t) atTop (𝓝 (f₀ t)))
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => g n t) atTop (𝓝 (g₀ t)))
    (hp : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => p n t) atTop (𝓝 (p₀ t)))
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => h n t) atTop (𝓝 (h₀ t)))
    (hg_meas : ∀ n, Measurable (g n)) (hp_meas : ∀ n, Measurable (p n))
    (hh_meas : ∀ n, Measurable (h n))
    (hp_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n t, t ∈ Icc (0 : ℝ) 1 → |p n t| ≤ C)
    (hh_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n t, t ∈ Icc (0 : ℝ) 1 → |h n t| ≤ C) :
    eVariationOn (intervalIntegral.productPrimitive f₀ g₀ p₀ h₀) (Icc (0 : ℝ) 1) ≤
      liminf (fun n => eVariationOn
        (intervalIntegral.productPrimitive (f n) (g n) (p n) (h n))
        (Icc (0 : ℝ) 1)) atTop := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  refine productPrimitive_le_liminf hf hg hp hh
    (fun n => ((hg_meas n).mul (hp_meas n)).add (hh_meas n)) ?_
  exact intervalIntegral.exists_bound_product_of_uniform_variation hV hvar
    (hg 0 hzero) hp_bound hh_bound

/-- Under the same uniform variation and sup-norm assumptions, the integration-by-parts
primitives themselves converge at every point of the interval. -/
theorem productPrimitive_tendsto_of_uniform_variation
    {f g p h : ℕ → ℝ → ℝ} {f₀ g₀ p₀ h₀ : ℝ → ℝ} {V : ℝ≥0∞}
    (hV : V ≠ ∞)
    (hvar : ∀ n, eVariationOn (g n) (Icc (0 : ℝ) 1) ≤ V)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => f n t) atTop (𝓝 (f₀ t)))
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => g n t) atTop (𝓝 (g₀ t)))
    (hp : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => p n t) atTop (𝓝 (p₀ t)))
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => h n t) atTop (𝓝 (h₀ t)))
    (hg_meas : ∀ n, Measurable (g n)) (hp_meas : ∀ n, Measurable (p n))
    (hh_meas : ∀ n, Measurable (h n))
    (hp_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n t, t ∈ Icc (0 : ℝ) 1 → |p n t| ≤ C)
    (hh_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n t, t ∈ Icc (0 : ℝ) 1 → |h n t| ≤ C)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => intervalIntegral.productPrimitive (f n) (g n) (p n) (h n) x)
      atTop (𝓝 (intervalIntegral.productPrimitive f₀ g₀ p₀ h₀ x)) := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  exact intervalIntegral.tendsto_productPrimitive_of_bounded_integrand hf hg hp hh
    (fun n => ((hg_meas n).mul (hp_meas n)).add (hh_meas n))
    (intervalIntegral.exists_bound_product_of_uniform_variation hV hvar
      (hg 0 hzero) hp_bound hh_bound) hx

/-- Derivative form of pointwise convergence and variation lower semicontinuity for
integration-by-parts primitives. When the functions are differentiable, `deriv` is their
classical derivative. The estimate only uses its stated bounds and convergence. -/
theorem productPrimitive_deriv_tendsto_and_variation_le_liminf
    {f g h : ℕ → ℝ → ℝ} {f₀ g₀ h₀ : ℝ → ℝ} {V : ℝ≥0∞}
    (hV : V ≠ ∞)
    (hvar : ∀ n, eVariationOn (g n) (Icc (0 : ℝ) 1) ≤ V)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => f n t) atTop (𝓝 (f₀ t)))
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => g n t) atTop (𝓝 (g₀ t)))
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => deriv (f n) t) atTop (𝓝 (deriv f₀ t)))
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun n => h n t) atTop (𝓝 (h₀ t)))
    (hg_meas : ∀ n, Measurable (g n))
    (hderiv_meas : ∀ n, Measurable (deriv (f n)))
    (hh_meas : ∀ n, Measurable (h n))
    (hderiv_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ n t, t ∈ Icc (0 : ℝ) 1 → |deriv (f n) t| ≤ C)
    (hh_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ n t, t ∈ Icc (0 : ℝ) 1 → |h n t| ≤ C) :
    (∀ x ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => intervalIntegral.productPrimitive
        (f n) (g n) (deriv (f n)) (h n) x) atTop
        (𝓝 (intervalIntegral.productPrimitive f₀ g₀ (deriv f₀) h₀ x))) ∧
    eVariationOn (intervalIntegral.productPrimitive f₀ g₀ (deriv f₀) h₀)
      (Icc (0 : ℝ) 1) ≤
      liminf (fun n => eVariationOn
        (intervalIntegral.productPrimitive (f n) (g n) (deriv (f n)) (h n))
        (Icc (0 : ℝ) 1)) atTop := by
  constructor
  · intro x hx
    exact productPrimitive_tendsto_of_uniform_variation hV hvar hf hg hderiv hh
      hg_meas hderiv_meas hh_meas hderiv_bound hh_bound hx
  · exact productPrimitive_le_liminf_of_uniform_variation hV hvar hf hg hderiv hh
      hg_meas hderiv_meas hh_meas hderiv_bound hh_bound

end eVariationOn

end
