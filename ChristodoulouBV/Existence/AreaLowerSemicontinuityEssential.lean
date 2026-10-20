module

public import ChristodoulouBV.Existence.AreaLowerSemicontinuity
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Essential bounds in Christodoulou's Lemmas 6.1 and 6.2

The source's `L∞` hypotheses are bounds almost everywhere in the integration
variable. The Stieltjes quantities here are, as in the source proof, the
pointwise variations of the integration-by-parts primitives. In particular,
isolated values of a BV function contribute to the variation.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

attribute [local instance] Measure.Subtype.measureSpace

namespace ChristodoulouBV

private theorem tendsto_integral_of_ae_bounded
    {q : ℕ → ℝ → ℝ} {r : ℝ → ℝ}
    (hq_meas : ∀ n, Measurable (q n))
    (hq_bound : ∃ C : ℝ, ∀ n, ∀ᵐ t ∂volume,
      t ∈ Icc (0 : ℝ) 1 → |q n t| ≤ C)
    (hq_lim : ∀ t ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => q n t) atTop (𝓝 (r t)))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..x, q n t) atTop
      (𝓝 (∫ t in (0 : ℝ)..x, r t)) := by
  obtain ⟨C, hC⟩ := hq_bound
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (bound := fun _ => C)
  · exact Filter.Eventually.of_forall fun n => (hq_meas n).aestronglyMeasurable.restrict
  · refine Filter.Eventually.of_forall fun n => ?_
    filter_upwards [hC n] with t ht htx
    have htIcc : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le hx.1] at htx
      exact ⟨htx.1.le, htx.2.trans hx.2⟩
    simpa only [Real.norm_eq_abs] using ht htIcc
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun t ht => ?_
    have htx : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le hx.1] at ht
      exact ⟨ht.1.le, ht.2.trans hx.2⟩
    exact hq_lim t htx

private theorem productPrimitive_congr_on_Icc {f g g' p h : ℝ → ℝ}
    (hgg' : EqOn g g' (Icc (0 : ℝ) 1)) :
    EqOn (intervalIntegral.productPrimitive f g p h)
      (intervalIntegral.productPrimitive f g' p h) (Icc (0 : ℝ) 1) := by
  intro x hx
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  simp only [intervalIntegral.productPrimitive, hgg' hx, hgg' hzero]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hx.1] at ht
  change g t * p t + h t = g' t * p t + h t
  rw [hgg' ⟨ht.1, ht.2.trans hx.2⟩]

/-- The primitives in Lemma 6.1 converge at every point, using
essential bounds for the ordinary integral. The all-point differentiability
premises identify `deriv` with the printed classical derivatives. -/
theorem lemma6_1_limit
    {fₙ gₙ hₙ : ℕ → ℝ → ℝ} {f g h : ℝ → ℝ}
    (_hfₙ_diff : ∀ n, ∀ x ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (fₙ n) x)
    (_hf_diff : ∀ x ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ f x)
    (hf_lim : ∀ x ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => fₙ n x) atTop (𝓝 (f x)))
    (hf_deriv_lim : ∀ x ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => deriv (fₙ n) x) atTop (𝓝 (deriv f x)))
    (hf_deriv_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ n, ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → |deriv (fₙ n) x| ≤ C)
    (hg_var : ∃ V : ℝ≥0∞, V ≠ ∞ ∧
      ∀ n, eVariationOn (gₙ n) (Icc (0 : ℝ) 1) ≤ V)
    (hg_lim : ∀ x ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => gₙ n x) atTop (𝓝 (g x)))
    (hh_meas : ∀ n, Measurable (hₙ n))
    (hh_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ n, ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → |hₙ n x| ≤ C)
    (hh_lim : ∀ x ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => hₙ n x) atTop (𝓝 (h x)))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => intervalIntegral.productPrimitive
      (fₙ n) (gₙ n) (deriv (fₙ n)) (hₙ n) x) atTop
      (𝓝 (intervalIntegral.productPrimitive f g (deriv f) h x)) := by
  let hab : (0 : ℝ) ≤ 1 := by norm_num
  let gₙ' : ℕ → ℝ → ℝ := fun n => Function.extendIcc (gₙ n) hab
  let g' : ℝ → ℝ := Function.extendIcc g hab
  obtain ⟨V, hV, hvar⟩ := hg_var
  have hvar' : ∀ n, eVariationOn (gₙ' n) (Icc (0 : ℝ) 1) ≤ V := by
    intro n
    rw [eVariationOn.congr (fun t ht =>
      BoundedVariationOn.extendIcc_of_mem hab ht)]
    exact hvar n
  have hg_bound := BoundedVariationOn.exists_uniform_bound_of_variation_le_of_tendsto_left
    hV hvar (hg_lim 0 (by norm_num))
  obtain ⟨Cg, hCg⟩ := hg_bound
  obtain ⟨Cp, hCp₀, hCp⟩ := hf_deriv_bound
  obtain ⟨Ch, _, hCh⟩ := hh_bound
  have hq_meas : ∀ n, Measurable (fun t =>
      gₙ' n t * deriv (fₙ n) t + hₙ n t) := by
    intro n
    have hgm : Measurable (gₙ' n) :=
      (BoundedVariationOn.extendIcc_boundedVariationOn hab
        (ne_top_of_le_ne_top hV (hvar n))).measurable
    exact (hgm.mul (measurable_deriv (fₙ n))).add (hh_meas n)
  have hq_bound : ∃ C : ℝ, ∀ n, ∀ᵐ t ∂volume,
      t ∈ Icc (0 : ℝ) 1 →
      |gₙ' n t * deriv (fₙ n) t + hₙ n t| ≤ C := by
    refine ⟨Cg * Cp + Ch, fun n => ?_⟩
    filter_upwards [hCp n, hCh n] with t hp hh ht
    have hg_bound' : |gₙ' n t| ≤ Cg := by
      simpa only [gₙ', BoundedVariationOn.extendIcc_of_mem hab ht] using hCg n t ht
    calc
      |gₙ' n t * deriv (fₙ n) t + hₙ n t| ≤
          |gₙ' n t * deriv (fₙ n) t| + |hₙ n t| := abs_add_le _ _
      _ = |gₙ' n t| * |deriv (fₙ n) t| + |hₙ n t| := by rw [abs_mul]
      _ ≤ Cg * Cp + Ch :=
        add_le_add (mul_le_mul hg_bound' (hp ht) (abs_nonneg _) (by
          have hz : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
          exact (abs_nonneg (gₙ 0 0)).trans (hCg 0 0 hz))) (hh ht)
  have hq_lim : ∀ t ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => gₙ' n t * deriv (fₙ n) t + hₙ n t) atTop
        (𝓝 (g' t * deriv f t + h t)) := by
    intro t ht
    have hg' : Tendsto (fun n => gₙ' n t) atTop (𝓝 (g' t)) := by
      simpa only [gₙ', g', BoundedVariationOn.extendIcc_of_mem hab ht]
        using hg_lim t ht
    exact ((hg'.mul (hf_deriv_lim t ht)).add (hh_lim t ht))
  have hi := tendsto_integral_of_ae_bounded hq_meas hq_bound hq_lim hx
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hprimₙ (n : ℕ) :
      intervalIntegral.productPrimitive (fₙ n) (gₙ n) (deriv (fₙ n)) (hₙ n) x =
      intervalIntegral.productPrimitive (fₙ n) (gₙ' n) (deriv (fₙ n)) (hₙ n) x :=
    productPrimitive_congr_on_Icc
      (fun t ht => (BoundedVariationOn.extendIcc_of_mem hab ht).symm) hx
  have hprim : intervalIntegral.productPrimitive f g (deriv f) h x =
      intervalIntegral.productPrimitive f g' (deriv f) h x :=
    productPrimitive_congr_on_Icc
      (fun t ht => (BoundedVariationOn.extendIcc_of_mem hab ht).symm) hx
  simp_rw [hprimₙ]
  rw [hprim]
  simpa only [intervalIntegral.productPrimitive] using
    (((hf_lim x hx).mul (by
      simpa only [gₙ', g', BoundedVariationOn.extendIcc_of_mem hab hx]
        using hg_lim x hx)).sub
      ((hf_lim 0 hzero).mul (by
        simpa only [gₙ', g', BoundedVariationOn.extendIcc_of_mem hab hzero]
          using hg_lim 0 hzero))).sub hi

/-- Lemma 6.1 with the printed all-point convergence premises and essential
`L∞` bounds. The displayed `Fₙ` and `F` are variations of the source's
pointwise integration-by-parts primitives. -/
theorem lemma6_1
    {fₙ gₙ hₙ : ℕ → ℝ → ℝ} {f g h : ℝ → ℝ}
    (hfₙ_diff : ∀ n, ∀ x ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (fₙ n) x)
    (hf_diff : ∀ x ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ f x)
    (hf_lim : ∀ x ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => fₙ n x) atTop (𝓝 (f x)))
    (hf_deriv_lim : ∀ x ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => deriv (fₙ n) x) atTop (𝓝 (deriv f x)))
    (hf_deriv_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ n, ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → |deriv (fₙ n) x| ≤ C)
    (hg_var : ∃ V : ℝ≥0∞, V ≠ ∞ ∧
      ∀ n, eVariationOn (gₙ n) (Icc (0 : ℝ) 1) ≤ V)
    (hg_lim : ∀ x ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => gₙ n x) atTop (𝓝 (g x)))
    (hh_meas : ∀ n, Measurable (hₙ n))
    (hh_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ n, ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → |hₙ n x| ≤ C)
    (hh_lim : ∀ x ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => hₙ n x) atTop (𝓝 (h x))) :
    eVariationOn (intervalIntegral.productPrimitive f g (deriv f) h)
      (Icc (0 : ℝ) 1) ≤
      liminf (fun n => eVariationOn
        (intervalIntegral.productPrimitive (fₙ n) (gₙ n) (deriv (fₙ n)) (hₙ n))
        (Icc (0 : ℝ) 1)) atTop :=
  eVariationOn.le_liminf_of_tendsto_pointwise fun _ hx =>
    lemma6_1_limit hfₙ_diff hf_diff hf_lim hf_deriv_lim hf_deriv_bound
      hg_var hg_lim hh_meas hh_bound hh_lim hx

private theorem continuousAt_integral_of_ae_bounded
    {Y : Type*} [TopologicalSpace Y] [FirstCountableTopology Y]
    {q : Y → ℝ → ℝ} {y : Y}
    (hq_meas : ∀ z, Measurable (q z))
    (hq_bound : ∃ C : ℝ, ∀ z, ∀ᵐ t ∂volume,
      t ∈ Icc (0 : ℝ) 1 → |q z t| ≤ C)
    (hq_cont : ∀ t ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => q z t) y)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (fun z => ∫ t in (0 : ℝ)..x, q z t) y := by
  obtain ⟨C, hC⟩ := hq_bound
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (bound := fun _ => C)
  · exact Filter.Eventually.of_forall fun z => (hq_meas z).aestronglyMeasurable.restrict
  · refine Filter.Eventually.of_forall fun z => ?_
    filter_upwards [hC z] with t ht htx
    have htIcc : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le hx.1] at htx
      exact ⟨htx.1.le, htx.2.trans hx.2⟩
    simpa only [Real.norm_eq_abs] using ht htIcc
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun t ht => ?_
    have htx : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le hx.1] at ht
      exact ⟨ht.1.le, ht.2.trans hx.2⟩
    exact hq_cont t htx

/-- The variation inequality in Lemma 6.2 at each fixed transverse parameter.
The variation and essential bounds of the approximating sections may depend on
the parameter. -/
theorem lemma6_2_pointwise
    {fₙ gₙ hₙ : ℕ → Ioo (0 : ℝ) 1 → ℝ → ℝ}
    {f g h : Ioo (0 : ℝ) 1 → ℝ → ℝ}
    (hfₙ_diff : ∀ n y, ∀ x ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (fₙ n y) x)
    (hf_diff : ∀ y, ∀ x ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (f y) x)
    (hf_lim : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => fₙ n y x) atTop (𝓝 (f y x)))
    (hf_deriv_lim : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => deriv (fₙ n y) x) atTop (𝓝 (deriv (f y) x)))
    (hf_deriv_bound : ∀ y, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n, ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → |deriv (fₙ n y) x| ≤ C)
    (hg_var : ∀ y, ∃ V : ℝ≥0∞, V ≠ ∞ ∧
      ∀ n, eVariationOn (gₙ n y) (Icc (0 : ℝ) 1) ≤ V)
    (hg_lim : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => gₙ n y x) atTop (𝓝 (g y x)))
    (hhₙ_meas : ∀ n y, Measurable (hₙ n y))
    (hhₙ_bound : ∀ y, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n, ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → |hₙ n y x| ≤ C)
    (hh_lim : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => hₙ n y x) atTop (𝓝 (h y x)))
    (y : Ioo (0 : ℝ) 1) :
    eVariationOn (intervalIntegral.productPrimitive
      (f y) (g y) (deriv (f y)) (h y)) (Icc (0 : ℝ) 1) ≤
      liminf (fun n => eVariationOn
        (intervalIntegral.productPrimitive
          (fₙ n y) (gₙ n y) (deriv (fₙ n y)) (hₙ n y))
        (Icc (0 : ℝ) 1)) atTop :=
  lemma6_1 (fun n => hfₙ_diff n y) (hf_diff y) (hf_lim y)
    (hf_deriv_lim y) (hf_deriv_bound y) (hg_var y) (hg_lim y)
    (fun n => hhₙ_meas n y) (hhₙ_bound y) (hh_lim y)

/-- Measurability of the transverse variation from essential bounds on every
section, uniform in the parameter, and the source's common countable set of
exceptional parameters. -/
theorem lemma6_2_measurable_of_uniform_section_ae_bounds
    {f g h : Ioo (0 : ℝ) 1 → ℝ → ℝ}
    {S : Set (Ioo (0 : ℝ) 1)}
    (hS : S.Countable)
    (hg_meas : ∀ y, Measurable (g y))
    (hh_meas : ∀ y, Measurable (h y))
    (hg_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y, ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → |g y x| ≤ C)
    (hf_deriv_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y, ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → |deriv (f y) x| ≤ C)
    (hh_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y, ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → |h y x| ≤ C)
    (hf_cont : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => f z x) y)
    (hg_cont : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => g z x) y)
    (hf_deriv_cont : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => deriv (f z) x) y)
    (hh_cont : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => h z x) y) :
    (∀ y ∉ S, LowerSemicontinuousAt (fun z => eVariationOn
      (intervalIntegral.productPrimitive (f z) (g z) (deriv (f z)) (h z))
      (Icc (0 : ℝ) 1)) y) ∧
    Measurable (fun y => eVariationOn
      (intervalIntegral.productPrimitive (f y) (g y) (deriv (f y)) (h y))
      (Icc (0 : ℝ) 1)) := by
  obtain ⟨Cg, hCg₀, hCg⟩ := hg_bound
  obtain ⟨Cp, _, hCp⟩ := hf_deriv_bound
  obtain ⟨Ch, _, hCh⟩ := hh_bound
  have hq_bound : ∃ C : ℝ, ∀ y, ∀ᵐ x ∂volume,
      x ∈ Icc (0 : ℝ) 1 →
      |g y x * deriv (f y) x + h y x| ≤ C := by
    refine ⟨Cg * Cp + Ch, fun y => ?_⟩
    filter_upwards [hCg y, hCp y, hCh y] with x hg hp hh hx
    calc
      |g y x * deriv (f y) x + h y x| ≤
          |g y x * deriv (f y) x| + |h y x| := abs_add_le _ _
      _ = |g y x| * |deriv (f y) x| + |h y x| := by rw [abs_mul]
      _ ≤ Cg * Cp + Ch :=
        add_le_add (mul_le_mul (hg hx) (hp hx) (abs_nonneg _) hCg₀) (hh hx)
  have hGcont : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => intervalIntegral.productPrimitive
        (f z) (g z) (deriv (f z)) (h z) x) y := by
    intro y hy x hx
    have hq_meas : ∀ z, Measurable (fun t =>
        g z t * deriv (f z) t + h z t) := by
      intro z
      exact ((hg_meas z).mul (measurable_deriv (f z))).add (hh_meas z)
    have hq_cont : ∀ t ∈ Icc (0 : ℝ) 1,
        ContinuousAt (fun z => g z t * deriv (f z) t + h z t) y := by
      intro t ht
      exact ((hg_cont y hy t ht).mul (hf_deriv_cont y hy t ht)).add
        (hh_cont y hy t ht)
    have hi := continuousAt_integral_of_ae_bounded hq_meas hq_bound hq_cont hx
    have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have hprod : ContinuousAt (fun z =>
        f z x * g z x - f z 0 * g z 0 -
          ∫ t in (0 : ℝ)..x, (g z t * deriv (f z) t + h z t)) y := by
      exact (((hf_cont y hy x hx).mul (hg_cont y hy x hx)).sub
        ((hf_cont y hy 0 hzero).mul (hg_cont y hy 0 hzero))).sub hi
    simpa only [intervalIntegral.productPrimitive] using hprod
  constructor
  · intro y hy
    exact eVariationOn.lowerSemicontinuousAt_of_continuousAt_sections (hGcont y hy)
  · exact eVariationOn.measurable_of_countable_noncontinuous_sections hS hGcont

/-- The inequality from the author ruling on the ordinary-integral
reading of Lemma 6.2, under uniform essential bounds on *every* limit section. This is an intermediate result: a literal rectangle `L∞` bound only
controls almost every transverse section. -/
theorem lemma6_2_of_uniform_section_ae_bounds
    {fₙ gₙ hₙ : ℕ → Ioo (0 : ℝ) 1 → ℝ → ℝ}
    {f g h : Ioo (0 : ℝ) 1 → ℝ → ℝ}
    {S : Set (Ioo (0 : ℝ) 1)}
    (hS : S.Countable)
    (hfₙ_diff : ∀ n y, ∀ x ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (fₙ n y) x)
    (hf_diff : ∀ y, ∀ x ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (f y) x)
    (hf_lim : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => fₙ n y x) atTop (𝓝 (f y x)))
    (hf_deriv_lim : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => deriv (fₙ n y) x) atTop (𝓝 (deriv (f y) x)))
    (hf_deriv_bound : ∀ y, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n, ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → |deriv (fₙ n y) x| ≤ C)
    (hg_var : ∀ y, ∃ V : ℝ≥0∞, V ≠ ∞ ∧
      ∀ n, eVariationOn (gₙ n y) (Icc (0 : ℝ) 1) ≤ V)
    (hg_lim : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => gₙ n y x) atTop (𝓝 (g y x)))
    (hhₙ_meas : ∀ n y, Measurable (hₙ n y))
    (hhₙ_bound : ∀ y, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n, ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → |hₙ n y x| ≤ C)
    (hh_lim : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => hₙ n y x) atTop (𝓝 (h y x)))
    (hFₙ_meas : ∀ n, Measurable (fun y : Ioo (0 : ℝ) 1 =>
      eVariationOn (intervalIntegral.productPrimitive
        (fₙ n y) (gₙ n y) (deriv (fₙ n y)) (hₙ n y)) (Icc (0 : ℝ) 1)))
    (_hFₙ_integrable : ∀ n, (∫⁻ y : Ioo (0 : ℝ) 1,
      eVariationOn (intervalIntegral.productPrimitive
        (fₙ n y) (gₙ n y) (deriv (fₙ n y)) (hₙ n y)) (Icc (0 : ℝ) 1)) ≠ ∞)
    (_hf_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y, ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → |f y x| ≤ C)
    (hf_deriv_bound_lim : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y, ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → |deriv (f y) x| ≤ C)
    (hg_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y, ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → |g y x| ≤ C)
    (hh_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y, ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → |h y x| ≤ C)
    (hh_meas : ∀ y, Measurable (h y))
    (hf_cont : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => f z x) y)
    (hf_deriv_cont : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => deriv (f z) x) y)
    (hg_cont : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => g z x) y)
    (hh_cont : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => h z x) y) :
    Measurable (fun y : Ioo (0 : ℝ) 1 =>
      eVariationOn (intervalIntegral.productPrimitive
        (f y) (g y) (deriv (f y)) (h y)) (Icc (0 : ℝ) 1)) ∧
    (∫⁻ y : Ioo (0 : ℝ) 1,
      eVariationOn (intervalIntegral.productPrimitive
        (f y) (g y) (deriv (f y)) (h y)) (Icc (0 : ℝ) 1)) ≤
      liminf (fun n => ∫⁻ y : Ioo (0 : ℝ) 1,
        eVariationOn (intervalIntegral.productPrimitive
          (fₙ n y) (gₙ n y) (deriv (fₙ n y)) (hₙ n y))
          (Icc (0 : ℝ) 1)) atTop := by
  let hab : (0 : ℝ) ≤ 1 := by norm_num
  let gₙ' : ℕ → Ioo (0 : ℝ) 1 → ℝ → ℝ :=
    fun n y => Function.extendIcc (gₙ n y) hab
  let g' : Ioo (0 : ℝ) 1 → ℝ → ℝ :=
    fun y => Function.extendIcc (g y) hab
  have hgₙ_meas' : ∀ n y, Measurable (gₙ' n y) := by
    intro n y
    obtain ⟨V, hV, hvar⟩ := hg_var y
    exact (BoundedVariationOn.extendIcc_boundedVariationOn hab
      (ne_top_of_le_ne_top hV (hvar n))).measurable
  have hg_meas' : ∀ y, Measurable (g' y) := by
    intro y
    apply measurable_of_tendsto_metrizable (fun n => hgₙ_meas' n y)
    rw [tendsto_pi_nhds]
    intro x
    have hx := (Set.projIcc (0 : ℝ) 1 hab x).property
    simpa only [gₙ', g', Function.extendIcc] using hg_lim y _ hx
  obtain ⟨Cg, hCg₀, hCg⟩ := hg_bound
  have hg_bound' : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y, ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → |g' y x| ≤ C := by
    refine ⟨Cg, hCg₀, fun y => ?_⟩
    filter_upwards [hCg y] with x hx hxt
    simpa only [g', BoundedVariationOn.extendIcc_of_mem hab hxt] using hx hxt
  have hg_cont' : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => g' z x) y := by
    intro y hy x hx
    simpa only [g', BoundedVariationOn.extendIcc_of_mem hab hx]
      using hg_cont y hy x hx
  have hF_eq : (fun y : Ioo (0 : ℝ) 1 =>
      eVariationOn (intervalIntegral.productPrimitive
        (f y) (g y) (deriv (f y)) (h y)) (Icc (0 : ℝ) 1)) =
      (fun y : Ioo (0 : ℝ) 1 =>
        eVariationOn (intervalIntegral.productPrimitive
          (f y) (g' y) (deriv (f y)) (h y)) (Icc (0 : ℝ) 1)) := by
    funext y
    exact eVariationOn.congr (productPrimitive_congr_on_Icc fun x hx =>
      (BoundedVariationOn.extendIcc_of_mem hab hx).symm)
  have hF_meas : Measurable (fun y : Ioo (0 : ℝ) 1 =>
      eVariationOn (intervalIntegral.productPrimitive
        (f y) (g y) (deriv (f y)) (h y)) (Icc (0 : ℝ) 1)) := by
    rw [hF_eq]
    exact (lemma6_2_measurable_of_uniform_section_ae_bounds hS hg_meas' hh_meas hg_bound'
      hf_deriv_bound_lim hh_bound hf_cont hg_cont' hf_deriv_cont hh_cont).2
  constructor
  · exact hF_meas
  · calc
      (∫⁻ y : Ioo (0 : ℝ) 1,
        eVariationOn (intervalIntegral.productPrimitive
          (f y) (g y) (deriv (f y)) (h y)) (Icc (0 : ℝ) 1)) ≤
          ∫⁻ y : Ioo (0 : ℝ) 1,
            liminf (fun n => eVariationOn
              (intervalIntegral.productPrimitive
                (fₙ n y) (gₙ n y) (deriv (fₙ n y)) (hₙ n y))
              (Icc (0 : ℝ) 1)) atTop :=
        lintegral_mono fun y =>
          lemma6_2_pointwise hfₙ_diff hf_diff hf_lim hf_deriv_lim
            hf_deriv_bound hg_var hg_lim hhₙ_meas hhₙ_bound hh_lim y
      _ ≤ _ := lintegral_liminf_le hFₙ_meas

end ChristodoulouBV

end
