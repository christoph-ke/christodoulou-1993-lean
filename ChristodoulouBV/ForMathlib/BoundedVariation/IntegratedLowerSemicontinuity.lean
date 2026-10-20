module

public import ChristodoulouBV.ForMathlib.BoundedVariation.LowerSemicontinuity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Measurability and integrated lower semicontinuity of variation

Pointwise continuous families of real functions have lower semicontinuous variation.
Continuity outside a countable parameter set therefore suffices for measurability,
and Fatou's lemma gives the extended-real integral estimate. For the open unit
interval, take `Y := Set.Ioo (0 : ℝ) 1` with `Measure.Subtype.measureSpace`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace intervalIntegral

/-- At a parameter where each factor is pointwise continuous, a uniform bound on the
product integrand makes the integration-by-parts primitive pointwise continuous. -/
theorem continuousAt_productPrimitive_of_bounded_integrand
    {Y : Type*} [TopologicalSpace Y] [FirstCountableTopology Y]
    {f g p h : Y → ℝ → ℝ} {y : Y}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt (fun z => f z t) y)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt (fun z => g z t) y)
    (hp : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt (fun z => p z t) y)
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt (fun z => h z t) y)
    (hq_meas : ∀ z, Measurable (fun t => g z t * p z t + h z t))
    (hq_bound : ∃ C : ℝ, ∀ z t, t ∈ Icc (0 : ℝ) 1 →
      |g z t * p z t + h z t| ≤ C)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (fun z => productPrimitive (f z) (g z) (p z) (h z) x) y := by
  obtain ⟨C, hC⟩ := hq_bound
  have hi : Tendsto
      (fun z => ∫ t in (0 : ℝ)..x, (g z t * p z t + h z t)) (𝓝 y)
      (𝓝 (∫ t in (0 : ℝ)..x, (g y t * p y t + h y t))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (bound := fun _ => C)
    · exact Filter.Eventually.of_forall fun z => (hq_meas z).aestronglyMeasurable.restrict
    · refine Filter.Eventually.of_forall fun z => Filter.Eventually.of_forall fun t ht => ?_
      have htx : t ∈ Icc (0 : ℝ) 1 := by
        rw [uIoc_of_le hx.1] at ht
        exact ⟨ht.1.le, ht.2.trans hx.2⟩
      simpa only [Real.norm_eq_abs] using hC z t htx
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall fun t ht => ?_
      have htx : t ∈ Icc (0 : ℝ) 1 := by
        rw [uIoc_of_le hx.1] at ht
        exact ⟨ht.1.le, ht.2.trans hx.2⟩
      exact (((hg t htx).mul (hp t htx)).add (hh t htx))
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have heq : (fun z => f z x * g z x - f z 0 * g z 0 -
      ∫ t in (0 : ℝ)..x, (g z t * p z t + h z t)) =
      ((fun z => f z x) * (fun z => g z x) -
        (fun z => f z 0) * (fun z => g z 0) -
        (fun z => ∫ t in (0 : ℝ)..x, (g z t * p z t + h z t))) := by
    funext z
    simp only [Pi.mul_apply, Pi.sub_apply]
  change ContinuousAt (fun z => f z x * g z x - f z 0 * g z 0 -
    ∫ t in (0 : ℝ)..x, (g z t * p z t + h z t)) y
  rw [heq]
  exact (((hf x hx).mul (hg x hx)).sub
    ((hf 0 hzero).mul (hg 0 hzero))).sub hi

end intervalIntegral

namespace eVariationOn

/-- If every section of a family is continuous at a parameter, its variation is lower
semicontinuous there. -/
theorem lowerSemicontinuousAt_of_continuousAt_sections
    {Y : Type*} [TopologicalSpace Y] {G : Y → ℝ → ℝ} {y : Y} {s : Set ℝ}
    (hG : ∀ x ∈ s, ContinuousAt (fun z => G z x) y) :
    LowerSemicontinuousAt (fun z => eVariationOn (G z) s) y :=
  fun _ hv => lowerSemicontinuous_aux (fun x hx => hG x hx) hv

/-- A variation function is measurable if its underlying sections are continuous outside
a countable set of parameters. -/
theorem measurable_of_countable_noncontinuous_sections
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [MeasurableSingletonClass Y] {G : Y → ℝ → ℝ} {S : Set Y}
    (hS : S.Countable)
    (hG : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => G z x) y) :
    Measurable (fun y => eVariationOn (G y) (Icc (0 : ℝ) 1)) := by
  apply measurable_of_measurable_on_compl_countable S hS
  have hsc : LowerSemicontinuousOn
      (fun y => eVariationOn (G y) (Icc (0 : ℝ) 1)) Sᶜ := by
    intro y hy
    exact (lowerSemicontinuousAt_of_continuousAt_sections
      (hG y (by simpa only [mem_compl_iff] using hy))).lowerSemicontinuousWithinAt Sᶜ
  exact (lowerSemicontinuous_restrict_iff.mpr hsc).measurable

/-- Integrated lower semicontinuity of variation under pointwise convergence, with
continuity of the limit family outside a countable exceptional set. The integral is
extended-real; no finiteness assumption is made. -/
theorem lintegral_le_liminf_lintegral_of_countable_noncontinuous_sections
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [MeasurableSingletonClass Y] {μ : Measure Y}
    {Gₙ : ℕ → Y → ℝ → ℝ} {G : Y → ℝ → ℝ} {S : Set Y}
    (hS : S.Countable)
    (hGcont : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => G z x) y)
    (hGlim : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => Gₙ n y x) atTop (𝓝 (G y x)))
    (hGₙ_meas : ∀ n, Measurable
      (fun y => eVariationOn (Gₙ n y) (Icc (0 : ℝ) 1))) :
    (∀ y ∉ S, LowerSemicontinuousAt
      (fun z => eVariationOn (G z) (Icc (0 : ℝ) 1)) y) ∧
    Measurable (fun y => eVariationOn (G y) (Icc (0 : ℝ) 1)) ∧
    (∫⁻ y, eVariationOn (G y) (Icc (0 : ℝ) 1) ∂μ) ≤
      liminf (fun n => ∫⁻ y, eVariationOn (Gₙ n y) (Icc (0 : ℝ) 1) ∂μ) atTop := by
  have hcont : ∀ y ∉ S, LowerSemicontinuousAt
      (fun z => eVariationOn (G z) (Icc (0 : ℝ) 1)) y := by
    intro y hy
    exact lowerSemicontinuousAt_of_continuousAt_sections (hGcont y hy)
  have hmeas := measurable_of_countable_noncontinuous_sections hS hGcont
  refine ⟨hcont, hmeas, ?_⟩
  calc
    (∫⁻ y, eVariationOn (G y) (Icc (0 : ℝ) 1) ∂μ) ≤
        ∫⁻ y, liminf (fun n => eVariationOn (Gₙ n y) (Icc (0 : ℝ) 1)) atTop ∂μ :=
      lintegral_mono fun y => le_liminf_of_tendsto_pointwise (hGlim y)
    _ ≤ _ := lintegral_liminf_le hGₙ_meas

/-- A finite lower limit of the approximating integrated variations makes the limiting
integrated variation finite. -/
theorem lintegral_ne_top_of_liminf_lintegral_ne_top
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [MeasurableSingletonClass Y] {μ : Measure Y}
    {Gₙ : ℕ → Y → ℝ → ℝ} {G : Y → ℝ → ℝ} {S : Set Y}
    (hS : S.Countable)
    (hGcont : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => G z x) y)
    (hGlim : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => Gₙ n y x) atTop (𝓝 (G y x)))
    (hGₙ_meas : ∀ n, Measurable
      (fun y => eVariationOn (Gₙ n y) (Icc (0 : ℝ) 1)))
    (hfinite : liminf (fun n => ∫⁻ y,
      eVariationOn (Gₙ n y) (Icc (0 : ℝ) 1) ∂μ) atTop ≠ ∞) :
    (∫⁻ y, eVariationOn (G y) (Icc (0 : ℝ) 1) ∂μ) ≠ ∞ :=
  ne_top_of_le_ne_top hfinite
    (lintegral_le_liminf_lintegral_of_countable_noncontinuous_sections
      hS hGcont hGlim hGₙ_meas).2.2

/-- The integrated form for integration-by-parts primitives. The approximating data have
uniform variation and sup-norm bounds in the integration variable for each parameter;
the limiting integrand has a bound uniform in both variables. No bound on the integrals
of the approximating variations is required. -/
theorem productPrimitive_lintegral_le_liminf
    {Y : Type*} [TopologicalSpace Y] [FirstCountableTopology Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] [MeasurableSingletonClass Y]
    {μ : Measure Y}
    {fₙ gₙ pₙ hₙ : ℕ → Y → ℝ → ℝ} {f g p h : Y → ℝ → ℝ} {S : Set Y}
    (hS : S.Countable)
    (hvar : ∀ y, ∃ V : ℝ≥0∞, V ≠ ∞ ∧
      ∀ n, eVariationOn (gₙ n y) (Icc (0 : ℝ) 1) ≤ V)
    (hf_lim : ∀ y t, t ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => fₙ n y t) atTop (𝓝 (f y t)))
    (hg_lim : ∀ y t, t ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => gₙ n y t) atTop (𝓝 (g y t)))
    (hp_lim : ∀ y t, t ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => pₙ n y t) atTop (𝓝 (p y t)))
    (hh_lim : ∀ y t, t ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => hₙ n y t) atTop (𝓝 (h y t)))
    (hgₙ_meas : ∀ n y, Measurable (gₙ n y))
    (hpₙ_meas : ∀ n y, Measurable (pₙ n y))
    (hhₙ_meas : ∀ n y, Measurable (hₙ n y))
    (hpₙ_bound : ∀ y, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n t, t ∈ Icc (0 : ℝ) 1 → |pₙ n y t| ≤ C)
    (hhₙ_bound : ∀ y, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n t, t ∈ Icc (0 : ℝ) 1 → |hₙ n y t| ≤ C)
    (hg_meas : ∀ y, Measurable (g y))
    (hp_meas : ∀ y, Measurable (p y))
    (hh_meas : ∀ y, Measurable (h y))
    (hg_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y t, t ∈ Icc (0 : ℝ) 1 → |g y t| ≤ C)
    (hp_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y t, t ∈ Icc (0 : ℝ) 1 → |p y t| ≤ C)
    (hh_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y t, t ∈ Icc (0 : ℝ) 1 → |h y t| ≤ C)
    (hf_cont : ∀ y ∉ S, ∀ t ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => f z t) y)
    (hg_cont : ∀ y ∉ S, ∀ t ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => g z t) y)
    (hp_cont : ∀ y ∉ S, ∀ t ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => p z t) y)
    (hh_cont : ∀ y ∉ S, ∀ t ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => h z t) y)
    (hFₙ_meas : ∀ n, Measurable (fun y => eVariationOn
      (intervalIntegral.productPrimitive (fₙ n y) (gₙ n y) (pₙ n y) (hₙ n y))
      (Icc (0 : ℝ) 1))) :
    (∀ y ∉ S, LowerSemicontinuousAt (fun z => eVariationOn
      (intervalIntegral.productPrimitive (f z) (g z) (p z) (h z))
      (Icc (0 : ℝ) 1)) y) ∧
    Measurable (fun y => eVariationOn
      (intervalIntegral.productPrimitive (f y) (g y) (p y) (h y))
      (Icc (0 : ℝ) 1)) ∧
    (∫⁻ y, eVariationOn
      (intervalIntegral.productPrimitive (f y) (g y) (p y) (h y))
      (Icc (0 : ℝ) 1) ∂μ) ≤
      liminf (fun n => ∫⁻ y, eVariationOn
        (intervalIntegral.productPrimitive (fₙ n y) (gₙ n y) (pₙ n y) (hₙ n y))
        (Icc (0 : ℝ) 1) ∂μ) atTop := by
  obtain ⟨Cg, hCg₀, hCg⟩ := hg_bound
  obtain ⟨Cp, _, hCp⟩ := hp_bound
  obtain ⟨Ch, _, hCh⟩ := hh_bound
  have hq_bound : ∃ C : ℝ, ∀ y t, t ∈ Icc (0 : ℝ) 1 →
      |g y t * p y t + h y t| ≤ C := by
    refine ⟨Cg * Cp + Ch, fun y t ht => ?_⟩
    calc
      |g y t * p y t + h y t| ≤ |g y t * p y t| + |h y t| := abs_add_le _ _
      _ = |g y t| * |p y t| + |h y t| := by rw [abs_mul]
      _ ≤ Cg * Cp + Ch :=
        add_le_add (mul_le_mul (hCg y t ht) (hCp y t ht) (abs_nonneg _) hCg₀)
          (hCh y t ht)
  refine lintegral_le_liminf_lintegral_of_countable_noncontinuous_sections
    hS ?_ ?_ hFₙ_meas
  · intro y hy t ht
    exact intervalIntegral.continuousAt_productPrimitive_of_bounded_integrand
      (hf_cont y hy) (hg_cont y hy) (hp_cont y hy) (hh_cont y hy)
      (fun z => ((hg_meas z).mul (hp_meas z)).add (hh_meas z))
      hq_bound ht
  · intro y t ht
    obtain ⟨V, hV, hvar_y⟩ := hvar y
    have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    exact intervalIntegral.tendsto_productPrimitive_of_bounded_integrand
      (hf_lim y) (hg_lim y) (hp_lim y) (hh_lim y)
      (fun n => ((hgₙ_meas n y).mul (hpₙ_meas n y)).add (hhₙ_meas n y))
      (intervalIntegral.exists_bound_product_of_uniform_variation hV hvar_y
        (hg_lim y 0 hzero) (hpₙ_bound y) (hhₙ_bound y)) ht

end eVariationOn

end
