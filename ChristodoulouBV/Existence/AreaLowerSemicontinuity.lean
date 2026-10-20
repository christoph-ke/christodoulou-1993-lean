module

public import ChristodoulouBV.ForMathlib.BoundedVariation.IntegratedLowerSemicontinuity
public import ChristodoulouBV.ForMathlib.BoundedVariation.LocalStieltjes
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Lower semicontinuity in Lemmas 6.1 and 6.2

We use the integration-by-parts primitive `intervalIntegral.productPrimitive` for the
source expression `∫₀ˣ (f dg - h dx)`. Its variation on the **closed** interval is the
Stieltjes total variation in these statements. The values of a BV function at an
isolated spike are retained. The vector measure `localStieltjes` instead uses
one-sided limits and can discard such a spike, so its variation is only known to be
bounded above by pointwise variation without an additional representative convention.

The functions are represented on `ℝ` for Lean's derivative and interval integral.
Only values on `[0,1]` enter the conclusions. Each BV section is constantly extended
outside `[0,1]` before applying the established measurable primitive theorems. The `hₙ`
are measurable representatives of their source `L∞` functions.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

attribute [local instance] Measure.Subtype.measureSpace

namespace ChristodoulouBV

private theorem measurable_extendIcc_of_bv {g : ℝ → ℝ}
    (hg : BoundedVariationOn g (Icc (0 : ℝ) 1)) :
    Measurable (Function.extendIcc g (by norm_num : (0 : ℝ) ≤ 1)) :=
  (BoundedVariationOn.extendIcc_boundedVariationOn (by norm_num) hg).measurable

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

/-- Lemma 6.1 for Borel, uniformly pointwise bounded representatives. This
retains the printed all-point differentiability and derivative convergence
premises. `F` is the pointwise variation of the integration-by-parts primitive,
including the exact values at both endpoints and at interior jumps. -/
theorem lemma6_1_of_bounded_representatives
    {fₙ gₙ hₙ : ℕ → ℝ → ℝ} {f g h : ℝ → ℝ}
    (_hfₙ_diff : ∀ n, ∀ x ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (fₙ n) x)
    (_hf_diff : ∀ x ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ f x)
    (hf_lim : ∀ x ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => fₙ n x) atTop (𝓝 (f x)))
    (hf_deriv_lim : ∀ x ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => deriv (fₙ n) x) atTop (𝓝 (deriv f x)))
    (hf_deriv_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ n x, x ∈ Icc (0 : ℝ) 1 → |deriv (fₙ n) x| ≤ C)
    (hg_var : ∃ V : ℝ≥0∞, V ≠ ∞ ∧
      ∀ n, eVariationOn (gₙ n) (Icc (0 : ℝ) 1) ≤ V)
    (hg_lim : ∀ x ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => gₙ n x) atTop (𝓝 (g x)))
    (hh_meas : ∀ n, Measurable (hₙ n))
    (hh_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ n x, x ∈ Icc (0 : ℝ) 1 → |hₙ n x| ≤ C)
    (hh_lim : ∀ x ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => hₙ n x) atTop (𝓝 (h x))) :
    eVariationOn (intervalIntegral.productPrimitive f g (deriv f) h)
      (Icc (0 : ℝ) 1) ≤
      liminf (fun n => eVariationOn
        (intervalIntegral.productPrimitive (fₙ n) (gₙ n) (deriv (fₙ n)) (hₙ n))
        (Icc (0 : ℝ) 1)) atTop := by
  let hab : (0 : ℝ) ≤ 1 := by norm_num
  let gₙ' : ℕ → ℝ → ℝ := fun n => Function.extendIcc (gₙ n) hab
  let g' : ℝ → ℝ := Function.extendIcc g hab
  obtain ⟨V, hV, hvar⟩ := hg_var
  have hvar' : ∀ n, eVariationOn (gₙ' n) (Icc (0 : ℝ) 1) ≤ V := by
    intro n
    rw [eVariationOn.congr (fun x hx =>
      BoundedVariationOn.extendIcc_of_mem hab hx)]
    exact hvar n
  have hg_lim' : ∀ x ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => gₙ' n x) atTop (𝓝 (g' x)) := by
    intro x hx
    simpa only [gₙ', g', BoundedVariationOn.extendIcc_of_mem hab hx] using hg_lim x hx
  have hg_meas' : ∀ n, Measurable (gₙ' n) := by
    intro n
    exact measurable_extendIcc_of_bv
      (ne_top_of_le_ne_top hV (hvar n))
  have hresult := eVariationOn.productPrimitive_deriv_tendsto_and_variation_le_liminf
    hV hvar' hf_lim hg_lim' hf_deriv_lim hh_lim hg_meas'
    (fun n => measurable_deriv (fₙ n)) hh_meas hf_deriv_bound hh_bound
  have hprim : EqOn (intervalIntegral.productPrimitive f g (deriv f) h)
      (intervalIntegral.productPrimitive f g' (deriv f) h) (Icc (0 : ℝ) 1) :=
    productPrimitive_congr_on_Icc fun x hx =>
      (BoundedVariationOn.extendIcc_of_mem hab hx).symm
  have hprimₙ (n : ℕ) : EqOn
      (intervalIntegral.productPrimitive (fₙ n) (gₙ n) (deriv (fₙ n)) (hₙ n))
      (intervalIntegral.productPrimitive (fₙ n) (gₙ' n) (deriv (fₙ n)) (hₙ n))
      (Icc (0 : ℝ) 1) :=
    productPrimitive_congr_on_Icc fun x hx =>
      (BoundedVariationOn.extendIcc_of_mem hab hx).symm
  rw [eVariationOn.congr hprim]
  have heqₙ : (fun n => eVariationOn
      (intervalIntegral.productPrimitive (fₙ n) (gₙ n) (deriv (fₙ n)) (hₙ n))
      (Icc (0 : ℝ) 1)) =
      (fun n => eVariationOn
        (intervalIntegral.productPrimitive (fₙ n) (gₙ' n) (deriv (fₙ n)) (hₙ n))
        (Icc (0 : ℝ) 1)) := by
    funext n
    exact eVariationOn.congr (hprimₙ n)
  rw [heqₙ]
  exact hresult.2

/-- The pointwise transverse inequality in Lemma 6.2 is Lemma 6.1 on each
fixed `y` section. Section bounds may depend on `y`. -/
theorem lemma6_2_pointwise_of_bounded_representatives
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
      ∀ n x, x ∈ Icc (0 : ℝ) 1 → |deriv (fₙ n y) x| ≤ C)
    (hg_var : ∀ y, ∃ V : ℝ≥0∞, V ≠ ∞ ∧
      ∀ n, eVariationOn (gₙ n y) (Icc (0 : ℝ) 1) ≤ V)
    (hg_lim : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => gₙ n y x) atTop (𝓝 (g y x)))
    (hhₙ_meas : ∀ n y, Measurable (hₙ n y))
    (hhₙ_bound : ∀ y, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n x, x ∈ Icc (0 : ℝ) 1 → |hₙ n y x| ≤ C)
    (hh_lim : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => hₙ n y x) atTop (𝓝 (h y x)))
    (y : Ioo (0 : ℝ) 1) :
    eVariationOn (intervalIntegral.productPrimitive (f y) (g y) (deriv (f y)) (h y))
      (Icc (0 : ℝ) 1) ≤
      liminf (fun n => eVariationOn
        (intervalIntegral.productPrimitive (fₙ n y) (gₙ n y)
          (deriv (fₙ n y)) (hₙ n y)) (Icc (0 : ℝ) 1)) atTop :=
  lemma6_1_of_bounded_representatives (fun n => hfₙ_diff n y) (hf_diff y)
    (hf_lim y) (hf_deriv_lim y)
    (hf_deriv_bound y) (hg_var y) (hg_lim y) (fun n => hhₙ_meas n y)
    (hhₙ_bound y) (hh_lim y)

/-- The limit Stieltjes variation is lower semicontinuous away from the common
countable exceptional set, hence measurable on the open parameter interval. -/
theorem lemma6_2_measurable_of_bounded_representatives
    {f g h : Ioo (0 : ℝ) 1 → ℝ → ℝ}
    {S : Set (Ioo (0 : ℝ) 1)}
    (hS : S.Countable)
    (hg_meas : ∀ y, Measurable (g y))
    (hh_meas : ∀ y, Measurable (h y))
    (hg_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y x, x ∈ Icc (0 : ℝ) 1 → |g y x| ≤ C)
    (hf_deriv_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y x, x ∈ Icc (0 : ℝ) 1 → |deriv (f y) x| ≤ C)
    (hh_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y x, x ∈ Icc (0 : ℝ) 1 → |h y x| ≤ C)
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
  have hq_bound : ∃ C : ℝ, ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      |g y x * deriv (f y) x + h y x| ≤ C := by
    refine ⟨Cg * Cp + Ch, fun y x hx => ?_⟩
    calc
      |g y x * deriv (f y) x + h y x| ≤
          |g y x * deriv (f y) x| + |h y x| := abs_add_le _ _
      _ = |g y x| * |deriv (f y) x| + |h y x| := by rw [abs_mul]
      _ ≤ Cg * Cp + Ch :=
        add_le_add (mul_le_mul (hCg y x hx) (hCp y x hx) (abs_nonneg _) hCg₀)
          (hCh y x hx)
  have hGcont : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => intervalIntegral.productPrimitive
        (f z) (g z) (deriv (f z)) (h z) x) y := by
    intro y hy x hx
    exact intervalIntegral.continuousAt_productPrimitive_of_bounded_integrand
      (hf_cont y hy) (hg_cont y hy) (hf_deriv_cont y hy) (hh_cont y hy)
      (fun z => ((hg_meas z).mul (measurable_deriv (f z))).add (hh_meas z))
      hq_bound hx
  constructor
  · intro y hy
    exact eVariationOn.lowerSemicontinuousAt_of_continuousAt_sections (hGcont y hy)
  · exact eVariationOn.measurable_of_countable_noncontinuous_sections hS hGcont

/-- The extended-real conclusion of Lemma 6.2 for Borel, uniformly pointwise
bounded representatives. The parameter type is the open unit interval with
Lebesgue measure. The `Fₙ ∈ L¹` premise is recorded as measurability and
finiteness of each individual nonnegative integral. -/
theorem lemma6_2_of_bounded_representatives
    {fₙ gₙ hₙ : ℕ → Ioo (0 : ℝ) 1 → ℝ → ℝ}
    {f g h : Ioo (0 : ℝ) 1 → ℝ → ℝ}
    {S : Set (Ioo (0 : ℝ) 1)}
    (hS : S.Countable)
    (_hfₙ_diff : ∀ n y, ∀ x ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (fₙ n y) x)
    (_hf_diff : ∀ y, ∀ x ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (f y) x)
    (hf_lim : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => fₙ n y x) atTop (𝓝 (f y x)))
    (hf_deriv_lim : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => deriv (fₙ n y) x) atTop (𝓝 (deriv (f y) x)))
    (hf_deriv_bound : ∀ y, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n x, x ∈ Icc (0 : ℝ) 1 → |deriv (fₙ n y) x| ≤ C)
    (hg_var : ∀ y, ∃ V : ℝ≥0∞, V ≠ ∞ ∧
      ∀ n, eVariationOn (gₙ n y) (Icc (0 : ℝ) 1) ≤ V)
    (hg_lim : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => gₙ n y x) atTop (𝓝 (g y x)))
    (hhₙ_meas : ∀ n y, Measurable (hₙ n y))
    (hhₙ_bound : ∀ y, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n x, x ∈ Icc (0 : ℝ) 1 → |hₙ n y x| ≤ C)
    (hh_lim : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => hₙ n y x) atTop (𝓝 (h y x)))
    (hFₙ_meas : ∀ n, Measurable (fun y : Ioo (0 : ℝ) 1 =>
      eVariationOn (intervalIntegral.productPrimitive
        (fₙ n y) (gₙ n y) (deriv (fₙ n y)) (hₙ n y)) (Icc (0 : ℝ) 1)))
    (_hFₙ_integrable : ∀ n, (∫⁻ y : Ioo (0 : ℝ) 1,
      eVariationOn (intervalIntegral.productPrimitive
        (fₙ n y) (gₙ n y) (deriv (fₙ n y)) (hₙ n y)) (Icc (0 : ℝ) 1)) ≠ ∞)
    (_hf_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y x, x ∈ Icc (0 : ℝ) 1 → |f y x| ≤ C)
    (hf_deriv_bound_lim : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y x, x ∈ Icc (0 : ℝ) 1 → |deriv (f y) x| ≤ C)
    (hg_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y x, x ∈ Icc (0 : ℝ) 1 → |g y x| ≤ C)
    (hh_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y x, x ∈ Icc (0 : ℝ) 1 → |h y x| ≤ C)
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
  have hvar' : ∀ y, ∃ V : ℝ≥0∞, V ≠ ∞ ∧
      ∀ n, eVariationOn (gₙ' n y) (Icc (0 : ℝ) 1) ≤ V := by
    intro y
    obtain ⟨V, hV, hvar⟩ := hg_var y
    refine ⟨V, hV, fun n => ?_⟩
    rw [eVariationOn.congr (fun x hx =>
      BoundedVariationOn.extendIcc_of_mem hab hx)]
    exact hvar n
  have hg_lim' : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => gₙ' n y x) atTop (𝓝 (g' y x)) := by
    intro y x hx
    simpa only [gₙ', g', BoundedVariationOn.extendIcc_of_mem hab hx] using hg_lim y x hx
  have hgₙ_meas' : ∀ n y, Measurable (gₙ' n y) := by
    intro n y
    obtain ⟨V, hV, hvar⟩ := hg_var y
    exact measurable_extendIcc_of_bv (ne_top_of_le_ne_top hV (hvar n))
  have hg_meas' : ∀ y, Measurable (g' y) := by
    intro y
    apply measurable_of_tendsto_metrizable (fun n => hgₙ_meas' n y)
    rw [tendsto_pi_nhds]
    intro x
    have hx := (Set.projIcc (0 : ℝ) 1 hab x).property
    simpa only [gₙ', g', Function.extendIcc] using hg_lim y _ hx
  obtain ⟨Cg, hCg₀, hCg⟩ := hg_bound
  have hg_bound' : ∃ C : ℝ, 0 ≤ C ∧
      ∀ y x, x ∈ Icc (0 : ℝ) 1 → |g' y x| ≤ C := by
    refine ⟨Cg, hCg₀, ?_⟩
    intro y x hx
    simpa only [g', BoundedVariationOn.extendIcc_of_mem hab hx] using hCg y x hx
  have hg_cont' : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => g' z x) y := by
    intro y hy x hx
    simpa only [g', BoundedVariationOn.extendIcc_of_mem hab hx] using hg_cont y hy x hx
  have hFₙ_meas' : ∀ n, Measurable (fun y : Ioo (0 : ℝ) 1 =>
      eVariationOn (intervalIntegral.productPrimitive
        (fₙ n y) (gₙ' n y) (deriv (fₙ n y)) (hₙ n y)) (Icc (0 : ℝ) 1)) := by
    intro n
    convert hFₙ_meas n using 1
    funext y
    exact eVariationOn.congr (productPrimitive_congr_on_Icc fun x hx =>
      BoundedVariationOn.extendIcc_of_mem hab hx)
  have hmain := eVariationOn.productPrimitive_lintegral_le_liminf
    (μ := (volume : Measure (Ioo (0 : ℝ) 1)))
    hS hvar' hf_lim hg_lim' hf_deriv_lim hh_lim
    hgₙ_meas' (fun n y => measurable_deriv (fₙ n y)) hhₙ_meas
    hf_deriv_bound hhₙ_bound hg_meas'
    (fun y => measurable_deriv (f y)) hh_meas
    hg_bound' hf_deriv_bound_lim hh_bound
    hf_cont hg_cont' hf_deriv_cont hh_cont hFₙ_meas'
  have hF_eq : (fun y : Ioo (0 : ℝ) 1 =>
      eVariationOn (intervalIntegral.productPrimitive
        (f y) (g y) (deriv (f y)) (h y)) (Icc (0 : ℝ) 1)) =
      (fun y : Ioo (0 : ℝ) 1 =>
        eVariationOn (intervalIntegral.productPrimitive
          (f y) (g' y) (deriv (f y)) (h y)) (Icc (0 : ℝ) 1)) := by
    funext y
    exact eVariationOn.congr (productPrimitive_congr_on_Icc fun x hx =>
      (BoundedVariationOn.extendIcc_of_mem hab hx).symm)
  have hFₙ_eq (n : ℕ) : (fun y : Ioo (0 : ℝ) 1 =>
      eVariationOn (intervalIntegral.productPrimitive
        (fₙ n y) (gₙ n y) (deriv (fₙ n y)) (hₙ n y)) (Icc (0 : ℝ) 1)) =
      (fun y : Ioo (0 : ℝ) 1 =>
        eVariationOn (intervalIntegral.productPrimitive
          (fₙ n y) (gₙ' n y) (deriv (fₙ n y)) (hₙ n y)) (Icc (0 : ℝ) 1)) := by
    funext y
    exact eVariationOn.congr (productPrimitive_congr_on_Icc fun x hx =>
      (BoundedVariationOn.extendIcc_of_mem hab hx).symm)
  constructor
  · rw [hF_eq]
    exact hmain.2.1
  · simp_rw [hFₙ_eq, hF_eq]
    exact hmain.2.2

end ChristodoulouBV

end
