module

public import ChristodoulouBV.Existence.AreaLowerSemicontinuityEssential
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# The lower-integral conclusion of Lemma 6.2

The source's rectangle `L∞` assumptions are stated on the product of the closed
`x` interval and open `y` interval. They are distinct from bounds on every
`y` section. The conclusion uses Mathlib's lower Lebesgue integral and does
not require measurability of the limit variation.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

attribute [local instance] Measure.Subtype.measureSpace

namespace ChristodoulouBV

/-- The lower-integral step of Lemma 6.2: a pointwise liminf bound and Fatou
for almost everywhere measurable approximants. No measurability of `F` is
needed. -/
theorem lemma6_2_lintegral_le_liminf_of_pointwise
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : α → ℝ≥0∞} {Fₙ : ℕ → α → ℝ≥0∞}
    (hpoint : ∀ y, F y ≤ liminf (fun n => Fₙ n y) atTop)
    (hFₙ_ae : ∀ n, AEMeasurable (Fₙ n) μ) :
    (∫⁻ y, F y ∂μ) ≤ liminf (fun n => ∫⁻ y, Fₙ n y ∂μ) atTop :=
  (lintegral_mono hpoint).trans (lintegral_liminf_le' hFₙ_ae)

/-- The lower-integral conclusion of Christodoulou's Lemma 6.2 under its
printed hypotheses. Each `y` section satisfies Lemma 6.1, the approximating
variations are `L¹`, the four limit functions are `L∞` on the rectangle, and
their fixed-`x` sections are continuous away from one countable set. The
variation retains pointwise values of the integration-by-parts primitive. -/
theorem lemma6_2_lintegral
    {fₙ gₙ hₙ : ℕ → Ioo (0 : ℝ) 1 → ℝ → ℝ}
    {f g h : Ioo (0 : ℝ) 1 → ℝ → ℝ}
    {S : Set (Ioo (0 : ℝ) 1)}
    (_hS : S.Countable)
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
    (hFₙ_ae : ∀ n, AEMeasurable (fun y : Ioo (0 : ℝ) 1 =>
      eVariationOn (intervalIntegral.productPrimitive
        (fₙ n y) (gₙ n y) (deriv (fₙ n y)) (hₙ n y)) (Icc (0 : ℝ) 1)) volume)
    (_hFₙ_finite : ∀ n, (∫⁻ y : Ioo (0 : ℝ) 1,
      eVariationOn (intervalIntegral.productPrimitive
        (fₙ n y) (gₙ n y) (deriv (fₙ n y)) (hₙ n y)) (Icc (0 : ℝ) 1)) ≠ ∞)
    (_hf_Linf : MemLp (fun p : Icc (0 : ℝ) 1 × Ioo (0 : ℝ) 1 => f p.2 p.1) ∞ volume)
    (_hf_deriv_Linf : MemLp (fun p : Icc (0 : ℝ) 1 × Ioo (0 : ℝ) 1 =>
      deriv (f p.2) p.1) ∞ volume)
    (_hg_Linf : MemLp (fun p : Icc (0 : ℝ) 1 × Ioo (0 : ℝ) 1 => g p.2 p.1) ∞ volume)
    (_hh_Linf : MemLp (fun p : Icc (0 : ℝ) 1 × Ioo (0 : ℝ) 1 => h p.2 p.1) ∞ volume)
    (_hf_cont : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => f z x) y)
    (_hf_deriv_cont : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => deriv (f z) x) y)
    (_hg_cont : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => g z x) y)
    (_hh_cont : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => h z x) y) :
    (∫⁻ y : Ioo (0 : ℝ) 1,
      eVariationOn (intervalIntegral.productPrimitive
        (f y) (g y) (deriv (f y)) (h y)) (Icc (0 : ℝ) 1)) ≤
      liminf (fun n => ∫⁻ y : Ioo (0 : ℝ) 1,
        eVariationOn (intervalIntegral.productPrimitive
          (fₙ n y) (gₙ n y) (deriv (fₙ n y)) (hₙ n y))
          (Icc (0 : ℝ) 1)) atTop :=
  lemma6_2_lintegral_le_liminf_of_pointwise
    (fun y => lemma6_2_pointwise hfₙ_diff hf_diff hf_lim hf_deriv_lim
      hf_deriv_bound hg_var hg_lim hhₙ_meas hhₙ_bound hh_lim y) hFₙ_ae

end ChristodoulouBV

end
