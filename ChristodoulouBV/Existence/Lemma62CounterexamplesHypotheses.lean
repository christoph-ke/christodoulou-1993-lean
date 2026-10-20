module

public import ChristodoulouBV.Existence.AreaLowerSemicontinuityLower

/-!
# Exact premises for the counterexamples to Lemma 6.2

`Lemma62Hypotheses` bundles, without strengthening or weakening, the premises
of `lemma6_2_lintegral`. The section functional uses the same pointwise
integration-by-parts primitive and the same closed interval.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

attribute [local instance] Measure.Subtype.measureSpace

namespace ChristodoulouBV

/-- The open unit interval has finite induced Lebesgue measure. -/
instance lemma62FiniteVolume : IsFiniteMeasure (volume : Measure (Ioo (0 : ℝ) 1)) where
  measure_univ_lt_top := by
    rw [Measure.Subtype.volume_univ nullMeasurableSet_Ioo]
    norm_num

/-- The section functional appearing in the printed Lemma 6.2. -/
noncomputable def lemma62Functional (f g h : Ioo (0 : ℝ) 1 → ℝ → ℝ)
    (y : Ioo (0 : ℝ) 1) : ℝ≥0∞ :=
  eVariationOn (intervalIntegral.productPrimitive (f y) (g y) (deriv (f y)) (h y))
    (Icc (0 : ℝ) 1)

/-- Exactly the premises of `lemma6_2_lintegral`, packaged for existential
counterexamples. In particular the four essential bounds are on the rectangle,
not uniformly on every section. -/
structure Lemma62Hypotheses
    (fₙ gₙ hₙ : ℕ → Ioo (0 : ℝ) 1 → ℝ → ℝ)
    (f g h : Ioo (0 : ℝ) 1 → ℝ → ℝ)
    (S : Set (Ioo (0 : ℝ) 1)) : Prop where
  hS : S.Countable
  hfₙ_diff : ∀ n y, ∀ x ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (fₙ n y) x
  hf_diff : ∀ y, ∀ x ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (f y) x
  hf_lim : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => fₙ n y x) atTop (𝓝 (f y x))
  hf_deriv_lim : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => deriv (fₙ n y) x) atTop (𝓝 (deriv (f y) x))
  hf_deriv_bound : ∀ y, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n, ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → |deriv (fₙ n y) x| ≤ C
  hg_var : ∀ y, ∃ V : ℝ≥0∞, V ≠ ∞ ∧
      ∀ n, eVariationOn (gₙ n y) (Icc (0 : ℝ) 1) ≤ V
  hg_lim : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => gₙ n y x) atTop (𝓝 (g y x))
  hhₙ_meas : ∀ n y, Measurable (hₙ n y)
  hhₙ_bound : ∀ y, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n, ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → |hₙ n y x| ≤ C
  hh_lim : ∀ y x, x ∈ Icc (0 : ℝ) 1 →
      Tendsto (fun n => hₙ n y x) atTop (𝓝 (h y x))
  hFₙ_ae : ∀ n, AEMeasurable (fun y : Ioo (0 : ℝ) 1 =>
      eVariationOn (intervalIntegral.productPrimitive
        (fₙ n y) (gₙ n y) (deriv (fₙ n y)) (hₙ n y)) (Icc (0 : ℝ) 1)) volume
  hFₙ_finite : ∀ n, (∫⁻ y : Ioo (0 : ℝ) 1,
      eVariationOn (intervalIntegral.productPrimitive
        (fₙ n y) (gₙ n y) (deriv (fₙ n y)) (hₙ n y)) (Icc (0 : ℝ) 1)) ≠ ∞
  hf_Linf : MemLp (fun p : Icc (0 : ℝ) 1 × Ioo (0 : ℝ) 1 => f p.2 p.1) ∞ volume
  hf_deriv_Linf : MemLp (fun p : Icc (0 : ℝ) 1 × Ioo (0 : ℝ) 1 =>
      deriv (f p.2) p.1) ∞ volume
  hg_Linf : MemLp (fun p : Icc (0 : ℝ) 1 × Ioo (0 : ℝ) 1 => g p.2 p.1) ∞ volume
  hh_Linf : MemLp (fun p : Icc (0 : ℝ) 1 × Ioo (0 : ℝ) 1 => h p.2 p.1) ∞ volume
  hf_cont : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => f z x) y
  hf_deriv_cont : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => deriv (f z) x) y
  hg_cont : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => g z x) y
  hh_cont : ∀ y ∉ S, ∀ x ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun z => h z x) y

/-- The bundle is exactly the premise list of `lemma6_2_lintegral`: the lemma
applies to it field by field, with no further input. -/
theorem Lemma62Hypotheses.lintegral_le_liminf
    {fₙ gₙ hₙ : ℕ → Ioo (0 : ℝ) 1 → ℝ → ℝ} {f g h : Ioo (0 : ℝ) 1 → ℝ → ℝ}
    {S : Set (Ioo (0 : ℝ) 1)} (H : Lemma62Hypotheses fₙ gₙ hₙ f g h S) :
    (∫⁻ y : Ioo (0 : ℝ) 1, lemma62Functional f g h y) ≤
      liminf (fun n => ∫⁻ y : Ioo (0 : ℝ) 1,
        eVariationOn (intervalIntegral.productPrimitive
          (fₙ n y) (gₙ n y) (deriv (fₙ n y)) (hₙ n y))
          (Icc (0 : ℝ) 1)) atTop :=
  lemma6_2_lintegral H.hS H.hfₙ_diff H.hf_diff H.hf_lim H.hf_deriv_lim
    H.hf_deriv_bound H.hg_var H.hg_lim H.hhₙ_meas H.hhₙ_bound H.hh_lim H.hFₙ_ae
    H.hFₙ_finite H.hf_Linf H.hf_deriv_Linf H.hg_Linf H.hh_Linf H.hf_cont
    H.hf_deriv_cont H.hg_cont H.hh_cont

end ChristodoulouBV
