module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Increasing limits of area measures

For an increasing sequence of measures, the pointwise supremum on
measurable sets is a measure. Monotone convergence for counting measure
proves countable additivity without a finiteness premise.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The increasing limit of a sequence of measures. -/
@[expose] noncomputable def increasingAreaMeasure
    {α : Type*} [MeasurableSpace α] (μ : ℕ → Measure α) (hm : Monotone μ) : Measure α :=
  Measure.ofMeasurable (fun E _ => ⨆ n, μ n E) (by simp only [measure_empty, iSup_const])
    (by
      intro E hE hd
      simp_rw [measure_iUnion hd hE]
      have h := lintegral_iSup (μ := (Measure.count : Measure ℕ))
        (f := fun n i => μ n (E i)) (fun _ => measurable_of_countable _)
        (fun m n hmn i => hm hmn (E i))
      simpa only [lintegral_count] using h.symm)

/-- Evaluation of an increasing limit on a measurable set is the
supremum of the evaluations. -/
theorem increasingAreaMeasure_apply
    {α : Type*} [MeasurableSpace α] (μ : ℕ → Measure α) (hm : Monotone μ)
    {E : Set α} (hE : MeasurableSet E) :
    increasingAreaMeasure μ hm E = ⨆ n, μ n E :=
  Measure.ofMeasurable_apply E hE

/-- Every measure in the exhaustion is bounded by its increasing limit. -/
theorem le_increasingAreaMeasure
    {α : Type*} [MeasurableSpace α] (μ : ℕ → Measure α) (hm : Monotone μ) (n : ℕ) :
    μ n ≤ increasingAreaMeasure μ hm := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [increasingAreaMeasure_apply μ hm hE]
  exact le_iSup (fun n => μ n E) n

end ChristodoulouBV

end
