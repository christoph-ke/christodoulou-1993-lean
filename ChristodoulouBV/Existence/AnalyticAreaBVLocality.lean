module

public import ChristodoulouBV.Existence.AnalyticAreaBVKernel
import ChristodoulouBV.ForMathlib.BoundedVariation.Algebra
import Mathlib.Tactic

/-!
# Locality of section variation measures

On an open interval, the Stieltjes variation measure is independent of
values outside that interval and of an additive anchoring constant.
This is the locality needed when joining the physical area charts.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Primitives differing by a constant on an open interval determine
the same variation measure there. Arbitrary values at the two endpoints
are deliberately excluded from the comparison. -/
theorem variation_measure_restrict_Ioo_eq_of_eqOn_add_const
    {f g : ℝ → ℝ} (hf : BoundedVariationOn f univ)
    (hg : BoundedVariationOn g univ) {A B c : ℝ}
    (hfg : EqOn f (fun t => g t + c) (Ioo A B)) :
    hf.vectorMeasure.variation.restrict (Ioo A B) =
      hg.vectorMeasure.variation.restrict (Ioo A B) := by
  have hr {x : ℝ} (hx : x ∈ Ioo A B) :
      Function.rightLim f x = Function.rightLim g x + c := by
    have heq : f =ᶠ[𝓝[>] x] fun t => g t + c := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hx)] with t ht
      exact hfg ht
    exact tendsto_nhds_unique (hf.tendsto_rightLim x)
      (((hg.tendsto_rightLim x).add_const c).congr' heq.symm)
  apply Real.measure_ext_Ioo_rat
  intro a b
  rw [Measure.restrict_apply measurableSet_Ioo, Measure.restrict_apply measurableSet_Ioo,
    Ioo_inter_Ioo, hf.variation_vectorMeasure_Ioo_right, hg.variation_vectorMeasure_Ioo_right]
  calc
    _ = eVariationOn (fun t => Function.rightLim g t + c)
        (Ioo (max (a : ℝ) A) (min (b : ℝ) B)) := by
      apply eVariationOn.eq_of_eqOn
      intro t ht
      exact hr ⟨(le_max_right _ _).trans_lt ht.1,
        ht.2.trans_le (min_le_right _ _)⟩
    _ = _ := eVariationOn.add_const _ _ _

end ChristodoulouBV

end
