module

public import ChristodoulouBV.ForMathlib.BoundedVariation.LowerSemicontinuity

/-!
# Uniform variation bounds under pointwise limits

The bound is stated on an arbitrary ordered set, so it also applies to
noninterval slices at terminal characteristic levels.
-/

public section

open Filter
open scoped Topology ENNReal

namespace eVariationOn

/-- A common variation bound passes to a pointwise limit on the same set. -/
theorem le_of_tendsto_pointwise {α M ι : Type*} [LinearOrder α]
    [PseudoEMetricSpace M] {p : Filter ι} [p.NeBot]
    {F : ι → α → M} {f : α → M} {s : Set α} {C : ℝ≥0∞}
    (hF : ∀ x ∈ s, Tendsto (fun i => F i x) p (𝓝 (f x)))
    (hC : ∀ᶠ i in p, eVariationOn (F i) s ≤ C) :
    eVariationOn f s ≤ C := by
  calc
    eVariationOn f s ≤ liminf (fun i => eVariationOn (F i) s) p :=
      le_liminf_of_tendsto_pointwise hF
    _ ≤ liminf (fun _ : ι => C) p := liminf_le_liminf hC
    _ = C := liminf_const C

end eVariationOn

end
