module

public import ChristodoulouBV.AreaEstimates.BasicEstimatesUnit
public import ChristodoulouBV.AreaEstimates.BasicEstimatesVariationUnit

/-!
# Basic estimates of Section 4

The amplitude estimates and variation contraction are split into focused
modules below this import point.
-/

public section

open Set MeasureTheory

namespace ChristodoulouBV

/-- Lemma 4.1: the two null integrals are bounded by total variation of
the corresponding scalar-to-radius derivative ratios. -/
theorem lemma4_1_larger {b : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    (∀ u ∈ Ioo (0 : ℝ) 1,
      (∫⁻ v in Ioo u 1, ENNReal.ofReal (|S.theta u v| / S.r u v)) ≤
        eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u 1)) ∧
    (∀ v ∈ Ioo (0 : ℝ) 1,
      (∫⁻ u in Ioo 0 v, ENNReal.ofReal (|S.zeta u v| / S.r u v)) ≤
        eVariationOn (fun u => S.beta u v / S.nu u v) (Ioo 0 v)) := by
  exact ⟨fun u hu => outgoing_scalar_variation_bound hb hu H,
    fun v hv => incoming_scalar_variation_bound hb hv H⟩

/-- Lemma 4.1 on the source's closed unit C¹ development. -/
theorem lemma4_1 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    (∀ u ∈ Ioo (0 : ℝ) 1,
      (∫⁻ v in Ioo u 1, ENNReal.ofReal (|S.theta u v| / S.r u v)) ≤
        eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u 1)) ∧
    (∀ v ∈ Ioo (0 : ℝ) 1,
      (∫⁻ u in Ioo 0 v, ENNReal.ofReal (|S.zeta u v| / S.r u v)) ≤
        eVariationOn (fun u => S.beta u v / S.nu u v) (Ioo 0 v)) := by
  exact ⟨fun u hu => outgoing_scalar_variation_bound_unit hu H,
    fun v hv => incoming_scalar_variation_bound_unit hv H⟩

end ChristodoulouBV

end
