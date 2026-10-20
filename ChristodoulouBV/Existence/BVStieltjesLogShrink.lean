module

public import ChristodoulouBV.Existence.BVStieltjesLogTransport
public import ChristodoulouBV.Existence.BVStieltjesOutgoingShrink
import Mathlib.Tactic

/-!
# Shrinking logarithmic residuals

Finite variation of each fixed edge and the closed-transverse-edge
analytic-area tails vanish separately. These conclusions are independent
of the mass-ratio majorants used later for absorption.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The source outgoing logarithmic residual limit (6.8b). -/
theorem eq6_8b
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun u => eVariationOn (bvOutgoingLogResidual d.scalarRightFields u a)
      (Ioo u a)) (𝓝[<] a) (𝓝 0) := by
  have hc : 0 < a / 2 := half_pos ha
  have hca : a / 2 < a := half_lt_self ha
  have hf := (bv_outgoing_log_residual_bv h hD d (u := 0) le_rfl hc hca.le).mono
    Ioo_subset_Icc_self
  have hfixed := bv_variation_left_tail_tendsto_zero hca hf
  have harea := bv_area_outgoing_closed_rectangle_tendsto h hD d .phiBetaNu
    (u₀ := 0) (a := a) le_rfl
  have hsum : Tendsto (fun u =>
      eVariationOn (bvOutgoingLogResidual d.scalarRightFields 0 a) (Ioo u a) +
        bvAnalyticArea h hD d .phiBetaNu (Icc 0 u ×ˢ Ioo u a)) (𝓝[<] a) (𝓝 0) := by
    simpa only [add_zero] using hfixed.add harea
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [Ioo_mem_nhdsLT ha] with u hu
  exact eq6_8a h hD d hu.1 hu.2

/-- The corrected source incoming logarithmic residual limit (6.11b). -/
theorem eq6_11b
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun v => eVariationOn (bvIncomingLogResidual d.scalarRightFields v a)
      (Ioo a v)) (𝓝[>] a) (𝓝 0) := by
  let c := (a + b) / 2
  have hac : a < c := by dsimp only [c]; linarith only [hab]
  have hcb : c < b := by dsimp only [c]; linarith only [hab]
  have hf := (bv_incoming_log_residual_bv h hD d ha.le hac.le hcb).mono
    Ioo_subset_Icc_self
  have hfixed := bv_variation_right_tail_tendsto_zero hac hf
  have harea := bv_area_incoming_closed_rectangle_tendsto h hD d .phiAlphaLam
    (b := b) ha.le
  have hsum : Tendsto (fun v =>
      eVariationOn (bvIncomingLogResidual d.scalarRightFields b a) (Ioo a v) +
        bvAnalyticArea h hD d .phiAlphaLam (Ioo a v ×ˢ Icc v b)) (𝓝[>] a) (𝓝 0) := by
    simpa only [add_zero] using hfixed.add harea
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [Ioo_mem_nhdsGT hab] with v hv
  exact eq6_11a h hD d ha hv.1 hv.2

end ChristodoulouBV

end
