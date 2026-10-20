module

public import ChristodoulouBV.Existence.C1ContinuationCutoff
import Mathlib.Tactic

/-!
# Outgoing variation tends to zero at a finite endpoint

The finite-cutoff contraction is exhausted on the endpoint patch. The endpoint
residual tails then give equation (6.3), without an endpoint solution premise.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Each terminal outgoing variation is bounded by six times the sum of
the two terminal residual integrals. Only finite members are used. -/
theorem endpointPatch_variation_le_residuals
    {alpha₀ : ℝ → ℝ} {vStar : ℝ}
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧ (family b).alpha 0 v = alpha₀ v)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) vStar) :
    let P := endpointPatch family vStar
    let R := 6 * ((∫⁻ v in Ioo u vStar,
      ENNReal.ofReal |sourceOutgoingAlphaResidual P u v|) +
      (∫⁻ v in Ioo u vStar, ENNReal.ofReal |sourceOutgoingLogResidual P u v|))
    eVariationOn (fun v => P.alpha u v / P.lam u v) (Ioo u vStar) ≤ R ∧
      eVariationOn (fun v => Real.log (P.lam u v)) (Ioo u vStar) ≤ R := by
  let P := endpointPatch family vStar
  let R := 6 * ((∫⁻ v in Ioo u vStar,
    ENNReal.ofReal |sourceOutgoingAlphaResidual P u v|) +
    (∫⁻ v in Ioo u vStar, ENNReal.ofReal |sourceOutgoingLogResidual P u v|))
  have hcut (a : ℝ) (hua : u < a) (haStar : a < vStar) :
      eVariationOn (fun v => P.alpha u v / P.lam u v) (Ioo u a) +
        eVariationOn (fun v => Real.log (P.lam u v)) (Ioo u a) ≤ R := by
    obtain ⟨b, hab, hbStar⟩ := exists_between haStar
    obtain ⟨B, haB, hBb⟩ := exists_between hab
    have hb : b ∈ Ioo (0 : ℝ) vStar := ⟨hu.1.trans (hua.trans hab), hbStar⟩
    obtain ⟨HS, hdata⟩ := hfamily b hb
    have h := s6_finite_cutoff_variation_le_residuals
      (hu.1.trans (hua.trans haB)) hBb HS hdata hD (hu.1.trans hua) haB ⟨hu.1, hua⟩
    have hvalues (v : ℝ) (hv : v ∈ Ioo u a) := endpointPatch_agrees hfamily hb
      (show (u, v) ∈ developmentWithInitialEdge b from ⟨hu.1.le, hv.1, hv.2.trans hab⟩)
    have hq : EqOn (fun v => P.alpha u v / P.lam u v)
        (fun v => (family b).alpha u v / (family b).lam u v) (Ioo u a) := by
      intro v hv
      exact congrArg₂ (· / ·) (hvalues v hv).2.2.2.2.2.1
        (hvalues v hv).2.2.2.1
    have hl : EqOn (fun v => Real.log (P.lam u v))
        (fun v => Real.log ((family b).lam u v)) (Ioo u a) := by
      intro v hv
      exact congrArg Real.log (hvalues v hv).2.2.2.1
    have hA : (∫⁻ v in Ioo u a, ENNReal.ofReal |sourceOutgoingAlphaResidual P u v|) =
        ∫⁻ v in Ioo u a, ENNReal.ofReal |sourceOutgoingAlphaResidual (family b) u v| := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      rw [(endpointPatch_outgoing_residual_eq hfamily hb hu.1 hv.1 (hv.2.trans hab)).1]
    have hL : (∫⁻ v in Ioo u a, ENNReal.ofReal |sourceOutgoingLogResidual P u v|) =
        ∫⁻ v in Ioo u a, ENNReal.ofReal |sourceOutgoingLogResidual (family b) u v| := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      rw [(endpointPatch_outgoing_residual_eq hfamily hb hu.1 hv.1 (hv.2.trans hab)).2]
    rw [eVariationOn.congr hq, eVariationOn.congr hl]
    rw [← hA, ← hL] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (add_le_add (lintegral_mono_set (Ioo_subset_Ioo_right haStar.le))
        (lintegral_mono_set (Ioo_subset_Ioo_right haStar.le))) bot_le)
  constructor
  · apply s6_variation_terminal_exhaustion_bound _ hu.2
    intro a hua haStar
    exact (le_add_right le_rfl).trans (hcut a hua haStar)
  · apply s6_variation_terminal_exhaustion_bound _ hu.2
    intro a hua haStar
    exact (le_add_left le_rfl).trans (hcut a hua haStar)

/-- Equation (6.3): both outgoing terminal variations tend to zero. The
fixed smallness threshold is the same one used in the bootstrap and endpoint estimates. -/
theorem eq6_3
    {alpha₀ : ℝ → ℝ} {vStar : ℝ} (hStar : 0 < vStar)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen)
    {family : ℝ → Fields}
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (family b) ∧
      ∀ v ∈ Ioo (0 : ℝ) b,
        (family b).r 0 v = v / 2 ∧ (family b).alpha 0 v = alpha₀ v) :
    let P := endpointPatch family vStar
    Tendsto (fun u => eVariationOn (fun v => P.alpha u v / P.lam u v)
      (Ioo u vStar)) (𝓝[<] vStar) (𝓝 0) ∧
    Tendsto (fun u => eVariationOn (fun v => Real.log (P.lam u v))
      (Ioo u vStar)) (𝓝[<] vStar) (𝓝 0) := by
  let P := endpointPatch family vStar
  have hR : Tendsto (fun u => (6 : ℝ≥0∞) *
      ((∫⁻ v in Ioo u vStar, ENNReal.ofReal |sourceOutgoingAlphaResidual P u v|) +
        (∫⁻ v in Ioo u vStar, ENNReal.ofReal |sourceOutgoingLogResidual P u v|)))
      (𝓝[<] vStar) (𝓝 0) := by
    simpa only [add_zero, mul_zero] using
      (ENNReal.Tendsto.const_mul
        ((eq6_1_lintegral hStar hD hfamily).add
          (eq6_2_lintegral hStar hD hfamily))
        (Or.inr (by norm_num : (6 : ℝ≥0∞) ≠ ∞)))
  have hQbound : ∀ᶠ u in 𝓝[<] vStar,
      eVariationOn (fun v => P.alpha u v / P.lam u v) (Ioo u vStar) ≤
        6 * ((∫⁻ v in Ioo u vStar, ENNReal.ofReal |sourceOutgoingAlphaResidual P u v|) +
          (∫⁻ v in Ioo u vStar, ENNReal.ofReal |sourceOutgoingLogResidual P u v|)) := by
    filter_upwards [Ioo_mem_nhdsLT hStar] with u hu
    exact (endpointPatch_variation_le_residuals hD hfamily hu).1
  have hLbound : ∀ᶠ u in 𝓝[<] vStar,
      eVariationOn (fun v => Real.log (P.lam u v)) (Ioo u vStar) ≤
        6 * ((∫⁻ v in Ioo u vStar, ENNReal.ofReal |sourceOutgoingAlphaResidual P u v|) +
          (∫⁻ v in Ioo u vStar, ENNReal.ofReal |sourceOutgoingLogResidual P u v|)) := by
    filter_upwards [Ioo_mem_nhdsLT hStar] with u hu
    exact (endpointPatch_variation_le_residuals hD hfamily hu).2
  exact ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hR
      (Eventually.of_forall fun _ => bot_le) hQbound,
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hR
      (Eventually.of_forall fun _ => bot_le) hLbound⟩

end ChristodoulouBV

end
