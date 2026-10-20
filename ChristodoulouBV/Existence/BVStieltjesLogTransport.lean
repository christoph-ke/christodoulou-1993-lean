module

public import ChristodoulouBV.Existence.BVStieltjesLogIdentities
public import ChristodoulouBV.Existence.BVStieltjesIntegralTransport
public import ChristodoulouBV.Existence.BVStieltjesKernel
import Mathlib.Tactic

/-!
# Logarithmic transport against the complementary analytic carriers

The outgoing logarithmic residual uses incoming-section variation of
`φ, β/ν`; the incoming residual uses outgoing-section variation of
`φ, α/λ`. Closed transverse edges retain the characteristic jump masses.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Outgoing logarithmic transport on an initial or shifted triangle.
Both transverse characteristics are retained by the actual carrier. -/
theorem bv_outgoing_log_transport
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u₀ u a : ℝ} (hu₀ : 0 ≤ u₀)
    (huu : u₀ ≤ u) (_hua : u < a) :
    eVariationOn (bvOutgoingLogResidual d.scalarRightFields u a) (Ioo u a) ≤
      eVariationOn (bvOutgoingLogResidual d.scalarRightFields u₀ a) (Ioo u a) +
        bvAnalyticArea h hD d .phiBetaNu (Icc u₀ u ×ˢ Ioo u a) := by
  let S := d.scalarRightFields
  let q := fun t => -areaPhysicalPrimitive .phiBetaNu S t u₀ u
  have hqi (x : ℝ) (hx : x ∈ Ioo u a) (y : ℝ) (hy : y ∈ Ioo u a) (hxy : x ≤ y) :
      IntervalIntegrable q volume x y := by
    apply IntervalIntegrable.neg
    apply bv_area_primitive_integrable_transverse h hD d .phiBetaNu hxy huu
      (A := u₀) (B := u) ⟨le_rfl, huu⟩ ⟨huu, le_rfl⟩ (sub_pos.mpr hx.1)
    · intro p hp
      exact ⟨hu₀.trans hp.2.1, hp.2.2.trans_lt (hx.1.trans_le hp.1.1)⟩
    · intro p hp
      change x - u ≤ p.1 - p.2
      exact sub_le_sub hp.1.1 hp.2.2
  have hfg (x : ℝ) (hx : x ∈ Ioo u a) (y : ℝ) (hy : y ∈ Ioo u a) (hxy : x ≤ y) :
      (bvOutgoingLogResidual S u a y - bvOutgoingLogResidual S u a x) -
        (bvOutgoingLogResidual S u₀ a y - bvOutgoingLogResidual S u₀ a x) =
          ∫ t in x..y, q t := by
    rw [bv_outgoing_log_residual_increment h hD d (hu₀.trans huu) hx.1 hxy hy.2.le,
      bv_outgoing_log_residual_increment h hD d hu₀ (huu.trans_lt hx.1) hxy hy.2.le]
    simpa only [q, intervalIntegral.integral_neg] using
      bv_outgoing_log_rectangle_increment h hD d hu₀ huu hx.1 hxy
  have hb : ∀ᵐ t ∂volume, t ∈ Ioo u a → ENNReal.ofReal |q t| ≤
      areaBVGlobalSectionKernel h hD d .phiBetaNu t (Icc u₀ u) := by
    filter_upwards [bv_area_incoming_increment_le_global_kernel h hD d .phiBetaNu rfl]
      with t ht htI
    simpa only [q, abs_neg] using ht u₀ u hu₀ huu htI.1
  have he := stieltjes_variation_transport_integral hqi hfg hb
  have harea : bvAnalyticArea h hD d .phiBetaNu (Icc u₀ u ×ˢ Ioo u a) =
      ∫⁻ t in Ioo u a, areaBVGlobalSectionKernel h hD d .phiBetaNu t (Icc u₀ u) := by
    simpa only [AreaSectionPair.incoming, ite_true] using
      bv_area_section_rectangle_sets h hD d .phiBetaNu measurableSet_Ioo measurableSet_Icc
  rw [← harea] at he
  exact he

/-- The source outgoing logarithmic Stieltjes inequality (6.8a),
with its closed transverse edges and canonical initial trace. -/
theorem eq6_8a
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u a : ℝ} (hu : 0 < u) (hua : u < a) :
    eVariationOn (bvOutgoingLogResidual d.scalarRightFields u a) (Ioo u a) ≤
      eVariationOn (bvOutgoingLogResidual d.scalarRightFields 0 a) (Ioo u a) +
        bvAnalyticArea h hD d .phiBetaNu (Icc 0 u ×ˢ Ioo u a) :=
  bv_outgoing_log_transport h hD d le_rfl hu.le hua

/-- The corrected source incoming logarithmic Stieltjes inequality (6.11a).
The actual outgoing-section carrier includes both transverse endpoints. -/
theorem eq6_11a
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a v b : ℝ} (ha : 0 < a) (_hav : a < v) (hvb : v < b) :
    eVariationOn (bvIncomingLogResidual d.scalarRightFields v a) (Ioo a v) ≤
      eVariationOn (bvIncomingLogResidual d.scalarRightFields b a) (Ioo a v) +
        bvAnalyticArea h hD d .phiAlphaLam (Ioo a v ×ˢ Icc v b) := by
  let S := d.scalarRightFields
  let q := fun t => areaPhysicalPrimitive .phiAlphaLam S t v b
  have hqi (x : ℝ) (hx : x ∈ Ioo a v) (y : ℝ) (hy : y ∈ Ioo a v) (hxy : x ≤ y) :
      IntervalIntegrable q volume x y := by
    apply bv_area_primitive_integrable_transverse h hD d .phiAlphaLam hxy hvb.le
      (A := v) (B := b) ⟨le_rfl, hvb.le⟩ ⟨hvb.le, le_rfl⟩ (sub_pos.mpr hy.2)
    · intro p hp
      exact ⟨ha.le.trans (hx.1.le.trans hp.1.1), hp.1.2.trans_lt (hy.2.trans_le hp.2.1)⟩
    · intro p hp
      change v - y ≤ p.2 - p.1
      exact sub_le_sub hp.2.1 hp.1.2
  have hfg (x : ℝ) (hx : x ∈ Ioo a v) (y : ℝ) (hy : y ∈ Ioo a v) (hxy : x ≤ y) :
      (bvIncomingLogResidual S v a y - bvIncomingLogResidual S v a x) -
        (bvIncomingLogResidual S b a y - bvIncomingLogResidual S b a x) =
          ∫ t in x..y, q t := by
    rw [bv_incoming_log_residual_increment h hD d ha.le hx.1.le hxy hy.2,
      bv_incoming_log_residual_increment h hD d ha.le hx.1.le hxy (hy.2.trans hvb)]
    exact bv_incoming_log_rectangle_increment h hD d (ha.le.trans hx.1.le) hxy hy.2 hvb.le
  have hb : ∀ᵐ t ∂volume, t ∈ Ioo a v → ENNReal.ofReal |q t| ≤
      areaBVGlobalSectionKernel h hD d .phiAlphaLam t (Icc v b) := by
    filter_upwards [bv_area_canonical_increment_le_global_kernel h hD d .phiAlphaLam]
      with t ht htI
    have hi := ht v b hvb.le (fun w hw =>
      show (t, w) ∈ areaSmoothDomain from ⟨ha.trans htI.1, htI.2.trans_le hw.1⟩)
    exact hi.trans (measure_mono Ioc_subset_Icc_self)
  have he := stieltjes_variation_transport_integral hqi hfg hb
  have harea : bvAnalyticArea h hD d .phiAlphaLam (Ioo a v ×ˢ Icc v b) =
      ∫⁻ t in Ioo a v, areaBVGlobalSectionKernel h hD d .phiAlphaLam t (Icc v b) := by
    simpa only [AreaSectionPair.incoming, Bool.false_eq_true, ite_false] using
      bv_area_section_rectangle_sets h hD d .phiAlphaLam measurableSet_Ioo measurableSet_Icc
  rw [← harea] at he
  exact he

end ChristodoulouBV

end
