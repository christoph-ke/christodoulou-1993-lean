module

public import ChristodoulouBV.Existence.AxisIncomingEdges
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Shifted incoming residuals

Equation (6.16a) retains the scalar residual on the terminal edge.
Its left tail and the finite incoming triangle area vanish separately,
giving the uniform incoming scalar residual limit (6.16b).
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Equation (6.16a): the shifted incoming scalar residual is bounded
by its terminal-edge residual and the ν--φ area of the open triangle. -/
theorem eq6_16a
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a ε v : ℝ} (hεa : ε < a)
    (hv : v ∈ Ioo (a - ε) a) :
    eVariationOn (bvIncomingScalarResidual d.scalarRightFields v (a - ε))
        (Ioo (a - ε) v) ≤
      eVariationOn (bvIncomingScalarResidual d.scalarRightFields a (a - ε))
        (Ioo (a - ε) v) +
      bvAnalyticArea h hD d .nuPhi (openCoordTriangle (a - ε) a) := by
  refine (eq6_10a h hD d (sub_pos.mpr hεa) hv.1 hv.2).trans
    (add_le_add le_rfl ?_)
  exact measure_mono (fun _ hp => ⟨hp.1.1, hp.1.2.trans hp.2.1, hp.2.2⟩)

/-- Equation (6.16b): incoming scalar residuals vanish uniformly on
all sections of every shrinking past triangle at a positive axis point. -/
theorem eq6_16b
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε => ⨆ v ∈ Ioo (a - ε) a, eVariationOn
      (bvIncomingScalarResidual d.scalarRightFields v (a - ε)) (Ioo (a - ε) v))
      (𝓝[>] 0) (𝓝 0) := by
  have hsum := (bv_incoming_scalar_edge_tendsto h hD d ha).add
    (bv_analytic_area_incoming_triangle_tendsto h hD d .nuPhi ha)
  rw [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [Ioo_mem_nhdsGT ha] with ε hε
  refine iSup_le fun v => iSup_le fun hv => (eq6_16a h hD d hε.2 hv).trans ?_
  exact add_le_add (eVariationOn.mono _ (Ioo_subset_Ioo_right hv.2.le)) le_rfl

/-- Incoming logarithmic transport with the canonical half-open transverse
carrier. The terminal characteristic retains its possible jump mass. -/
theorem bv_incoming_log_transport_half_open
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a v b : ℝ} (ha : 0 < a) (_hav : a < v) (hvb : v < b) :
    eVariationOn (bvIncomingLogResidual d.scalarRightFields v a) (Ioo a v) ≤
      eVariationOn (bvIncomingLogResidual d.scalarRightFields b a) (Ioo a v) +
        bvAnalyticArea h hD d .phiAlphaLam (Ioo a v ×ˢ Ioc v b) := by
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
      areaBVGlobalSectionKernel h hD d .phiAlphaLam t (Ioc v b) := by
    filter_upwards [bv_area_canonical_increment_le_global_kernel h hD d .phiAlphaLam]
      with t ht htI
    have hi := ht v b hvb.le (fun w hw =>
      show (t, w) ∈ areaSmoothDomain from ⟨ha.trans htI.1, htI.2.trans_le hw.1⟩)
    exact hi
  have he := stieltjes_variation_transport_integral hqi hfg hb
  have harea : bvAnalyticArea h hD d .phiAlphaLam (Ioo a v ×ˢ Ioc v b) =
      ∫⁻ t in Ioo a v, areaBVGlobalSectionKernel h hD d .phiAlphaLam t (Ioc v b) := by
    simpa only [AreaSectionPair.incoming, Bool.false_eq_true, ite_false] using
      bv_area_section_rectangle_sets h hD d .phiAlphaLam measurableSet_Ioo measurableSet_Ioc
  rw [← harea] at he
  exact he

/-- The amended half-open incoming triangles have vanishing area, including
possible carrier atoms on the terminal characteristic. Finiteness comes
from the area limit bounds on the triangle at `ε = a / 2`. -/
theorem bv_analytic_area_incoming_half_open_triangle_tendsto
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε => bvAnalyticArea h hD d k
      {p | a - ε < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ a}) (𝓝[>] 0) (𝓝 0) := by
  apply bv_analytic_area_shrinking_right h hD d k
  · intro ε _
    exact (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const))
  · intro ε η _ hεη p hp
    exact ⟨(sub_le_sub_left hεη a).trans_lt hp.1, hp.2.1, hp.2.2⟩
  · refine ⟨a / 2, half_pos ha, fun p hp => ⟨?_, hp.2.1⟩⟩
    linarith only [ha, hp.1]
  · apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hp1 := mem_iInter.mp (mem_iInter.mp hp 1) zero_lt_one
    have hg : 0 < a - p.1 := sub_pos.mpr (hp1.2.1.trans_le hp1.2.2)
    have hp2 := mem_iInter.mp (mem_iInter.mp hp ((a - p.1) / 2)) (half_pos hg)
    linarith only [hp2.1, hg]

/-- Amended (6.17a): the corrected incoming log residual is bounded by
its terminal-edge residual and the area of `{a-ε < u < v ≤ a}`. -/
theorem eq6_17a
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a ε v : ℝ} (hεa : ε < a)
    (hv : v ∈ Ioo (a - ε) a) :
    eVariationOn (bvIncomingLogResidual d.scalarRightFields v (a - ε))
        (Ioo (a - ε) v) ≤
      eVariationOn (bvIncomingLogResidual d.scalarRightFields a (a - ε))
        (Ioo (a - ε) v) +
      bvAnalyticArea h hD d .phiAlphaLam
        {p | a - ε < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ a} := by
  refine (bv_incoming_log_transport_half_open h hD d (sub_pos.mpr hεa) hv.1 hv.2).trans
    (add_le_add le_rfl ?_)
  exact measure_mono (fun _ hp => ⟨hp.1.1, hp.1.2.trans hp.2.1, hp.2.2⟩)

/-- Corrected (6.17b), including the missing `g*` term of ERR-32:
incoming log residuals vanish uniformly on shrinking past triangles. -/
theorem eq6_17b
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε => ⨆ v ∈ Ioo (a - ε) a, eVariationOn
      (bvIncomingLogResidual d.scalarRightFields v (a - ε)) (Ioo (a - ε) v))
      (𝓝[>] 0) (𝓝 0) := by
  have hsum := (bv_incoming_log_edge_tendsto h hD d ha).add
    (bv_analytic_area_incoming_half_open_triangle_tendsto h hD d .phiAlphaLam ha)
  rw [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [Ioo_mem_nhdsGT ha] with ε hε
  refine iSup_le fun v => iSup_le fun hv => (eq6_17a h hD d hε.2 hv).trans ?_
  exact add_le_add (eVariationOn.mono _ (Ioo_subset_Ioo_right hv.2.le)) le_rfl

end ChristodoulouBV

end
