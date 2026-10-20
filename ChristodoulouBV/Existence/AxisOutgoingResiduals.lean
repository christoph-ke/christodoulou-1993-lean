module

public import ChristodoulouBV.Existence.AxisOutgoingEdges
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Shifted outgoing residual estimates

The amended (6.13a) retains the scalar residual on the shifted initial
edge. For the logarithmic residual, the positive shifted edge permits
the sharper half-open transverse carrier bound: its upper jump mass is
retained, and its lower endpoint is the canonical right trace. Both
rectangles therefore lie in the literal open outgoing triangle.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The positive-edge refinement of the outgoing BV logarithmic transport.
The half-open carrier retains the upper characteristic's jump mass. -/
theorem bv_outgoing_log_transport_half_open
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u₀ u b : ℝ} (hu₀ : 0 < u₀)
    (huu : u₀ ≤ u) (_hub : u < b) :
    eVariationOn (bvOutgoingLogResidual d.scalarRightFields u b) (Ioo u b) ≤
      eVariationOn (bvOutgoingLogResidual d.scalarRightFields u₀ b) (Ioo u b) +
        bvAnalyticArea h hD d .phiBetaNu (Ioc u₀ u ×ˢ Ioo u b) := by
  let S := d.scalarRightFields
  let q := fun t => -areaPhysicalPrimitive .phiBetaNu S t u₀ u
  have hqi (x : ℝ) (hx : x ∈ Ioo u b) (y : ℝ) (hy : y ∈ Ioo u b) (hxy : x ≤ y) :
      IntervalIntegrable q volume x y := by
    apply IntervalIntegrable.neg
    apply bv_area_primitive_integrable_transverse h hD d .phiBetaNu hxy huu
      (A := u₀) (B := u) ⟨le_rfl, huu⟩ ⟨huu, le_rfl⟩ (sub_pos.mpr hx.1)
    · intro p hp
      exact ⟨hu₀.le.trans hp.2.1, hp.2.2.trans_lt (hx.1.trans_le hp.1.1)⟩
    · intro p hp
      change x - u ≤ p.1 - p.2
      exact sub_le_sub hp.1.1 hp.2.2
  have hfg (x : ℝ) (hx : x ∈ Ioo u b) (y : ℝ) (hy : y ∈ Ioo u b) (hxy : x ≤ y) :
      (bvOutgoingLogResidual S u b y - bvOutgoingLogResidual S u b x) -
        (bvOutgoingLogResidual S u₀ b y - bvOutgoingLogResidual S u₀ b x) =
          ∫ t in x..y, q t := by
    rw [bv_outgoing_log_residual_increment h hD d (hu₀.le.trans huu) hx.1 hxy hy.2.le,
      bv_outgoing_log_residual_increment h hD d hu₀.le (huu.trans_lt hx.1) hxy hy.2.le]
    simpa only [q, intervalIntegral.integral_neg] using
      bv_outgoing_log_rectangle_increment h hD d hu₀.le huu hx.1 hxy
  have hb : ∀ᵐ t ∂volume, t ∈ Ioo u b → ENNReal.ofReal |q t| ≤
      areaBVGlobalSectionKernel h hD d .phiBetaNu t (Ioc u₀ u) := by
    filter_upwards [bv_area_canonical_increment_le_global_kernel h hD d .phiBetaNu]
      with t ht htI
    have hi := ht u₀ u huu (fun s hs =>
      show (s, t) ∈ areaSmoothDomain from ⟨hu₀.trans_le hs.1, hs.2.trans_lt htI.1⟩)
    simpa only [q, abs_neg] using hi
  have he := stieltjes_variation_transport_integral hqi hfg hb
  have harea : bvAnalyticArea h hD d .phiBetaNu (Ioc u₀ u ×ˢ Ioo u b) =
      ∫⁻ t in Ioo u b, areaBVGlobalSectionKernel h hD d .phiBetaNu t (Ioc u₀ u) := by
    simpa only [AreaSectionPair.incoming, ite_true] using
      bv_area_section_rectangle_sets h hD d .phiBetaNu measurableSet_Ioo measurableSet_Ioc
  rw [← harea] at he
  exact he

/-- Corrected (6.13a): the scalar residual is bounded by its shifted-edge
residual variation and the λ--φ area of the shrinking triangle. -/
theorem eq6_13a
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a ε u : ℝ} (ha : 0 < a) (hu : u ∈ Ioo a (a + ε)) :
    eVariationOn (bvOutgoingScalarResidual d.scalarRightFields u (a + ε))
        (Ioo u (a + ε)) ≤
      eVariationOn (bvOutgoingScalarResidual d.scalarRightFields a (a + ε))
        (Ioo a (a + ε)) +
      bvAnalyticArea h hD d .lamPhi (openCoordTriangle a (a + ε)) := by
  refine (bv_outgoing_scalar_transport h hD d ha.le hu.1.le hu.2).trans
    (add_le_add (eVariationOn.mono _ (Ioo_subset_Ioo_left hu.1.le)) ?_)
  exact measure_mono (fun _ hp => ⟨hp.1.1, hp.1.2.trans hp.2.1, hp.2.2⟩)

/-- (6.14a), using (6.8a) as corrected by ERR-30. The fixed-edge
logarithmic residual is measured on the same outgoing interval. -/
theorem eq6_14a
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a ε u : ℝ} (ha : 0 < a) (hu : u ∈ Ioo a (a + ε)) :
    eVariationOn (bvOutgoingLogResidual d.scalarRightFields u (a + ε))
        (Ioo u (a + ε)) ≤
      eVariationOn (bvOutgoingLogResidual d.scalarRightFields a (a + ε))
        (Ioo u (a + ε)) +
      bvAnalyticArea h hD d .phiBetaNu (openCoordTriangle a (a + ε)) := by
  refine (bv_outgoing_log_transport_half_open h hD d ha hu.1.le hu.2).trans
    (add_le_add le_rfl ?_)
  exact measure_mono (fun _ hp => ⟨hp.1.1, hp.1.2.trans_lt hp.2.1, hp.2.2⟩)

/-- (6.13b): the outgoing scalar residual tends uniformly to zero on
all sections of the shrinking triangle. The amended edge residual and
the finite analytic area vanish separately. -/
theorem eq6_13b
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε => ⨆ u ∈ Ioo a (a + ε), eVariationOn
      (bvOutgoingScalarResidual d.scalarRightFields u (a + ε)) (Ioo u (a + ε)))
      (𝓝[>] 0) (𝓝 0) := by
  have hsum := (bv_outgoing_scalar_edge_tendsto h hD d ha.le).add
    (bv_analytic_area_outgoing_triangle_tendsto h hD d .lamPhi ha.le)
  rw [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le)
  exact Eventually.of_forall fun ε => iSup_le fun u => iSup_le fun hu =>
    eq6_13a h hD d ha hu

/-- (6.14b): the outgoing logarithmic residual tends uniformly to zero
on all sections of the shrinking triangle. -/
theorem eq6_14b
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε => ⨆ u ∈ Ioo a (a + ε), eVariationOn
      (bvOutgoingLogResidual d.scalarRightFields u (a + ε)) (Ioo u (a + ε)))
      (𝓝[>] 0) (𝓝 0) := by
  have hsum := (bv_outgoing_log_edge_tendsto h hD d ha.le).add
    (bv_analytic_area_outgoing_triangle_tendsto h hD d .phiBetaNu ha.le)
  rw [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le)
  apply Eventually.of_forall
  intro ε
  refine iSup_le fun u => iSup_le fun hu => (eq6_14a h hD d ha hu).trans ?_
  exact add_le_add (eVariationOn.mono _ (Ioo_subset_Ioo_left hu.1.le)) le_rfl

end ChristodoulouBV

end
