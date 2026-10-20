module

public import ChristodoulouBV.Existence.BVStieltjesOutgoing
public import ChristodoulouBV.Existence.BVStieltjesScalarShrink
import Mathlib.Tactic

/-!
# Outgoing fixed-edge residuals and corner shrinking

Finite variation of the fixed initial-edge residual and finite-measure
continuity of the analytic carrier give the outgoing scalar residual limit.
The area-tail statement also permits the closed transverse edges needed
by the logarithmic transport.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The outgoing scalar residual on a fixed off-axis edge has finite
variation, including either endpoint of the compact section. -/
theorem bv_outgoing_scalar_residual_bv
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u a b : ℝ} (hu : 0 ≤ u) (hua : u < a) (hab : a ≤ b) :
    BoundedVariationOn (bvOutgoingScalarResidual d.scalarRightFields u b) (Icc a b) := by
  obtain ⟨K, hθ, _⟩ := bv_item5 h hD d
  have hz : BoundedVariationOn (d.scalarRightFields.theta u) (Icc a b) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((eVariationOn.mono _ (fun t ht =>
        show (u, t) ∈ globalDomain from ⟨hu, hua.trans_le ht.1⟩)).trans (hθ u))
  have hi := bv_outgoing_scalar_flux_integrable h hD d hu hua hab
  have hInt :=
    (hi.absolutelyContinuousOnInterval_intervalIntegral right_mem_uIcc).boundedVariationOn
  rw [uIcc_of_le hab] at hInt
  exact hz.add hInt

/-- Outgoing analytic-area rectangles shrink even when their transverse
edges are closed. No boundary characteristic is declared null. -/
theorem bv_area_outgoing_closed_rectangle_tendsto
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {u₀ a : ℝ} (hu₀ : 0 ≤ u₀) :
    Tendsto (fun u => bvAnalyticArea h hD d k (Icc u₀ u ×ˢ Ioo u a))
      (𝓝[<] a) (𝓝 0) := by
  let E := fun ε : ℝ => globalDomain ∩ {p : ℝ × ℝ | a - ε < p.2 ∧ p.2 < a}
  have hglobal : MeasurableSet globalDomain :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd)
  have hE (ε : ℝ) : MeasurableSet (E ε) :=
    hglobal.inter ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const))
  have hm (ε η : ℝ) (_hε : 0 < ε) (hεη : ε ≤ η) : E ε ⊆ E η := by
    intro p hp
    exact ⟨hp.1, by linarith only [hp.2.1, hεη], hp.2.2⟩
  have he : (⋂ ε > 0, E ε) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hp' (ε : ℝ) (hε : 0 < ε) : p ∈ E ε :=
      mem_iInter.mp (mem_iInter.mp hp ε) hε
    have hpa := (hp' 1 zero_lt_one).2.2
    have hε : 0 < (a - p.2) / 2 := by linarith only [hpa]
    have hpv := (hp' _ hε).2.1
    linarith only [hpv, hpa]
  have ht := bv_analytic_area_shrinking_right h hD d k E
    (fun ε _ => hE ε) hm ⟨1, zero_lt_one, fun _ hp => hp.1⟩ he
  have hsub : Tendsto (fun u : ℝ => a - u) (𝓝[<] a) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [id_eq, sub_self] using
        ((tendsto_const_nhds (x := a)).sub
          (continuousWithinAt_id : Tendsto (fun u : ℝ => u) (𝓝[<] a) (𝓝 a)))
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact sub_pos.mpr hu
  have ht' : Tendsto (fun u => bvAnalyticArea h hD d k (E (a - u)))
      (𝓝[<] a) (𝓝 0) := ht.comp hsub
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht'
    (Eventually.of_forall fun _ => bot_le)
  exact Eventually.of_forall fun u => measure_mono (fun p hp =>
    ⟨⟨hu₀.trans hp.1.1, hp.1.2.trans_lt hp.2.1⟩,
      by simpa only [sub_sub_cancel] using hp.2.1, hp.2.2⟩)

/-- The actual area rectangles in (6.10b) shrink to zero.
They are dominated by nested strips inside the global domain. -/
theorem bv_area_incoming_closed_rectangle_tendsto
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a b : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun v => bvAnalyticArea h hD d k (Ioo a v ×ˢ Icc v b)) (𝓝[>] a) (𝓝 0) := by
  let E := fun v : ℝ => globalDomain ∩ {p : ℝ × ℝ | a < p.1 ∧ p.1 < v}
  have hglobal : MeasurableSet globalDomain :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd)
  have hE (v : ℝ) : MeasurableSet (E v) :=
    hglobal.inter ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_const))
  have hm (v w : ℝ) (_hv : a < v) (hvw : v ≤ w) : E v ⊆ E w := by
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.trans_le hvw⟩
  have he : (⋂ v > a, E v) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hp' (v : ℝ) (hv : a < v) : p ∈ E v :=
      mem_iInter.mp (mem_iInter.mp hp v) hv
    have hpa := (hp' (a + 1) (lt_add_one a)).2.1
    have hmid : a < (a + p.1) / 2 := by linarith only [hpa]
    have hpv := (hp' _ hmid).2.2
    linarith only [hpv, hpa]
  have ht := tendsto_measure_biInter_gt (μ := bvAnalyticArea h hD d k)
    (s := E) (fun v _ => (hE v).nullMeasurableSet) hm
    ⟨a + 1, lt_add_one a,
      (bv_analytic_area_subset_finite h hD d k (fun _ hp => hp.1)).2⟩
  have ht' : Tendsto (fun v => bvAnalyticArea h hD d k (E v)) (𝓝[>] a) (𝓝 0) := by
    simpa only [he, measure_empty, Function.comp_def] using ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht'
    (Eventually.of_forall fun _ => bot_le)
  exact Eventually.of_forall fun v => measure_mono (fun p hp =>
    ⟨⟨ha.trans hp.1.1.le, hp.1.2.trans_le hp.2.1⟩, hp.1.1, hp.1.2⟩)

/-- The source outgoing scalar residual limit (6.7b). It uses the fixed
initial-edge residual's finite variation and the actual carrier tail. -/
theorem eq6_7b
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun u => eVariationOn (bvOutgoingScalarResidual d.scalarRightFields u a)
      (Ioo u a)) (𝓝[<] a) (𝓝 0) := by
  let c := a / 2
  have hc : 0 < c := half_pos ha
  have hca : c < a := half_lt_self ha
  have hf := (bv_outgoing_scalar_residual_bv h hD d (u := 0) le_rfl hc hca.le).mono
    Ioo_subset_Icc_self
  have hfixed := bv_variation_left_tail_tendsto_zero hca hf
  have harea := bv_area_outgoing_closed_rectangle_tendsto h hD d .lamPhi (a := a) (u₀ := 0) le_rfl
  have hsum : Tendsto (fun u =>
      eVariationOn (bvOutgoingScalarResidual d.scalarRightFields 0 a) (Ioo u a) +
        bvAnalyticArea h hD d .lamPhi (Icc 0 u ×ˢ Ioo u a)) (𝓝[<] a) (𝓝 0) := by
    simpa only [add_zero] using hfixed.add harea
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [Ioo_mem_nhdsLT ha] with u hu
  exact (bv_outgoing_scalar_transport h hD d (u₀ := 0) le_rfl hu.1.le hu.2).trans
    (add_le_add le_rfl (measure_mono (Set.prod_mono Ioo_subset_Icc_self Subset.rfl)))

end ChristodoulouBV

end
