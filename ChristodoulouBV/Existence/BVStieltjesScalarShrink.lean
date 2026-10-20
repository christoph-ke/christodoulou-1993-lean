module

public import ChristodoulouBV.Existence.BVStieltjesScalarTransport
public import ChristodoulouBV.Existence.BVStieltjesShrink
public import ChristodoulouBV.Existence.AreaLimitBounds
import Mathlib.Tactic

/-!
# Shrinking incoming scalar residuals

The fixed terminal edge has finite pointwise variation. Its open
variation tail and a nested containing strip for the finite analytic
area vanish separately.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The canonical incoming scalar residual has finite variation on
every compact off-axis segment of a fixed terminal edge. -/
theorem bv_incoming_scalar_residual_bv
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a c b : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) (hcb : c < b) :
    BoundedVariationOn (bvIncomingScalarResidual d.scalarRightFields b a) (Icc a c) := by
  obtain ⟨K, _, hζ⟩ := bv_item5 h hD d
  have hz : BoundedVariationOn (fun s => d.scalarRightFields.zeta s b) (Icc a c) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((eVariationOn.mono _ (fun s hs =>
        show (s, b) ∈ globalDomain from ⟨ha.trans hs.1, hs.2.trans_lt hcb⟩)).trans (hζ b))
  let q := fun z : Fin 9 → ℝ => z 2 * ((z 5 - z 2 * z 3) * z 0)
  have hq : Continuous q := by fun_prop
  have hi := bv_area_algebra_intervalIntegrable h hD d .nuPhi hac (sub_pos.mpr hcb)
    (fun s hs => show (s, b) ∈ globalDomain from ⟨ha.trans hs.1, hs.2.trans_lt hcb⟩)
    (fun s hs => show b - c ≤ b - s from sub_le_sub_left hs.2 b) hq
  have hi' : IntervalIntegrable (fun s => d.scalarRightFields.nu s b *
      (d.scalarRightFields.zeta s b / d.scalarRightFields.r s b)) volume a c := by
    change IntervalIntegrable (fun s => d.scalarRightFields.nu s b *
      ((d.scalarRightFields.beta s b - d.scalarRightFields.nu s b *
        d.scalarRightFields.phi s b) * (d.scalarRightFields.r s b)⁻¹)) volume a c at hi
    simpa only [Fields.zeta, div_eq_mul_inv] using hi
  have hInt :=
    (hi'.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).boundedVariationOn
  rw [uIcc_of_le hac] at hInt
  exact hz.add hInt

/-- The actual area rectangles in (6.10b) shrink to zero.
They are dominated by nested strips inside the global domain. -/
theorem bv_area_incoming_rectangle_tendsto
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) {a b : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun v => bvAnalyticArea h hD d k (Ioo a v ×ˢ Ioo v b)) (𝓝[>] a) (𝓝 0) := by
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
    ⟨⟨ha.trans hp.1.1.le, hp.1.2.trans hp.2.1⟩, hp.1.1, hp.1.2⟩)

/-- The source incoming scalar residual limit (6.10b). The fixed-edge
variation and analytic-area limits are proved independently. -/
theorem eq6_10b
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun v => eVariationOn (bvIncomingScalarResidual d.scalarRightFields v a)
      (Ioo a v)) (𝓝[>] a) (𝓝 0) := by
  let c := (a + b) / 2
  have hac : a < c := by dsimp only [c]; linarith only [hab]
  have hcb : c < b := by dsimp only [c]; linarith only [hab]
  have hf := (bv_incoming_scalar_residual_bv h hD d ha.le hac.le hcb).mono Ioo_subset_Icc_self
  have hfixed := bv_variation_right_tail_tendsto_zero hac hf
  have harea := bv_area_incoming_rectangle_tendsto h hD d .nuPhi (b := b) ha.le
  have hsum : Tendsto (fun v =>
      eVariationOn (bvIncomingScalarResidual d.scalarRightFields b a) (Ioo a v) +
        bvAnalyticArea h hD d .nuPhi (Ioo a v ×ˢ Ioo v b)) (𝓝[>] a) (𝓝 0) := by
    simpa only [add_zero] using hfixed.add harea
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [Ioo_mem_nhdsGT hab] with v hv
  exact eq6_10a h hD d ha hv.1 hv.2

end ChristodoulouBV

end
