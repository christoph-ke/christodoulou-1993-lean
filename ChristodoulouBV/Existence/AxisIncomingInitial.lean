module

public import ChristodoulouBV.Existence.AxisOutgoing
import Mathlib.Tactic

/-!
# Initial endpoint of the outgoing uniform corner estimate

At axis parameter zero, the closed lower edge of the BV logarithmic
transport is retained. The resulting half-open triangles shrink to the
empty set inside the finite global carrier. This supplies the endpoint
missing from the positive-basepoint statement (6.15).
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem initial_triangle_tendsto
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (k : AreaSectionPair) :
    Tendsto (fun ε => bvAnalyticArea h hD d k
      {p | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < ε}) (𝓝[>] 0) (𝓝 0) := by
  apply bv_analytic_area_shrinking_right h hD d k
  · intro ε _
    exact (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const))
  · intro ε η _ hεη p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.trans_le hεη⟩
  · exact ⟨1, zero_lt_one, fun _ hp => ⟨hp.1, hp.2.1⟩⟩
  · apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hp1 := mem_iInter.mp (mem_iInter.mp hp 1) zero_lt_one
    have hg : 0 < p.2 := hp1.1.trans_lt hp1.2.1
    have hp2 := mem_iInter.mp (mem_iInter.mp hp (p.2 / 2)) (half_pos hg)
    exact (not_lt_of_ge (half_le_self hg.le)) hp2.2.2

private theorem initial_residuals_tendsto
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) :
    Tendsto (fun ε => ⨆ u ∈ Ioo 0 ε, eVariationOn
      (bvOutgoingScalarResidual d.scalarRightFields u ε) (Ioo u ε))
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε => ⨆ u ∈ Ioo 0 ε, eVariationOn
      (bvOutgoingLogResidual d.scalarRightFields u ε) (Ioo u ε))
      (𝓝[>] 0) (𝓝 0) := by
  have hR := (bv_outgoing_scalar_edge_tendsto h hD d (a := 0) le_rfl).add
    (initial_triangle_tendsto h hD d .lamPhi)
  have hG := (bv_outgoing_log_edge_tendsto h hD d (a := 0) le_rfl).add
    (initial_triangle_tendsto h hD d .phiBetaNu)
  simp only [zero_add, add_zero] at hR hG
  constructor
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hR
      (Eventually.of_forall fun _ => bot_le)
    apply Eventually.of_forall
    intro ε
    refine iSup_le fun u => iSup_le fun hu => ?_
    exact (bv_outgoing_scalar_transport h hD d le_rfl hu.1.le hu.2).trans
      (add_le_add (eVariationOn.mono _ (Ioo_subset_Ioo_left hu.1.le))
        (measure_mono (fun _ hp => ⟨hp.1.1.le, hp.1.2.trans hp.2.1, hp.2.2⟩)))
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hG
      (Eventually.of_forall fun _ => bot_le)
    apply Eventually.of_forall
    intro ε
    refine iSup_le fun u => iSup_le fun hu => ?_
    exact (bv_outgoing_log_transport h hD d le_rfl hu.1.le hu.2).trans
      (add_le_add (eVariationOn.mono _ (Ioo_subset_Ioo_left hu.1.le))
        (measure_mono (fun _ hp => ⟨hp.1.1, hp.1.2.trans_lt hp.2.1, hp.2.2⟩)))

/-- The uniform outgoing quotient and logarithmic variations also vanish
at the initial axis parameter. The terminal cutoff remains open. -/
theorem bv_outgoing_uniform_corner_initial
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (hsmall : D < ENNReal.ofReal epsilonChosen)
    :
    Tendsto (fun ε => ⨆ u ∈ Ioo 0 ε, eVariationOn
      (fun t => d.scalarRightFields.alpha u t / d.scalarRightFields.lam u t)
        (Ioo u ε)) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε => ⨆ u ∈ Ioo 0 ε, eVariationOn
      (fun t => Real.log (d.scalarRightFields.lam u t)) (Ioo u ε))
        (𝓝[>] 0) (𝓝 0) := by
  let S := d.scalarRightFields
  let Q := fun ε u => eVariationOn (fun t => S.alpha u t / S.lam u t) (Ioo u ε)
  let L := fun ε u => eVariationOn (fun t => Real.log (S.lam u t)) (Ioo u ε)
  let R := fun ε u => eVariationOn (bvOutgoingScalarResidual S u ε) (Ioo u ε)
  let G := fun ε u => eVariationOn (bvOutgoingLogResidual S u ε) (Ioo u ε)
  let κ := (10 : ℝ) ^ (65 : ℕ) * D.toReal
  have hκ := bv_absorption_coefficient_small hsmall
  have hM : 3 * ENNReal.ofReal (s6EndpointTVK * D.toReal) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hbound (ε : ℝ) :
      (⨆ u ∈ Ioo 0 ε, Q ε u) ≤ 3 * ENNReal.ofReal (s6EndpointTVK * D.toReal) ∧
      (⨆ u ∈ Ioo 0 ε, L ε u) ≤ 3 * ENNReal.ofReal (s6EndpointTVK * D.toReal) := by
    have hb (u : ℝ) (hu : u ∈ Ioo 0 ε) :=
      (scalar_right_fields_three_term_tv h hD d).1 u hu.1.le
    constructor
    · refine iSup_le fun u => iSup_le fun hu => ?_
      have ht := hb u hu
      change _ + _ + _ ≤ _ at ht
      exact (eVariationOn.mono _ Ioo_subset_Ioi_self).trans
        ((le_add_of_nonneg_right bot_le).trans
          ((le_add_of_nonneg_right bot_le).trans ht))
    · refine iSup_le fun u => iSup_le fun hu => ?_
      have ht := hb u hu
      change _ + _ + _ ≤ _ at ht
      exact (eVariationOn.mono _ Ioo_subset_Ioi_self).trans
        ((le_add_of_nonneg_left bot_le).trans ht)
  have hQfin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (⨆ u ∈ Ioo 0 ε, Q ε u) ≠ ∞ :=
    Eventually.of_forall fun ε => ne_top_of_le_ne_top hM (hbound ε).1
  have hLfin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (⨆ u ∈ Ioo 0 ε, L ε u) ≠ ∞ :=
    Eventually.of_forall fun ε => ne_top_of_le_ne_top hM (hbound ε).2
  have hQ : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (⨆ u ∈ Ioo 0 ε, Q ε u) ≤
        3 * (⨆ u ∈ Ioo 0 ε, R ε u) +
          ENNReal.ofReal κ * (⨆ u ∈ Ioo 0 ε, L ε u) := by
    apply Eventually.of_forall
    intro ε
    refine iSup_le fun u => iSup_le fun hu => ?_
    exact (bv_outgoing_quotient_residual_bound h hD d hu.1.le hu.2).trans
      (add_le_add
        (mul_le_mul le_rfl (le_iSup_of_le u (le_iSup_of_le hu le_rfl)) bot_le bot_le)
        (mul_le_mul le_rfl (le_iSup_of_le u (le_iSup_of_le hu le_rfl)) bot_le bot_le))
  have hL : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (⨆ u ∈ Ioo 0 ε, L ε u) ≤
        (⨆ u ∈ Ioo 0 ε, G ε u) +
          ENNReal.ofReal κ * (⨆ u ∈ Ioo 0 ε, Q ε u) := by
    apply Eventually.of_forall
    intro ε
    refine iSup_le fun u => iSup_le fun hu => ?_
    exact (bv_outgoing_log_residual_bound h hD d hu.1.le hu.2).trans
      (add_le_add (le_iSup_of_le u (le_iSup_of_le hu le_rfl))
        (mul_le_mul le_rfl (le_iSup_of_le u (le_iSup_of_le hu le_rfl)) bot_le bot_le))
  exact tendsto_zero_of_coupled_ennreal_variation_bounds hκ.1 hκ.2 hQfin hLfin hQ hL
    (initial_residuals_tendsto h hD d).1 (initial_residuals_tendsto h hD d).2

end ChristodoulouBV

end
