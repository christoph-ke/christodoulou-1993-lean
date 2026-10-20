module

public import ChristodoulouBV.Existence.AxisIncomingVariation
public import ChristodoulouBV.Existence.AxisIncomingInitial
public import ChristodoulouBV.Existence.Representatives
public import ChristodoulouBV.Frozen.AxisVanishingVariation
import Mathlib.Tactic

/-!
# The four literal scalar variation clauses at the axis

The BV weighted-mean contraction transfers quotient variation to scalar
variation. The closed delta endpoints are handled explicitly: zero delta
uses a fixed scalar edge tail, while the upper endpoint is retained in
the one-sided supremum envelope. At axis parameter zero the past clauses
are empty and the future clauses use the endpoint corner estimates.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem tendsto_axis_add (a : ℝ) :
    Tendsto (fun ε : ℝ => a + ε) (𝓝[>] 0) (𝓝[>] a) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [id_eq, add_zero] using
      (tendsto_const_nhds (x := a)).add
        (continuousWithinAt_id : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact lt_add_of_pos_right a hε

private theorem tendsto_axis_sub (a : ℝ) :
    Tendsto (fun ε : ℝ => a - ε) (𝓝[>] 0) (𝓝[<] a) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [id_eq, sub_zero] using
      (tendsto_const_nhds (x := a)).sub
        (continuousWithinAt_id : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact sub_lt_self a hε

private theorem tendsto_iSup_Ioc_zero {f : ℝ → ℝ≥0∞}
    (hf : Tendsto f (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => ⨆ δ ∈ Ioc (0 : ℝ) ε, f δ) (𝓝[>] 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero] at hf ⊢
  intro r hr
  obtain ⟨b, hb, hfb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hf r hr)
  filter_upwards [Ioo_mem_nhdsGT hb] with ε hε
  exact iSup_le fun δ => iSup_le fun hδ => hfb ⟨hδ.1, hδ.2.trans_lt hε.2⟩

private theorem past_outgoing
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (hsmall : D < ENNReal.ofReal epsilonChosen)
    {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun ε : ℝ => ⨆ δ ∈ Ioc (0 : ℝ) ε,
      eVariationOn (d.scalarRightFields.phi (a - δ))
        {v | v ∈ Ioo (a - δ) a ∧ (a - δ, v) ∈ globalDomain})
      (𝓝[>] 0) (𝓝 0) := by
  rcases ha.eq_or_lt with rfl | ha
  · apply tendsto_const_nhds.congr'
    apply Eventually.of_forall
    intro ε
    symm
    apply le_antisymm _ bot_le
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    have he : {v | v ∈ Ioo (0 - δ) 0 ∧ (0 - δ, v) ∈ globalDomain} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro v ⟨_, hp⟩
      have hp0 : 0 ≤ 0 - δ := hp.1
      linarith only [hp0, hδ.1]
    rw [he, eVariationOn.subsingleton _ Set.subsingleton_empty]
    exact le_rfl
  · have ht := tendsto_iSup_Ioc_zero
      (((eq6_9 h hD d hsmall ha).1).comp (tendsto_axis_sub a))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
      (Eventually.of_forall fun _ => bot_le)
    filter_upwards [Ioo_mem_nhdsGT ha] with ε hε
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    have hδa : δ < a := hδ.2.trans_lt hε.2
    exact ((eVariationOn.mono _ (fun _ hv => hv.1)).trans
      (bv_outgoing_ratio_variation h hD d (sub_nonneg.mpr hδa.le)
        (sub_lt_self a hδ.1))).trans
      (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))

private theorem past_incoming
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (hsmall : D < ENNReal.ofReal epsilonChosen)
    {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun ε : ℝ => ⨆ δ ∈ Ico (0 : ℝ) ε,
      eVariationOn (fun u => d.scalarRightFields.phi u (a - δ))
        {u | u ∈ Ioo (a - ε) (a - δ) ∧ (u, a - δ) ∈ globalDomain})
      (𝓝[>] 0) (𝓝 0) := by
  rcases ha.eq_or_lt with rfl | ha
  · apply tendsto_const_nhds.congr'
    apply Eventually.of_forall
    intro ε
    symm
    apply le_antisymm _ bot_le
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    have he : {u | u ∈ Ioo (0 - ε) (0 - δ) ∧ (u, 0 - δ) ∈ globalDomain} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro u ⟨hu, hp⟩
      have hp0 : 0 ≤ u := hp.1
      linarith only [hp0, hu.2, hδ.1]
    rw [he, eVariationOn.subsingleton _ Set.subsingleton_empty]
    exact le_rfl
  · have hf : BoundedVariationOn (fun u => d.scalarRightFields.phi u a) (Ioo 0 a) :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        ((eVariationOn.mono _ Ioo_subset_Ico_self).trans ((bv_scalar_variation h hD d).2 a ha))
    have ht := ((bv_variation_left_tail_tendsto_zero ha hf).comp (tendsto_axis_sub a))
    have hsum := ((eq6_18 h hD d hsmall ha).1).add ht
    rw [add_zero] at hsum
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => bot_le)
    filter_upwards [Ioo_mem_nhdsGT ha] with ε hε
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    rcases hδ.1.eq_or_lt with rfl | hδ0
    · simp only [sub_zero]
      exact (eVariationOn.mono _ (fun _ hu => hu.1)).trans (le_add_of_nonneg_left bot_le)
    · have hv : a - δ ∈ Ioo (a - ε) a :=
        ⟨sub_lt_sub_left hδ.2 a, sub_lt_self a hδ0⟩
      have hb : eVariationOn (fun t => d.scalarRightFields.beta t (a - δ) /
          d.scalarRightFields.nu t (a - δ)) (Ioo (a - ε) (a - δ)) ≤
          ⨆ v ∈ Ioo (a - ε) a, eVariationOn
            (fun t => d.scalarRightFields.beta t v / d.scalarRightFields.nu t v)
              (Ioo (a - ε) v) :=
        le_iSup_of_le (a - δ) (le_iSup_of_le hv le_rfl)
      exact ((eVariationOn.mono _ (fun _ hu => hu.1)).trans
        (bv_incoming_ratio_variation h hD d (sub_nonneg.mpr hε.2.le) hv.1)).trans
        (hb.trans (le_add_of_nonneg_right bot_le))

private theorem future_incoming
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (hsmall : D < ENNReal.ofReal epsilonChosen)
    {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun ε : ℝ => ⨆ δ ∈ Ioc (0 : ℝ) ε,
      eVariationOn (fun u => d.scalarRightFields.phi u (a + δ))
        {u | u ∈ Ioo a (a + δ) ∧ (u, a + δ) ∈ globalDomain})
      (𝓝[>] 0) (𝓝 0) := by
  have hc : Tendsto (fun v => eVariationOn (fun t => d.scalarRightFields.beta t v /
      d.scalarRightFields.nu t v) (Ioo a v)) (𝓝[>] a) (𝓝 0) := by
    rcases ha.eq_or_lt with rfl | ha
    · exact (representatives_incoming_corner h hD d hsmall (a := 0) le_rfl).1
    · exact (eq6_12 h hD d hsmall ha).1
  have ht := tendsto_iSup_Ioc_zero (hc.comp (tendsto_axis_add a))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall fun _ => bot_le)
  apply Eventually.of_forall
  intro ε
  refine iSup_le fun δ => iSup_le fun hδ => ?_
  exact ((eVariationOn.mono _ (fun _ hu => hu.1)).trans
    (bv_incoming_ratio_variation h hD d ha (lt_add_of_pos_right a hδ.1))).trans
    (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))

private theorem future_outgoing
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (hsmall : D < ENNReal.ofReal epsilonChosen)
    {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun ε : ℝ => ⨆ δ ∈ Ico (0 : ℝ) ε,
      eVariationOn (d.scalarRightFields.phi (a + δ))
        {v | v ∈ Ioo (a + δ) (a + ε) ∧ (a + δ, v) ∈ globalDomain})
      (𝓝[>] 0) (𝓝 0) := by
  have hu : Tendsto (fun ε => ⨆ u ∈ Ioo a (a + ε), eVariationOn
      (fun t => d.scalarRightFields.alpha u t / d.scalarRightFields.lam u t)
        (Ioo u (a + ε))) (𝓝[>] 0) (𝓝 0) := by
    rcases ha.eq_or_lt with rfl | ha
    · simpa only [zero_add] using (bv_outgoing_uniform_corner_initial h hD d hsmall).1
    · exact (eq6_15 h hD d hsmall ha).1
  have hf : BoundedVariationOn (d.scalarRightFields.phi a) (Ioo a (a + 1)) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((eVariationOn.mono _ Ioo_subset_Ioi_self).trans ((bv_scalar_variation h hD d).1 a ha))
  have ht := (bv_variation_right_tail_tendsto_zero (lt_add_one a) hf).comp (tendsto_axis_add a)
  have hsum := hu.add ht
  rw [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le)
  apply Eventually.of_forall
  intro ε
  refine iSup_le fun δ => iSup_le fun hδ => ?_
  rcases hδ.1.eq_or_lt with rfl | hδ0
  · simp only [add_zero]
    exact (eVariationOn.mono _ (fun _ hv => hv.1)).trans (le_add_of_nonneg_left bot_le)
  · have hu : a + δ ∈ Ioo a (a + ε) :=
      ⟨lt_add_of_pos_right a hδ0, by linarith only [hδ.2]⟩
    have hb : eVariationOn (fun t => d.scalarRightFields.alpha (a + δ) t /
        d.scalarRightFields.lam (a + δ) t) (Ioo (a + δ) (a + ε)) ≤
        ⨆ u ∈ Ioo a (a + ε), eVariationOn
          (fun t => d.scalarRightFields.alpha u t / d.scalarRightFields.lam u t)
            (Ioo u (a + ε)) :=
      le_iSup_of_le (a + δ) (le_iSup_of_le hu le_rfl)
    exact ((eVariationOn.mono _ (fun _ hv => hv.1)).trans
      (bv_outgoing_ratio_variation h hD d (ha.trans hu.1.le) hu.2)).trans
      (hb.trans (le_add_of_nonneg_right bot_le))

/-- The ratio-to-scalar bridge supplies all four literal frozen clauses
at every nonnegative axis parameter, including zero and both delta endpoints. -/
theorem s6_item4_bridge
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (hsmall : D < ENNReal.ofReal epsilonChosen)
    {a : ℝ} (ha : 0 ≤ a) : AxisVanishingVariation globalDomain d.scalarRightFields a :=
  ⟨past_outgoing h hD d hsmall ha, past_incoming h hD d hsmall ha,
    future_incoming h hD d hsmall ha, future_outgoing h hD d hsmall ha⟩

/-- Frozen BV item 4 for the canonical limit, on the unchanged global
domain with its initial edge. No right-continuity premise on the data is needed. -/
theorem bv_item4
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (hsmall : D < ENNReal.ofReal epsilonChosen) :
    ∀ a ∈ adjacentAxis globalDomain, AxisVanishingVariation globalDomain d.scalarRightFields a := by
  intro a ha
  have hcl : (a, a) ∈ closure globalDomain := ha
  rw [s6_closure_globalDomain] at hcl
  exact s6_item4_bridge h hD d hsmall hcl.1

/-- Item 4 transfers to the final right-representative witness because all four clauses
refer only to the unchanged scalar field. -/
theorem incoming_right_fields_item4
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (hsmall : D < ENNReal.ofReal epsilonChosen) :
    ∀ a ∈ adjacentAxis globalDomain,
      AxisVanishingVariation globalDomain d.incomingRightFields a := by
  intro a ha
  have hh := bv_item4 h hD d hsmall a ha
  exact ⟨hh.past_outgoing, hh.past_incoming, hh.future_incoming, hh.future_outgoing⟩

end ChristodoulouBV

end
