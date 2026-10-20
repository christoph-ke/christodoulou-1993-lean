module

public import ChristodoulouBV.Uniqueness.RescalingBasic

/-!
# Axis variation under affine rescaling

The four one-sided variation limits in item 4 retain their source bounds
after restricting the domain to the new initial outgoing edge.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- A positive scaling tends to zero through positive arguments. -/
theorem positive_scale_tendsto {h : ℝ} (hh : 0 < h) :
    Tendsto (fun ε : ℝ => h * ε) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [mul_zero] using
      (((show Continuous (fun ε : ℝ => h * ε) by fun_prop).tendsto 0).mono_left
        nhdsWithin_le_nhds)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact mul_pos hh hε

/-- A nonnegative variation bounded by an old scaled variation also vanishes. -/
theorem tendsto_zero_of_le_scaled {F G : ℝ → ENNReal} {h : ℝ}
    (hh : 0 < h) (hF : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (0 : ENNReal)))
    (hGF : ∀ ε, G ε ≤ F (h * ε)) :
    Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 (0 : ENNReal)) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hF.comp (positive_scale_tendsto hh)) (fun _ => bot_le) hGF

/-- Affine coordinates commute with subtraction of a null displacement. -/
theorem affineCoordinate_sub (a h b δ : ℝ) :
    affineCoordinate a h (b - δ) = affineCoordinate a h b - h * δ := by
  unfold affineCoordinate
  ring

/-- Affine coordinates commute with addition of a null displacement. -/
theorem affineCoordinate_add (a h b δ : ℝ) :
    affineCoordinate a h (b + δ) = affineCoordinate a h b + h * δ := by
  unfold affineCoordinate
  ring

/-- Past outgoing variation near an axis parameter. -/
noncomputable def pastOutgoingVariation (U : Set (ℝ × ℝ)) (S : Fields) (b ε : ℝ) : ENNReal :=
  ⨆ δ ∈ Set.Ioc (0 : ℝ) ε,
    eVariationOn (S.phi (b - δ))
      {v | v ∈ Set.Ioo (b - δ) b ∧ (b - δ, v) ∈ U}

/-- Past incoming variation near an axis parameter. -/
noncomputable def pastIncomingVariation (U : Set (ℝ × ℝ)) (S : Fields) (b ε : ℝ) : ENNReal :=
  ⨆ δ ∈ Set.Ico (0 : ℝ) ε,
    eVariationOn (fun u => S.phi u (b - δ))
      {u | u ∈ Set.Ioo (b - ε) (b - δ) ∧ (u, b - δ) ∈ U}

/-- Future incoming variation near an axis parameter. -/
noncomputable def futureIncomingVariation (U : Set (ℝ × ℝ)) (S : Fields) (b ε : ℝ) : ENNReal :=
  ⨆ δ ∈ Set.Ioc (0 : ℝ) ε,
    eVariationOn (fun u => S.phi u (b + δ))
      {u | u ∈ Set.Ioo b (b + δ) ∧ (u, b + δ) ∈ U}

/-- Future outgoing variation near an axis parameter. -/
noncomputable def futureOutgoingVariation (U : Set (ℝ × ℝ)) (S : Fields) (b ε : ℝ) : ENNReal :=
  ⨆ δ ∈ Set.Ico (0 : ℝ) ε,
    eVariationOn (S.phi (b + δ))
      {v | v ∈ Set.Ioo (b + δ) (b + ε) ∧ (b + δ, v) ∈ U}

/-- The rescaled past outgoing variation is bounded by the old variation
at the correspondingly scaled radius. -/
theorem rescaled_pastOutgoingVariation_le (U : Set (ℝ × ℝ)) (S : Fields)
    {a h : ℝ} (hh : 0 < h) (b ε : ℝ) :
    pastOutgoingVariation (rescaledDomain U a h) (rescaledFields S a h) b ε ≤
      pastOutgoingVariation U S (affineCoordinate a h b) (h * ε) := by
  unfold pastOutgoingVariation
  refine iSup_le fun δ => iSup_le fun hδ => ?_
  have hδ' : h * δ ∈ Set.Ioc (0 : ℝ) (h * ε) :=
    ⟨mul_pos hh hδ.1, mul_le_mul_of_nonneg_left hδ.2 hh.le⟩
  calc
    eVariationOn ((rescaledFields S a h).phi (b - δ))
        {v | v ∈ Set.Ioo (b - δ) b ∧
          (b - δ, v) ∈ rescaledDomain U a h} ≤
      eVariationOn (S.phi (affineCoordinate a h b - h * δ))
        {w | w ∈ Set.Ioo (affineCoordinate a h b - h * δ)
          (affineCoordinate a h b) ∧
          (affineCoordinate a h b - h * δ, w) ∈ U} := by
      change eVariationOn (fun v =>
          S.phi (affineCoordinate a h (b - δ)) (affineCoordinate a h v)) _ ≤ _
      rw [affineCoordinate_sub]
      apply eVariationOn_affine_le
        (f := S.phi (affineCoordinate a h b - h * δ))
        (s := {w | w ∈ Set.Ioo (affineCoordinate a h b - h * δ)
          (affineCoordinate a h b) ∧
          (affineCoordinate a h b - h * δ, w) ∈ U})
        (t := {v | v ∈ Set.Ioo (b - δ) b ∧
          (b - δ, v) ∈ rescaledDomain U a h}) hh
      intro v hv
      refine ⟨?_, ?_⟩
      · rw [← affineCoordinate_sub]
        exact ⟨affineCoordinate_strictMono hh hv.1.1,
          affineCoordinate_strictMono hh hv.1.2⟩
      · simpa only [← affineCoordinate_sub] using hv.2.2
    _ ≤ ⨆ δ' ∈ Set.Ioc (0 : ℝ) (h * ε),
        eVariationOn (S.phi (affineCoordinate a h b - δ'))
          {w | w ∈ Set.Ioo (affineCoordinate a h b - δ')
            (affineCoordinate a h b) ∧
            (affineCoordinate a h b - δ', w) ∈ U} :=
      le_iSup_of_le (h * δ) (le_iSup_of_le hδ' le_rfl)

/-- The rescaled past incoming variation is bounded by the old variation
at the correspondingly scaled radius. -/
theorem rescaled_pastIncomingVariation_le (U : Set (ℝ × ℝ)) (S : Fields)
    {a h : ℝ} (hh : 0 < h) (b ε : ℝ) :
    pastIncomingVariation (rescaledDomain U a h) (rescaledFields S a h) b ε ≤
      pastIncomingVariation U S (affineCoordinate a h b) (h * ε) := by
  unfold pastIncomingVariation
  refine iSup_le fun δ => iSup_le fun hδ => ?_
  have hδ' : h * δ ∈ Set.Ico (0 : ℝ) (h * ε) :=
    ⟨mul_nonneg hh.le hδ.1, mul_lt_mul_of_pos_left hδ.2 hh⟩
  calc
    eVariationOn (fun u => (rescaledFields S a h).phi u (b - δ))
        {u | u ∈ Set.Ioo (b - ε) (b - δ) ∧
          (u, b - δ) ∈ rescaledDomain U a h} ≤
      eVariationOn (fun w => S.phi w (affineCoordinate a h b - h * δ))
        {w | w ∈ Set.Ioo (affineCoordinate a h b - h * ε)
          (affineCoordinate a h b - h * δ) ∧
          (w, affineCoordinate a h b - h * δ) ∈ U} := by
      change eVariationOn (fun u =>
          S.phi (affineCoordinate a h u) (affineCoordinate a h (b - δ))) _ ≤ _
      rw [affineCoordinate_sub]
      apply eVariationOn_affine_le
        (f := fun w => S.phi w (affineCoordinate a h b - h * δ))
        (s := {w | w ∈ Set.Ioo (affineCoordinate a h b - h * ε)
          (affineCoordinate a h b - h * δ) ∧
          (w, affineCoordinate a h b - h * δ) ∈ U})
        (t := {u | u ∈ Set.Ioo (b - ε) (b - δ) ∧
          (u, b - δ) ∈ rescaledDomain U a h}) hh
      intro u hu
      refine ⟨?_, ?_⟩
      · rw [← affineCoordinate_sub, ← affineCoordinate_sub]
        exact ⟨affineCoordinate_strictMono hh hu.1.1,
          affineCoordinate_strictMono hh hu.1.2⟩
      · simpa only [← affineCoordinate_sub] using hu.2.2
    _ ≤ ⨆ δ' ∈ Set.Ico (0 : ℝ) (h * ε),
        eVariationOn (fun w => S.phi w (affineCoordinate a h b - δ'))
          {w | w ∈ Set.Ioo (affineCoordinate a h b - h * ε)
            (affineCoordinate a h b - δ') ∧
            (w, affineCoordinate a h b - δ') ∈ U} :=
      le_iSup_of_le (h * δ) (le_iSup_of_le hδ' le_rfl)

/-- The rescaled future incoming variation is bounded by the old variation
at the correspondingly scaled radius. -/
theorem rescaled_futureIncomingVariation_le (U : Set (ℝ × ℝ)) (S : Fields)
    {a h : ℝ} (hh : 0 < h) (b ε : ℝ) :
    futureIncomingVariation (rescaledDomain U a h) (rescaledFields S a h) b ε ≤
      futureIncomingVariation U S (affineCoordinate a h b) (h * ε) := by
  unfold futureIncomingVariation
  refine iSup_le fun δ => iSup_le fun hδ => ?_
  have hδ' : h * δ ∈ Set.Ioc (0 : ℝ) (h * ε) :=
    ⟨mul_pos hh hδ.1, mul_le_mul_of_nonneg_left hδ.2 hh.le⟩
  calc
    eVariationOn (fun u => (rescaledFields S a h).phi u (b + δ))
        {u | u ∈ Set.Ioo b (b + δ) ∧
          (u, b + δ) ∈ rescaledDomain U a h} ≤
      eVariationOn (fun w => S.phi w (affineCoordinate a h b + h * δ))
        {w | w ∈ Set.Ioo (affineCoordinate a h b)
          (affineCoordinate a h b + h * δ) ∧
          (w, affineCoordinate a h b + h * δ) ∈ U} := by
      change eVariationOn (fun u =>
          S.phi (affineCoordinate a h u) (affineCoordinate a h (b + δ))) _ ≤ _
      rw [affineCoordinate_add]
      apply eVariationOn_affine_le
        (f := fun w => S.phi w (affineCoordinate a h b + h * δ))
        (s := {w | w ∈ Set.Ioo (affineCoordinate a h b)
          (affineCoordinate a h b + h * δ) ∧
          (w, affineCoordinate a h b + h * δ) ∈ U})
        (t := {u | u ∈ Set.Ioo b (b + δ) ∧
          (u, b + δ) ∈ rescaledDomain U a h}) hh
      intro u hu
      refine ⟨?_, ?_⟩
      · rw [← affineCoordinate_add]
        exact ⟨affineCoordinate_strictMono hh hu.1.1,
          affineCoordinate_strictMono hh hu.1.2⟩
      · simpa only [← affineCoordinate_add] using hu.2.2
    _ ≤ ⨆ δ' ∈ Set.Ioc (0 : ℝ) (h * ε),
        eVariationOn (fun w => S.phi w (affineCoordinate a h b + δ'))
          {w | w ∈ Set.Ioo (affineCoordinate a h b)
            (affineCoordinate a h b + δ') ∧
            (w, affineCoordinate a h b + δ') ∈ U} :=
      le_iSup_of_le (h * δ) (le_iSup_of_le hδ' le_rfl)

/-- The rescaled future outgoing variation is bounded by the old variation
at the correspondingly scaled radius. -/
theorem rescaled_futureOutgoingVariation_le (U : Set (ℝ × ℝ)) (S : Fields)
    {a h : ℝ} (hh : 0 < h) (b ε : ℝ) :
    futureOutgoingVariation (rescaledDomain U a h) (rescaledFields S a h) b ε ≤
      futureOutgoingVariation U S (affineCoordinate a h b) (h * ε) := by
  unfold futureOutgoingVariation
  refine iSup_le fun δ => iSup_le fun hδ => ?_
  have hδ' : h * δ ∈ Set.Ico (0 : ℝ) (h * ε) :=
    ⟨mul_nonneg hh.le hδ.1, mul_lt_mul_of_pos_left hδ.2 hh⟩
  calc
    eVariationOn ((rescaledFields S a h).phi (b + δ))
        {v | v ∈ Set.Ioo (b + δ) (b + ε) ∧
          (b + δ, v) ∈ rescaledDomain U a h} ≤
      eVariationOn (S.phi (affineCoordinate a h b + h * δ))
        {w | w ∈ Set.Ioo (affineCoordinate a h b + h * δ)
          (affineCoordinate a h b + h * ε) ∧
          (affineCoordinate a h b + h * δ, w) ∈ U} := by
      change eVariationOn (fun v =>
          S.phi (affineCoordinate a h (b + δ)) (affineCoordinate a h v)) _ ≤ _
      rw [affineCoordinate_add]
      apply eVariationOn_affine_le
        (f := S.phi (affineCoordinate a h b + h * δ))
        (s := {w | w ∈ Set.Ioo (affineCoordinate a h b + h * δ)
          (affineCoordinate a h b + h * ε) ∧
          (affineCoordinate a h b + h * δ, w) ∈ U})
        (t := {v | v ∈ Set.Ioo (b + δ) (b + ε) ∧
          (b + δ, v) ∈ rescaledDomain U a h}) hh
      intro v hv
      refine ⟨?_, ?_⟩
      · rw [← affineCoordinate_add, ← affineCoordinate_add]
        exact ⟨affineCoordinate_strictMono hh hv.1.1,
          affineCoordinate_strictMono hh hv.1.2⟩
      · simpa only [← affineCoordinate_add] using hv.2.2
    _ ≤ ⨆ δ' ∈ Set.Ico (0 : ℝ) (h * ε),
        eVariationOn (S.phi (affineCoordinate a h b + δ'))
          {w | w ∈ Set.Ioo (affineCoordinate a h b + δ')
            (affineCoordinate a h b + h * ε) ∧
            (affineCoordinate a h b + δ', w) ∈ U} :=
      le_iSup_of_le (h * δ) (le_iSup_of_le hδ' le_rfl)

/-- All four axis-vanishing variation limits survive affine rescaling,
including the new initial outgoing edge. -/
theorem rescaled_item4 {U : Set (ℝ × ℝ)} {S : Fields}
    (hS : IsBVSolution U S) {a h : ℝ} (hh : 0 < h) :
    ∀ b ∈ adjacentAxis (rescaledDomain U a h),
      AxisVanishingVariation (rescaledDomain U a h) (rescaledFields S a h) b := by
  intro b hb
  have hc := affineCoordinate_mem_adjacentAxis hb
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hS.item4 _ hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Tendsto (pastOutgoingVariation (rescaledDomain U a h)
      (rescaledFields S a h) b) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ENNReal))
    exact tendsto_zero_of_le_scaled hh h₁
      (rescaled_pastOutgoingVariation_le U S hh b)
  · change Tendsto (pastIncomingVariation (rescaledDomain U a h)
      (rescaledFields S a h) b) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ENNReal))
    exact tendsto_zero_of_le_scaled hh h₂
      (rescaled_pastIncomingVariation_le U S hh b)
  · change Tendsto (futureIncomingVariation (rescaledDomain U a h)
      (rescaledFields S a h) b) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ENNReal))
    exact tendsto_zero_of_le_scaled hh h₃
      (rescaled_futureIncomingVariation_le U S hh b)
  · change Tendsto (futureOutgoingVariation (rescaledDomain U a h)
      (rescaledFields S a h) b) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ENNReal))
    exact tendsto_zero_of_le_scaled hh h₄
      (rescaled_futureOutgoingVariation_le U S hh b)

end ChristodoulouBV.Uniqueness

end
