module

public import ChristodoulouBV.Uniqueness.UnionBVAxisEmpty

/-!
# Item 4 on the union

The four local variation functions are bounded by the maximum of the two
source functions. Both source limits are available at every axis parameter,
including parameters not adjacent to one source.
-/

@[expose] public section

open Set Filter
open scoped Topology ENNReal

namespace ChristodoulouBV.Uniqueness

/-- The selected scalar field satisfies all four vanishing-variation limits
on the union, at every axis parameter. -/
theorem glued_item4_axis
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    (a : ℝ) : AxisVanishingVariation (U₁ ∪ U₂)
      (gluedFields U₁ S₁ S₂) a := by
  have hA₁ := IsBVSolution.axisVanishingVariation_all h₁ a
  have hA₂ := IsBVSolution.axisVanishingVariation_all h₂ a
  refine {
    past_outgoing := ?_
    past_incoming := ?_
    future_incoming := ?_
    future_outgoing := ?_ }
  · have hmax := hA₁.past_outgoing.max hA₂.past_outgoing
    have hmax' : Tendsto
        (fun ε : ℝ => max
          (⨆ δ ∈ Ioc (0 : ℝ) ε,
            eVariationOn (S₁.phi (a - δ))
              {v | v ∈ Ioo (a - δ) a ∧ (a - δ, v) ∈ U₁})
          (⨆ δ ∈ Ioc (0 : ℝ) ε,
            eVariationOn (S₂.phi (a - δ))
              {v | v ∈ Ioo (a - δ) a ∧ (a - δ, v) ∈ U₂}))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ENNReal)) := by
      simpa only [max_self] using hmax
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hmax' (fun _ => bot_le)
      (glued_past_outgoing_variation_le h₁ h₂ hdata a)
  · have hmax := hA₁.past_incoming.max hA₂.past_incoming
    have hmax' : Tendsto
        (fun ε : ℝ => max
          (⨆ δ ∈ Ico (0 : ℝ) ε,
            eVariationOn (fun u => S₁.phi u (a - δ))
              {u | u ∈ Ioo (a - ε) (a - δ) ∧ (u, a - δ) ∈ U₁})
          (⨆ δ ∈ Ico (0 : ℝ) ε,
            eVariationOn (fun u => S₂.phi u (a - δ))
              {u | u ∈ Ioo (a - ε) (a - δ) ∧ (u, a - δ) ∈ U₂}))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ENNReal)) := by
      simpa only [max_self] using hmax
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hmax' (fun _ => bot_le)
    intro ε
    apply iSup_le
    intro δ
    apply iSup_le
    intro hδ
    exact glued_past_incoming_variation_le h₁ h₂ hdata a ε δ hδ
  · have hmax := hA₁.future_incoming.max hA₂.future_incoming
    have hmax' : Tendsto
        (fun ε : ℝ => max
          (⨆ δ ∈ Ioc (0 : ℝ) ε,
            eVariationOn (fun u => S₁.phi u (a + δ))
              {u | u ∈ Ioo a (a + δ) ∧ (u, a + δ) ∈ U₁})
          (⨆ δ ∈ Ioc (0 : ℝ) ε,
            eVariationOn (fun u => S₂.phi u (a + δ))
              {u | u ∈ Ioo a (a + δ) ∧ (u, a + δ) ∈ U₂}))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ENNReal)) := by
      simpa only [max_self] using hmax
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hmax' (fun _ => bot_le)
    intro ε
    apply iSup_le
    intro δ
    apply iSup_le
    intro hδ
    exact glued_future_incoming_variation_le h₁ h₂ hdata a ε δ hδ
  · have hmax := hA₁.future_outgoing.max hA₂.future_outgoing
    have hmax' : Tendsto
        (fun ε : ℝ => max
          (⨆ δ ∈ Ico (0 : ℝ) ε,
            eVariationOn (S₁.phi (a + δ))
              {v | v ∈ Ioo (a + δ) (a + ε) ∧ (a + δ, v) ∈ U₁})
          (⨆ δ ∈ Ico (0 : ℝ) ε,
            eVariationOn (S₂.phi (a + δ))
              {v | v ∈ Ioo (a + δ) (a + ε) ∧ (a + δ, v) ∈ U₂}))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ENNReal)) := by
      simpa only [max_self] using hmax
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hmax' (fun _ => bot_le)
      (glued_future_outgoing_variation_le h₁ h₂ hdata a)

end ChristodoulouBV.Uniqueness

end
