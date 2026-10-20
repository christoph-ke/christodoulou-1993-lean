module

public import ChristodoulouBV.Frozen.Fields

/-! The four small variation limits at the axis. -/

@[expose] public section

open scoped Topology

namespace ChristodoulouBV

/-- Item 4, with the four printed `δ` ranges; each variation is restricted to `U`.
Christodoulou 1993, p. 1146; `source/transcription/s3-uniqueness.tex:33-41`. -/
structure AxisVanishingVariation (U : Set (ℝ × ℝ)) (S : Fields) (a : ℝ) : Prop where
  past_outgoing : Filter.Tendsto
    (fun ε : ℝ => ⨆ δ ∈ Set.Ioc (0 : ℝ) ε,
      eVariationOn (S.phi (a - δ))
        {v | v ∈ Set.Ioo (a - δ) a ∧ (a - δ, v) ∈ U})
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (0 : ENNReal))
  past_incoming : Filter.Tendsto
    (fun ε : ℝ => ⨆ δ ∈ Set.Ico (0 : ℝ) ε,
      eVariationOn (fun u => S.phi u (a - δ))
        {u | u ∈ Set.Ioo (a - ε) (a - δ) ∧ (u, a - δ) ∈ U})
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (0 : ENNReal))
  future_incoming : Filter.Tendsto
    (fun ε : ℝ => ⨆ δ ∈ Set.Ioc (0 : ℝ) ε,
      eVariationOn (fun u => S.phi u (a + δ))
        {u | u ∈ Set.Ioo a (a + δ) ∧ (u, a + δ) ∈ U})
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (0 : ENNReal))
  future_outgoing : Filter.Tendsto
    (fun ε : ℝ => ⨆ δ ∈ Set.Ico (0 : ℝ) ε,
      eVariationOn (S.phi (a + δ))
        {v | v ∈ Set.Ioo (a + δ) (a + ε) ∧ (a + δ, v) ∈ U})
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (0 : ENNReal))

end ChristodoulouBV

end
