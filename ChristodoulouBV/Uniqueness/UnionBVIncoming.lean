module

public import ChristodoulouBV.Uniqueness.UnionBVIncomingBound

/-!
# Incoming variation of the selected union fields

The incoming slices may be disconnected at a terminal outgoing level. The
finite partition bound handles all three required BV quantities there.
-/

public section

namespace ChristodoulouBV.Uniqueness

/-- The selected scalar field has one uniform incoming variation bound on
the entire union. -/
theorem glued_phi_variation_incoming_le
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    (v : ℝ) :
    eVariationOn (fun u => (gluedFields U₁ S₁ S₂).phi u v)
      {u | (u, v) ∈ U₁ ∪ U₂} ≤
      max (ENNReal.ofReal h₁.item3_variation.choose)
        (ENNReal.ofReal h₂.item3_variation.choose) := by
  apply incoming_variation_union_le_max h₁.solution.development
    h₂.solution.development
      (fun t => h₁.item3_variation.choose_spec.2 t)
      (fun t => h₂.item3_variation.choose_spec.2 t)
  · intro v' b s hb hs hsb
    exact (first_source_fields_tendsto_incoming_terminal
      h₁ h₂ hdata hb hs hsb).2.1
  · intro v' b s hb hs hsb
    exact (second_source_fields_tendsto_incoming_terminal
      h₁ h₂ hdata hb hs hsb).2.1

/-- The selected incoming expansion has one uniform variation bound on
the union. -/
theorem glued_nu_variation_incoming_le
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    (v : ℝ) :
    eVariationOn (fun u => (gluedFields U₁ S₁ S₂).nu u v)
      {u | (u, v) ∈ U₁ ∪ U₂} ≤
      max (ENNReal.ofReal h₁.item1.choose)
        (ENNReal.ofReal h₂.item1.choose) := by
  apply incoming_variation_union_le_max h₁.solution.development
    h₂.solution.development
      (fun t => h₁.item1.choose_spec.2 t)
      (fun t => h₂.item1.choose_spec.2 t)
  · intro v' b s hb hs hsb
    exact (first_source_fields_tendsto_incoming_terminal
      h₁ h₂ hdata hb hs hsb).2.2.2.1
  · intro v' b s hb hs hsb
    exact (second_source_fields_tendsto_incoming_terminal
      h₁ h₂ hdata hb hs hsb).2.2.2.1

/-- The selected incoming scalar amplitude has one uniform variation bound
on the union. -/
theorem glued_zeta_variation_incoming_le
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    (v : ℝ) :
    eVariationOn (fun u => (gluedFields U₁ S₁ S₂).zeta u v)
      {u | (u, v) ∈ U₁ ∪ U₂} ≤
      max (ENNReal.ofReal h₁.item5.choose)
        (ENNReal.ofReal h₂.item5.choose) := by
  apply incoming_variation_union_le_max h₁.solution.development
    h₂.solution.development
      (fun t => h₁.item5.choose_spec.2 t)
      (fun t => h₂.item5.choose_spec.2 t)
  · intro v' b s hb hs hsb
    exact (source_zeta_tendsto_incoming_terminal h₁ h₂ hdata hs hsb).1 hb
  · intro v' b s hb hs hsb
    exact (source_zeta_tendsto_incoming_terminal h₁ h₂ hdata hs hsb).2 hb

end ChristodoulouBV.Uniqueness

end
