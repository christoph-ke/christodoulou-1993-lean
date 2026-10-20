module

public import ChristodoulouBV.Uniqueness.UnionBVAxisIncomingPast

/-!
# Outgoing axis variation on the union

The largest point of a finite outgoing partition selects a source that
contains every earlier point, including on truncated axis intervals.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace ChristodoulouBV.Uniqueness

/-- Scalar variation on any restricted outgoing union slice is at most the
larger of the two source variations on that same restriction. -/
theorem glued_phi_variation_outgoing_restrict_le
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    (u : ℝ) (T : Set ℝ) :
    eVariationOn ((gluedFields U₁ S₁ S₂).phi u)
      {v | v ∈ T ∧ (u, v) ∈ U₁ ∪ U₂} ≤
      max (eVariationOn (S₁.phi u) {v | v ∈ T ∧ (u, v) ∈ U₁})
        (eVariationOn (S₂.phi u) {v | v ∈ T ∧ (u, v) ∈ U₂}) := by
  apply eVariationOn.le_max_of_finite_partition_source
  intro n w hw hws
  have htop : (u, w n) ∈ U₁ ∪ U₂ := (hws n).2
  rcases htop with ht₁ | ht₂
  · left
    intro i hi
    have hlt : u < w i := by
      rcases (hws i).2 with h | h
      · exact (h₁.solution.development.wedge h).2
      · exact (h₂.solution.development.wedge h).2
    have hmem : (u, w i) ∈ U₁ :=
      h₁.solution.development.outgoing_mem ht₁ hlt (hw hi)
    exact ⟨⟨(hws i).1, hmem⟩,
      (gluedFields_eq_first (S₂ := S₂) hmem).2.1⟩
  · right
    intro i hi
    have hlt : u < w i := by
      rcases (hws i).2 with h | h
      · exact (h₁.solution.development.wedge h).2
      · exact (h₂.solution.development.wedge h).2
    have hmem : (u, w i) ∈ U₂ :=
      h₂.solution.development.outgoing_mem ht₂ hlt (hw hi)
    exact ⟨⟨(hws i).1, hmem⟩,
      (gluedFields_eq_second h₁ h₂ hdata hmem).2.1⟩

/-- The past outgoing item-4 supremum on the union is bounded by the
maximum of the source suprema. -/
theorem glued_past_outgoing_variation_le
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    (a ε : ℝ) :
    (⨆ δ ∈ Ioc (0 : ℝ) ε,
      eVariationOn ((gluedFields U₁ S₁ S₂).phi (a - δ))
        {v | v ∈ Ioo (a - δ) a ∧ (a - δ, v) ∈ U₁ ∪ U₂}) ≤
      max
        (⨆ δ ∈ Ioc (0 : ℝ) ε,
          eVariationOn (S₁.phi (a - δ))
            {v | v ∈ Ioo (a - δ) a ∧ (a - δ, v) ∈ U₁})
        (⨆ δ ∈ Ioc (0 : ℝ) ε,
          eVariationOn (S₂.phi (a - δ))
            {v | v ∈ Ioo (a - δ) a ∧ (a - δ, v) ∈ U₂}) := by
  apply iSup_le
  intro δ
  apply iSup_le
  intro hδ
  have h := glued_phi_variation_outgoing_restrict_le h₁ h₂ hdata
    (a - δ) (Ioo (a - δ) a)
  exact h.trans (max_le_max
    (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))
    (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl)))

/-- The future outgoing item-4 supremum has the same source maximum
bound. -/
theorem glued_future_outgoing_variation_le
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    (a ε : ℝ) :
    (⨆ δ ∈ Ico (0 : ℝ) ε,
      eVariationOn ((gluedFields U₁ S₁ S₂).phi (a + δ))
        {v | v ∈ Ioo (a + δ) (a + ε) ∧
          (a + δ, v) ∈ U₁ ∪ U₂}) ≤
      max
        (⨆ δ ∈ Ico (0 : ℝ) ε,
          eVariationOn (S₁.phi (a + δ))
            {v | v ∈ Ioo (a + δ) (a + ε) ∧ (a + δ, v) ∈ U₁})
        (⨆ δ ∈ Ico (0 : ℝ) ε,
          eVariationOn (S₂.phi (a + δ))
            {v | v ∈ Ioo (a + δ) (a + ε) ∧ (a + δ, v) ∈ U₂}) := by
  apply iSup_le
  intro δ
  apply iSup_le
  intro hδ
  have h := glued_phi_variation_outgoing_restrict_le h₁ h₂ hdata
    (a + δ) (Ioo (a + δ) (a + ε))
  exact h.trans (max_le_max
    (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))
    (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl)))

end ChristodoulouBV.Uniqueness

end
