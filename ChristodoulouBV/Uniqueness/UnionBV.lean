module

public import ChristodoulouBV.Uniqueness.UnionBVAxis

/-!
# The glued solution belongs to the BV class

The three global variation constants are the maxima of the corresponding
source constants. The canonical outgoing traces and the terminal incoming
limits make these bounds valid on every slice of the union.
-/

@[expose] public section

namespace ChristodoulouBV.Uniqueness

/-- `ofReal` preserves the maximum bound needed to combine two source BV
constants into one real constant. -/
theorem max_ofReal_le_ofReal_max (x y : ℝ) :
    max (ENNReal.ofReal x) (ENNReal.ofReal y) ≤
      ENNReal.ofReal (max x y) :=
  max_le (ENNReal.ofReal_le_ofReal (le_max_left x y))
    (ENNReal.ofReal_le_ofReal (le_max_right x y))

/-- Two BV developments with matching initial data glue to a BV solution
on their union, with no additional premises or representative convention. -/
theorem glued_isBVSolution
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w) :
    IsBVSolution (U₁ ∪ U₂) (gluedFields U₁ S₁ S₂) := by
  refine {
    solution := glued_isSolution h₁ h₂ hdata
    nu_bounded_below := glued_nu_bounded_below h₁ h₂ hdata
    lam_bounded_below := glued_lam_bounded_below h₁ h₂ hdata
    item1 := ?_
    item2 := ?_
    item3_ac_out := ?_
    item3_ac_in := ?_
    item3_variation := ?_
    item4 := ?_
    item5 := ?_
    item6 := ?_ }
  · refine ⟨max h₁.item1.choose h₂.item1.choose, ?_, ?_⟩
    · intro u
      exact (glued_outgoing_variation_bounds h₁ h₂ hdata u).1 |>.trans
        (max_ofReal_le_ofReal_max _ _)
    · intro v
      exact (glued_nu_variation_incoming_le h₁ h₂ hdata v).trans
        (max_ofReal_le_ofReal_max _ _)
  · intro a _ha
    exact glued_item2_axis h₁ h₂ hdata a
  · intro u a b hab hseg
    exact glued_phi_ac_out h₁ h₂ hdata u a b hab hseg
  · intro v a b hab hseg
    exact glued_phi_ac_in h₁ h₂ hdata v a b hab hseg
  · refine ⟨max h₁.item3_variation.choose h₂.item3_variation.choose,
      ?_, ?_⟩
    · intro u
      exact (glued_outgoing_variation_bounds h₁ h₂ hdata u).2.1 |>.trans
        (max_ofReal_le_ofReal_max _ _)
    · intro v
      exact (glued_phi_variation_incoming_le h₁ h₂ hdata v).trans
        (max_ofReal_le_ofReal_max _ _)
  · intro a _ha
    exact glued_item4_axis h₁ h₂ hdata a
  · refine ⟨max h₁.item5.choose h₂.item5.choose, ?_, ?_⟩
    · intro u
      exact (glued_outgoing_variation_bounds h₁ h₂ hdata u).2.2 |>.trans
        (max_ofReal_le_ofReal_max _ _)
    · intro v
      exact (glued_zeta_variation_incoming_le h₁ h₂ hdata v).trans
        (max_ofReal_le_ofReal_max _ _)
  · intro a _ha
    exact glued_item6_axis h₁ h₂ hdata a

end ChristodoulouBV.Uniqueness

end
