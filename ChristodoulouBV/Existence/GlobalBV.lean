module

public import ChristodoulouBV.Existence.GlobalBVAxis
public import ChristodoulouBV.Existence.E1Witness

/-!
# Assembly of the global small-variation BV witness

The field record is always the final `d.incomingRightFields`, using the
existing shared subsequence. All frozen clauses except item 4 are proved
here or supplied by the established construction. The internal assemblies
below take precisely the literal item 4 assertion as their remaining
input; `GlobalBVClose` discharges it with `incoming_right_fields_item4`.
-/

public section

open Set Filter
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Item 4 depends only on φ, which is identical in the final and
canonical records. The incoming axis estimates therefore supply the canonical clause to
the literal final-witness premise below by this equivalence. -/
theorem incoming_right_fields_axis_vanishing_variation_iff
    {T : ℕ → Fields} (d : RadiusLimitData T) (a : ℝ) :
    AxisVanishingVariation globalDomain d.incomingRightFields a ↔
      AxisVanishingVariation globalDomain d.scalarRightFields a := by
  constructor
  · intro h
    exact ⟨h.past_outgoing, h.past_incoming, h.future_incoming, h.future_outgoing⟩
  · intro h
    exact ⟨h.past_outgoing, h.past_incoming, h.future_incoming, h.future_outgoing⟩

/-- Assemble every field of the frozen BV definition for the final
representatives, conditional only on their literal item 4 clause. -/
theorem s6_bv_assembly_of_item4
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) (hsmall : D < ENNReal.ofReal epsilonChosen)
    (hitem4 : ∀ a ∈ adjacentAxis globalDomain,
      AxisVanishingVariation globalDomain d.incomingRightFields a) :
    IsBVSolution globalDomain d.incomingRightFields := by
  obtain ⟨hacout, hacin, hvar⟩ := incoming_right_fields_item3 h hD d
  exact
    { solution := representative_stability h hD d
      nu_bounded_below := ⟨2 / 3, fun p hp =>
        (incoming_right_fields_geometry h hD d p hp).2.2.2.1⟩
      lam_bounded_below := ⟨1 / 3, by norm_num,
        fun p hp => (incoming_right_fields_geometry h hD d p hp).1⟩
      item1 := incoming_right_fields_item1 h hD d
      item2 := s6_bv_item2 h hD d hsmall
      item3_ac_out := hacout
      item3_ac_in := hacin
      item3_variation := hvar
      item4 := hitem4
      item5 := incoming_right_fields_item5 h hD d
      item6 := s6_bv_item6 h hD d hsmall }

/-- Arbitrary point values of the small BV datum are preserved. The
sole remaining construction input is item 4 for the final witness;
neither right continuity nor a new subsequence is required. -/
theorem exists_global_bv_small_variation_of_item4
    (hitem4 : ∀ {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
      (_h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (_hD : D ≠ ∞)
      (d : RadiusLimitData T), D < ENNReal.ofReal epsilonChosen →
      ∀ a ∈ adjacentAxis globalDomain,
        AxisVanishingVariation globalDomain d.incomingRightFields a)
    (alpha₀ : ℝ → ℝ)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen) :
    ∃ S : Fields, IsBVSolution globalDomain S ∧
      ∀ v, 0 < v → S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v := by
  obtain ⟨alphaₙ, hsmooth, hpoint, hvar, _⟩ :=
    smooth_data_below_epsilon epsilonChosen alpha₀ hD
  obtain ⟨T, h⟩ := uniform_smooth_bounds_for_sequence alpha₀ alphaₙ hsmooth hpoint hvar hD
  let hfin := ne_of_lt (hD.trans_le le_top)
  let d := radiusLimitData h hfin
  exact ⟨d.incomingRightFields,
    s6_bv_assembly_of_item4 h hfin d hD (hitem4 h hfin d hD),
    incoming_right_fields_data_trace h hpoint d⟩

/-- Strengthen the existing quantitative sequence theorem with the frozen BV
record for its very same let-bound `d.incomingRightFields`. The only
additional input is the literal item 4 assertion for such witnesses. -/
theorem exists_e1_witness_sequence_bv_of_right_continuous_of_item4
    (hitem4 : ∀ {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
      (_h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (_hD : D ≠ ∞)
      (d : RadiusLimitData T), D < ENNReal.ofReal epsilonChosen →
      ∀ a ∈ adjacentAxis globalDomain,
        AxisVanishingVariation globalDomain d.incomingRightFields a)
    (alpha₀ : ℝ → ℝ)
    (hrc : ∀ v ∈ Ici (0 : ℝ), ContinuousWithinAt alpha₀ (Ici v) v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen) :
    ∃ (alphaₙ : ℕ → ℝ → ℝ) (T : ℕ → Fields)
      (h : ∀ n, SmoothSolutionBounds (alphaₙ n) (eVariationOn alpha₀ (Ioi (0 : ℝ)))
        (smoothScalarOffset T) (T n)),
      (∀ n, ContDiffOn ℝ 1 (alphaₙ n) (Ici 0)) ∧
      (∀ v, 0 < v → Tendsto (fun n => alphaₙ n v) atTop (𝓝 (alpha₀ v))) ∧
      (∀ n, eVariationOn (alphaₙ n) (Ioi (0 : ℝ)) ≤
        eVariationOn alpha₀ (Ioi (0 : ℝ))) ∧
      (∀ n, eVariationOn (alphaₙ n) (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen) ∧
      Tendsto (fun n => eVariationOn (alphaₙ n) (Ioi (0 : ℝ))) atTop
        (𝓝 (eVariationOn alpha₀ (Ioi (0 : ℝ)))) ∧
      let d := radiusLimitData h (ne_of_lt (hD.trans_le le_top))
      let S := d.incomingRightFields
      IsSolution globalDomain S ∧ IsBVSolution globalDomain S ∧
      (∀ v, 0 < v → S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v) ∧
      RightBVFields globalDomain S ∧
      (∀ p ∈ globalDomain,
        (1 / 3 : ℝ) ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ 1 / 2 ∧
        (1 / 3 : ℝ) ≤ -S.nu p.1 p.2 ∧ -S.nu p.1 p.2 ≤ 2 / 3 ∧
        (2 / 3 : ℝ) ≤ 1 - 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
        1 - 2 * S.m p.1 p.2 / S.r p.1 p.2 ≤ 1) ∧
      (∀ u, 0 ≤ u → e1OutgoingTV S u ≤
        ENNReal.ofReal (e1WitnessTVK * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal)) ∧
      ∀ v, 0 < v → e1IncomingTV S v ≤
        ENNReal.ofReal (e1WitnessTVK * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal) := by
  obtain ⟨alphaₙ, T, h, hsmooth, hpoint, hvar, hsmall, hvarlim, hS⟩ :=
    exists_e1_witness_sequence_of_right_continuous alpha₀ hrc hD
  refine ⟨alphaₙ, T, h, hsmooth, hpoint, hvar, hsmall, hvarlim, hS.1, ?_, hS.2⟩
  let hfin := ne_of_lt (hD.trans_le le_top)
  let d := radiusLimitData h hfin
  exact s6_bv_assembly_of_item4 h hfin d hD (hitem4 h hfin d hD)

/-- The exact uniform witness statement required by the quantitative existence construction,
with `IsBVSolution` inserted immediately after `IsSolution`. The
universal threshold and TV coefficient precede the datum. Its only
remaining input is item 4 for the constructed incoming representatives. -/
theorem exists_uniform_e1_witness_bv_of_item4
    (hitem4 : ∀ {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
      (_h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (_hD : D ≠ ∞)
      (d : RadiusLimitData T), D < ENNReal.ofReal epsilonChosen →
      ∀ a ∈ adjacentAxis globalDomain,
        AxisVanishingVariation globalDomain d.incomingRightFields a) :
    ∃ εq : ℝ, 0 < εq ∧ ∃ K : ℝ, 0 < K ∧
      ∀ alpha₀ : ℝ → ℝ,
        (∀ v ∈ Ici (0 : ℝ), ContinuousWithinAt alpha₀ (Ici v) v) →
        eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal εq →
        ∃ S : Fields, IsSolution globalDomain S ∧ IsBVSolution globalDomain S ∧
          (∀ v, 0 < v → S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v) ∧
          RightBVFields globalDomain S ∧
          (∀ p ∈ globalDomain,
            (1 / 3 : ℝ) ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ 1 / 2 ∧
            (1 / 3 : ℝ) ≤ -S.nu p.1 p.2 ∧ -S.nu p.1 p.2 ≤ 2 / 3 ∧
            (2 / 3 : ℝ) ≤ 1 - 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
            1 - 2 * S.m p.1 p.2 / S.r p.1 p.2 ≤ 1) ∧
          (∀ u, 0 ≤ u → e1OutgoingTV S u ≤
            ENNReal.ofReal (K * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal)) ∧
          ∀ v, 0 < v → e1IncomingTV S v ≤
            ENNReal.ofReal (K * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal) := by
  refine ⟨epsilonChosen, epsilonChosen_pos, e1WitnessTVK, e1WitnessTVK_pos, ?_⟩
  intro alpha₀ hrc hD
  obtain ⟨alphaₙ, T, h, _, _, _, _, _, hS⟩ :=
    exists_e1_witness_sequence_bv_of_right_continuous_of_item4 hitem4 alpha₀ hrc hD
  exact ⟨(radiusLimitData h (ne_of_lt (hD.trans_le le_top))).incomingRightFields, hS⟩

end ChristodoulouBV

end
