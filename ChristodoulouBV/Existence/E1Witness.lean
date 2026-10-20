module

public import ChristodoulouBV.Existence.E1WitnessBounds
public import ChristodoulouBV.Existence.Representatives
public import ChristodoulouBV.Existence.SmoothData

/-!
# The quantitative right-continuous BV witness

For `S = d.incomingRightFields`, start with one-sided smooth approximation
of right-continuous data, apply the uniform smooth bounds, and use the shared
seven-field selection without extracting another subsequence. Lower
semicontinuity of variation and stability under representative changes
supply the two quantitative bounds. The same representatives retain all six
inclusive geometry inequalities at every domain point, including the
initial edge and jump lines.

The sequence theorem exposes the construction used in the global BV
assembly. The final theorem quantifies the positive threshold and TV
coefficient before the datum. These results assemble estimates and right
continuity; the remaining frozen BV clauses are proved in the global BV
assembly.
-/

public section

open Set Filter
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- The right-continuous approximants and their smooth solutions give
one shared limit whose final representatives satisfy the exact data,
right continuity, all six geometry bounds, and both three-term TV bounds.
The global BV assembly uses this `d` and its existing `subsequence`. -/
theorem exists_e1_witness_sequence_of_right_continuous
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
      IsSolution globalDomain S ∧
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
  obtain ⟨alphaₙ, hsmooth, hpoint, hvar, hsmall, hvarlim⟩ :=
    smooth_data_below_epsilon_of_right_continuous epsilonChosen alpha₀ hrc hD
  obtain ⟨T, h⟩ := uniform_smooth_bounds_for_sequence alpha₀ alphaₙ hsmooth hpoint hvar hD
  refine ⟨alphaₙ, T, h, hsmooth, hpoint, hvar, hsmall, hvarlim, ?_⟩
  let hfin := ne_of_lt (hD.trans_le le_top)
  let d := radiusLimitData h hfin
  obtain ⟨hout, hin⟩ := e1_witness_three_term_tv h hfin d
  exact ⟨representative_stability h hfin d, incoming_right_fields_data_trace h hpoint d,
    incoming_right_fields_rightBV_of_right_continuous h hfin hpoint
      (fun v hv => hrc v hv.le) d,
    incoming_right_fields_geometry h hfin d, hout, hin⟩

/-- Universal positive constants precede the right-continuous datum.
The constructed `incomingRightFields` witness satisfies both
three-term bounds and all six geometry inequalities, including `u = 0` and
jump lines. No scalar-amplitude premise or datum-dependent coefficient
is used. The full `IsBVSolution` assertion is proved in the global BV assembly. -/
theorem exists_uniform_e1_witness_estimates :
    ∃ εq : ℝ, 0 < εq ∧ ∃ K : ℝ, 0 < K ∧
      ∀ alpha₀ : ℝ → ℝ,
        (∀ v ∈ Ici (0 : ℝ), ContinuousWithinAt alpha₀ (Ici v) v) →
        eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal εq →
        ∃ S : Fields, IsSolution globalDomain S ∧
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
    exists_e1_witness_sequence_of_right_continuous alpha₀ hrc hD
  exact ⟨(radiusLimitData h (ne_of_lt (hD.trans_le le_top))).incomingRightFields, hS⟩

end ChristodoulouBV

end
