-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ChristodoulouBV.Frozen.IsC1Solution
public import ChristodoulouBV.Frozen.OpenDevelopment
public import ChristodoulouBV.Frozen.DevelopmentWithInitialEdge
import ChristodoulouBV.Provider.Theorem5_1

/-! The C¹ extension principle. -/

public section

namespace ChristodoulouBV

/-- Theorem 5.1, Christodoulou 1993, p. 1172 (statement and (5.1)), p. 1176
(the universal choice `ε₁ = (5 - 2√6)/3`), p. 1179 (conclusion).
The family follows the printed “for every `v₀`” premise. The mass bound is an
eventual bound for the shrinking domains, including all members of the family.
`source/transcription/s5-extension-theorem.tex:4-16,215-225,343-351`. -/
theorem theorem5_1 :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ (alpha₀ : ℝ → ℝ) (vStar : ℝ), 0 < vStar →
        ContDiffOn ℝ 1 alpha₀ (Set.Ici 0) →
        ∀ S : ℝ → Fields,
          (∀ v₀ ∈ Set.Ioo (0 : ℝ) vStar,
            IsC1Solution (developmentWithInitialEdge v₀) (S v₀) ∧
            (∀ v ∈ Set.Ioo (0 : ℝ) v₀,
              (S v₀).r 0 v = v / 2 ∧ (S v₀).alpha 0 v = alpha₀ v)) →
          (∃ u₀ ∈ Set.Ioo (0 : ℝ) vStar, ∃ η : ℝ, η < ε₁ ∧
            ∀ v₀ ∈ Set.Ioo (0 : ℝ) vStar,
              ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge v₀,
                2 * (S v₀).m p.1 p.2 / (S v₀).r p.1 p.2 ≤ η) →
          ∃ v₁ : ℝ, vStar < v₁ ∧ ∃ T : Fields,
            IsC1Solution (developmentWithInitialEdge v₁) T ∧
            (∀ v ∈ Set.Ioo (0 : ℝ) v₁,
              T.r 0 v = v / 2 ∧ T.alpha 0 v = alpha₀ v) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ChristodoulouBV.Provider.theorem5_1
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN
end ChristodoulouBV

end
-- FROZEN_ANCHOR_SUFFIX_END
