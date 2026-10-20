-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ChristodoulouBV.Frozen.IsBVSolution
import ChristodoulouBV.Provider.Theorem3_1Unique

/-! Uniqueness half of Theorem 3.1. -/

public section

namespace ChristodoulouBV

/-- The representative-independent `r, φ, m` conclusion recommended in the proposal.
Christodoulou 1993, p. 1148; `source/transcription/s3-uniqueness.tex:121-127`. -/
theorem theorem3_1_unique
    (U₁ U₂ : Set (ℝ × ℝ)) (S₁ S₂ : Fields)
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ v, (0, v) ∈ U₁ ∩ U₂ →
      S₁.r 0 v = S₂.r 0 v ∧ S₁.phi 0 v = S₂.phi 0 v) :
    ∀ p ∈ U₁ ∩ U₂,
      S₁.r p.1 p.2 = S₂.r p.1 p.2 ∧
      S₁.phi p.1 p.2 = S₂.phi p.1 p.2 ∧
      S₁.m p.1 p.2 = S₂.m p.1 p.2 :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ChristodoulouBV.Provider.theorem3_1_unique
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN
end ChristodoulouBV

end
-- FROZEN_ANCHOR_SUFFIX_END
