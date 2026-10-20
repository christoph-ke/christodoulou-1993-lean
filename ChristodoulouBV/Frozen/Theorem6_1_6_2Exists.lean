-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import ChristodoulouBV.Frozen.IsC1Solution
public import ChristodoulouBV.Frozen.IsBVSolution
public import ChristodoulouBV.Frozen.GlobalDomain
import ChristodoulouBV.Provider.Theorem6_1_6_2Exists

/-! The joint existence fragment of Theorems 6.1 and 6.2 (D9). -/

public section

namespace ChristodoulouBV

/-- The existence fragment of Theorems 6.1 and 6.2 with their shared `εStar`.
Christodoulou 1993, p. 1179 (Theorem 6.1), p. 1183 (Theorem 6.2 and its explicit
reference to the same constant); gauge `r(0,v)=v/2`, p. 1157.
The four image-area conclusions are deferred under D9.
`source/transcription/s6-existence.tex:4-13,237-249`;
`source/transcription/s4-area-estimates.tex:66-74`. -/
theorem theorem6_1_6_2_exists :
    ∃ εStar : ℝ, 0 < εStar ∧
      (∀ alpha₀ : ℝ → ℝ,
        ContDiffOn ℝ 1 alpha₀ (Set.Ici 0) →
        eVariationOn alpha₀ (Set.Ioi (0 : ℝ)) < ENNReal.ofReal εStar →
        ∃ S : Fields, IsC1Solution globalDomain S ∧
          ∀ v, 0 < v → S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v) ∧
      (∀ alpha₀ : ℝ → ℝ,
        eVariationOn alpha₀ (Set.Ioi (0 : ℝ)) < ENNReal.ofReal εStar →
        ∃ S : Fields, IsBVSolution globalDomain S ∧
          ∀ v, 0 < v → S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ChristodoulouBV.Provider.theorem6_1_6_2_exists
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN
end ChristodoulouBV

end
-- FROZEN_ANCHOR_SUFFIX_END
