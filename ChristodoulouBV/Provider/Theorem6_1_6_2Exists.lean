module

public import ChristodoulouBV.Frozen.IsC1Solution
public import ChristodoulouBV.Frozen.IsBVSolution
public import ChristodoulouBV.Frozen.GlobalDomain
public import ChristodoulouBV.Existence.GlobalC1
public import ChristodoulouBV.Existence.GlobalBVClose

/-!
# Provider for the existence fragment of Theorems 6.1 and 6.2

The shared constant is `epsilonChosen`. The C¹ branch is
`exists_global_c1_small_variation_solution` and the BV branch is
`exists_global_bv_small_variation`, including the incoming axis clause
(item 4 of the BV solution definition).
-/

public section

namespace ChristodoulouBV.Provider

/-- Theorems 6.1 and 6.2 (existence fragment), with the exact frozen statement. -/
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
  ⟨epsilonChosen, epsilonChosen_pos,
    fun alpha₀ hα hD => exists_global_c1_small_variation_solution alpha₀ hα hD,
    fun alpha₀ hD => exists_global_bv_small_variation alpha₀ hD⟩

end ChristodoulouBV.Provider

end
