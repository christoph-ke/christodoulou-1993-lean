module

public import ChristodoulouBV.Existence.GlobalBV
public import ChristodoulouBV.Existence.AxisIncomingItem4

/-!
# Unconditional global small-variation BV existence

`incoming_right_fields_item4` supplies item 4 for the final witness,
which closes the two global BV assemblies.
-/

public section

open Set Filter
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Global BV existence for small-variation data with arbitrary point values
(the BV branch of Theorems 6.1/6.2). -/
theorem exists_global_bv_small_variation
    (alpha₀ : ℝ → ℝ)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen) :
    ∃ S : Fields, IsBVSolution globalDomain S ∧
      ∀ v, 0 < v → S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v :=
  exists_global_bv_small_variation_of_item4
    (fun h hD d hs => incoming_right_fields_item4 h hD d hs) alpha₀ hD

/-- The uniform quantitative witness estimates together with `IsBVSolution` for the same
witness: the quantitative existence conclusion with the full BV solution predicate. -/
theorem exists_uniform_e1_witness_bv :
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
            ENNReal.ofReal (K * (eVariationOn alpha₀ (Ioi (0 : ℝ))).toReal) :=
  exists_uniform_e1_witness_bv_of_item4
    (fun h hD d hs => incoming_right_fields_item4 h hD d hs)

end ChristodoulouBV

end
