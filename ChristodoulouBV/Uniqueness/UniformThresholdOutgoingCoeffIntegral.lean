module

public import ChristodoulouBV.Uniqueness.UniformThresholdExpansionPointwise

/-!
# Outgoing transport coefficient integral from a shared package

The global scalar variation number and pointwise field bounds suffice for a
common integral bound on both normalized BV solutions.
-/

@[expose] public section

open Set
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- A single package bounds the outgoing logarithmic coefficient integral
for either member of every normalized comparison. -/
theorem UniformThresholdBounds.nuCoeff_integral_uniform_pair
    (P : UniformThresholdBounds) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        P.VariationHoldsOne D.U₁ D.S₁ →
        P.VariationHoldsOne D.U₂ D.S₂ →
        ∀ V, D.a < V → V < D.b →
          ∀ u ∈ Ico D.a V,
            (∫ t in u..V, IsBVSolution.nuCoeff D.S₁ u t) ≤ M ∧
            (∫ t in u..V, IsBVSolution.nuCoeff D.S₂ u t) ≤ M := by
  let Q := P.C / P.c
  let M := Q * P.variation
  have hQ : 0 ≤ Q := div_nonneg P.C_nonneg P.c_pos.le
  have hM : 0 ≤ M := mul_nonneg hQ P.variation_nonneg
  refine ⟨M, hM, ?_⟩
  intro D ha hb hP hvar₁ hvar₂ V haV hVb u hu
  have hpt : (u, V) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨hu.1, hu.2, hVb⟩
  have hboundOne (U : Set (ℝ × ℝ)) (S : Fields)
      (h : IsBVSolution U S) (hp : (u, V) ∈ U)
      (hS : S = D.S₁ ∨ S = D.S₂)
      (hvar : ∀ x, eVariationOn (S.phi x) {y | (x, y) ∈ U} ≤
        ENNReal.ofReal P.variation) :
      (∫ t in u..V, IsBVSolution.nuCoeff S u t) ≤ M := by
    have hquot : ∀ t ∈ Ioc u V,
        |S.theta u t / S.lam u t| ≤ Q := by
      intro t ht
      have htT : (u, t) ∈ triangle D.a D.b :=
        (mem_triangle).2 ⟨hu.1, ht.1, ht.2.trans_lt hVb⟩
      exact P.theta_div_lam_le D ha hb hP htT S hS
    have hsubset : Ioc u V ⊆ {t | (u, t) ∈ U} := by
      intro t ht
      exact h.solution.development.outgoing_mem hp ht.1 ht.2
    have hvariation : (eVariationOn (S.phi u) (Ioc u V)).toReal ≤
        P.variation :=
      ENNReal.toReal_le_of_le_ofReal P.variation_nonneg
        ((eVariationOn.mono (S.phi u) hsubset).trans (hvar u))
    exact (h.eq3_1a_nuCoeff hp hquot).trans
      (by simpa only [M] using
        mul_le_mul_of_nonneg_left hvariation hQ)
  exact ⟨hboundOne D.U₁ D.S₁ D.h₁ (D.hT hpt).1 (Or.inl rfl) hvar₁.2.2.1,
    hboundOne D.U₂ D.S₂ D.h₂ (D.hT hpt).2 (Or.inr rfl) hvar₂.2.2.1⟩

end ChristodoulouBV.Uniqueness

end
