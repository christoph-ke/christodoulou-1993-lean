module

public import ChristodoulouBV.Uniqueness.UniformThresholdCoefficient
public import ChristodoulouBV.Uniqueness.QuotientBetaNorm

/-!
# Package-uniform outgoing quotient segment
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- Package-uniform version of the original quotient estimate. -/
theorem UniformThresholdBounds.nuCoeff_outgoing_segment_small
    (P : UniformThresholdBounds) :
    ∃ Q : ℝ, 1 ≤ Q ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ P.gapThreshold →
        (∀ p q, (p, q) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi p) (Ioc p q)).toReal ≤ ε ∧
            (eVariationOn (fun s => S.phi s q) (Ico p q)).toReal ≤ ε) →
        ∀ u x v, (u, v) ∈ triangle D.a D.b →
          u < x → x ≤ v →
          (∫ t in x..v, IsBVSolution.nuCoeff D.S₁ u t) ≤ Q * ε := by
  obtain ⟨Q, hQ, hcoef⟩ := P.coefficient_bounds_normalized
  refine ⟨Q, by linarith, ?_⟩
  intro D ha hb hP ε hε hε₀le hsmall u x v huv hux hxv
  have hpre : ∀ p q, (p, q) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        (eVariationOn (S.phi p) (Ioc p q)).toReal ≤ P.gapThreshold := by
    intro p q hpq S hS
    exact (hsmall p q hpq S hS).1.trans hε₀le
  have hM : ∀ t ∈ Ioc u v,
      |D.S₁.theta u t / D.S₁.lam u t| ≤ Q := by
    intro t ht
    have hut : (u, t) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩
    rcases hcoef D ha hb hP hpre u t hut D.S₁ (Or.inl rfl) with
      ⟨_, _, _, _, _, _, _, _, _, _, _, hθ,
        _, _, _, _, _, _, _, _⟩
    exact hθ
  have hfull := D.h₁.eq3_1a_nuCoeff (D.hT huv).1 hM
  have hvar := (hsmall u v huv D.S₁ (Or.inl rfl)).1
  have hK := D.h₁.nu_coeff_integrable_axis (D.hT huv).1 hM
  have hInt : IntervalIntegrable (IsBVSolution.nuCoeff D.S₁ u)
      volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).2 hK
  have hpos : 0 ≤ᵐ[volume.restrict (Ioc u v)]
      IsBVSolution.nuCoeff D.S₁ u := by
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro t ht
    have hut : (u, t) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩
    exact IsBVSolution.nu_coeff_nonneg
      D.h₁.solution.development D.h₁ (D.hT hut).1
  have hmono := intervalIntegral.integral_mono_interval
    hux.le hxv le_rfl hpos hInt
  exact hmono.trans (hfull.trans (mul_le_mul_of_nonneg_left hvar
    (by linarith : 0 ≤ Q)))

end ChristodoulouBV.Uniqueness

end
