module

public import ChristodoulouBV.Uniqueness.UniformThresholdIncomingCoeffIntegral
public import ChristodoulouBV.Uniqueness.QuotientAlphaNorm

/-!
# Package-uniform incoming quotient segment
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The incoming transport integral has a package-dependent coefficient. -/
theorem UniformThresholdBounds.incomingCoeff_initial_segment_small
    (P : UniformThresholdBounds) :
    ∃ J : ℝ, 0 ≤ J ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
      ∀ ε : ℝ, 0 ≤ ε → ∀ u v,
        (u, v) ∈ triangle D.a D.b →
        (eVariationOn (fun s => D.S₁.phi s v) (Ico D.a v)).toReal ≤ ε →
        (∫ s in D.a..u, -IsBVSolution.incomingCoeff D.S₁ s v) ≤
          J * ε := by
  obtain ⟨J, hJ, hcoef⟩ := P.incomingCoeff_integral_small
  refine ⟨J, hJ, ?_⟩
  intro D ha hb hP ε hε u v huv hvar
  have hvab : v ∈ Ioo D.a D.b :=
    ⟨huv.1.trans_lt huv.2.1, huv.2.2⟩
  have hpoint : (D.a, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨le_rfl, hvab.1, hvab.2⟩
  have hfull := hcoef D ha hb hP ε hε D.a v hpoint
    D.S₁ (Or.inl rfl) hvar
  change -(∫ s in D.a..v,
    IsBVSolution.incomingCoeff D.S₁ s v) ≤ J * ε at hfull
  have hK := (D.incomingCoeff_integrable_pair ha v hvab).1
  have hInt : IntervalIntegrable
      (fun s => -IsBVSolution.incomingCoeff D.S₁ s v)
      volume D.a v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hvab.1.le).2 hK.neg
  have hpos : 0 ≤ᵐ[volume.restrict (Ioc D.a v)]
      (fun s => -IsBVSolution.incomingCoeff D.S₁ s v) := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    have hne : ∀ᵐ s : ℝ ∂volume, s ≠ v := by simp [ae_iff]
    filter_upwards [hne] with s hsne hs
    have hst : (s, v) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨hs.1.le, lt_of_le_of_ne hs.2 hsne, hvab.2⟩
    exact neg_nonneg.mpr (D.h₁.incomingCoeff_nonpos (D.hT hst).1)
  have hmono := intervalIntegral.integral_mono_interval
    le_rfl huv.1 huv.2.1.le hpos hInt
  calc
    (∫ s in D.a..u, -IsBVSolution.incomingCoeff D.S₁ s v) ≤
      ∫ s in D.a..v, -IsBVSolution.incomingCoeff D.S₁ s v := hmono
    _ = -(∫ s in D.a..v, IsBVSolution.incomingCoeff D.S₁ s v) :=
      intervalIntegral.integral_neg
    _ ≤ J * ε := hfull


end ChristodoulouBV.Uniqueness

end
