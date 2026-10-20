module

public import ChristodoulouBV.Uniqueness.ExpansionCoefficientDifference

/-!
# Incoming coefficient integrals on comparison triangles

The unsigned form of (3.12) controls every initial subsegment of an incoming
ray. This form is used by the representative-stable expansion comparison.
-/

@[expose] public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- Under a fixed quotient bound and incoming variation bound, the absolute
incoming logarithmic coefficient has an `O(ε)` integral on every initial
subsegment of the full incoming characteristic. -/
theorem ComparisonData.incomingCoeff_integral_small (D : ComparisonData)
    {C ε v u : ℝ} (hC : 0 ≤ C)
    (hav : D.a < v) (hvb : v < D.b)
    (hau : D.a ≤ u) (huv : u < v)
    (hquot : ∀ s ∈ Ico D.a v,
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        |S.zeta s v / S.nu s v| ≤ C)
    (hY : ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
      (eVariationOn (fun s => S.phi s v) (Ico D.a v)).toReal ≤ ε) :
    ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
      -(∫ s in D.a..u, IsBVSolution.incomingCoeff S s v) ≤ C * ε := by
  intro S hS
  have hpoint : (D.a, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨le_rfl, hav, hvb⟩
  have haccess : ∀ s ∈ Ico D.a v, (s, v) ∈ D.U₁ ∩ D.U₂ := by
    intro s hs
    exact D.hT ((mem_triangle).2 ⟨hs.1, hs.2, hvb⟩)
  have hcore {U : Set (ℝ × ℝ)} (h : IsBVSolution U S)
      (haccessS : ∀ s ∈ Ico D.a v, (s, v) ∈ U) :
      -(∫ s in D.a..u, IsBVSolution.incomingCoeff S s v) ≤ C * ε := by
    have hM : ∀ s ∈ Ico D.a v, |S.zeta s v / S.nu s v| ≤ C :=
      fun s hs => hquot s hs S hS
    have hInt : IntervalIntegrable
        (fun s => -IsBVSolution.incomingCoeff S s v) volume D.a v :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hav.le).2
        (h.incomingCoeff_integrable_axis hav haccessS hM)).neg
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc D.a v)]
        (fun s => -IsBVSolution.incomingCoeff S s v) := by
      apply (ae_restrict_iff' measurableSet_Ioc).mpr
      have hne : ∀ᵐ s : ℝ ∂volume, s ≠ v := by
        simp [ae_iff, measure_singleton]
      filter_upwards [hne] with s hsne hs
      have hs' : s ∈ Ico D.a v :=
        ⟨hs.1.le, lt_of_le_of_ne hs.2 hsne⟩
      exact neg_nonneg.mpr (h.incomingCoeff_nonpos (haccessS s hs'))
    have hmono :
        (∫ s in D.a..u, -IsBVSolution.incomingCoeff S s v) ≤
          ∫ s in D.a..v, -IsBVSolution.incomingCoeff S s v :=
      intervalIntegral.integral_mono_interval le_rfl hau huv.le hnonneg hInt
    have hfull := h.eq3_1b hav haccessS hM
    have hvar := hY S hS
    change -(∫ s in D.a..v, IsBVSolution.incomingCoeff S s v) ≤
      C * (eVariationOn (fun s => S.phi s v) (Ico D.a v)).toReal at hfull
    calc
      -(∫ s in D.a..u, IsBVSolution.incomingCoeff S s v) =
          ∫ s in D.a..u, -IsBVSolution.incomingCoeff S s v :=
        (intervalIntegral.integral_neg).symm
      _ ≤ ∫ s in D.a..v, -IsBVSolution.incomingCoeff S s v := hmono
      _ = -(∫ s in D.a..v, IsBVSolution.incomingCoeff S s v) :=
        intervalIntegral.integral_neg
      _ ≤ C * ε := hfull.trans (mul_le_mul_of_nonneg_left hvar hC)
  rcases hS with rfl | rfl
  · exact hcore D.h₁ (fun s hs => (haccess s hs).1)
  · exact hcore D.h₂ (fun s hs => (haccess s hs).2)

end ChristodoulouBV.Uniqueness

end
