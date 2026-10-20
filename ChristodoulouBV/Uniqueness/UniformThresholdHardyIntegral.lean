module

public import ChristodoulouBV.Uniqueness.UniformThresholdScalarHardy

/-!
# Package-uniform outgoing Hardy integral

The scalar Hardy constant is selected from the radius bound before the
normalized comparison data are selected.
-/

@[expose] public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- A fixed radius constant bounds the Hardy integral of `I` by the
outgoing scalar variation. It is chosen before the smallness parameter and
works on every ray and every compact comparison top. -/
theorem UniformThresholdBounds.I_hardy_le_small_variation
    (P : UniformThresholdBounds) :
    ∃ Ktotal : ℝ, 0 ≤ Ktotal ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        ∀ ε : ℝ, 0 ≤ ε →
          (∀ u v, (u, v) ∈ triangle D.a D.b →
            (eVariationOn (D.S₁.phi u) (Ioc u v)).toReal ≤ ε ∧
            (eVariationOn (D.S₂.phi u) (Ioc u v)).toReal ≤ ε) →
          ∀ u v, (huv : (u, v) ∈ triangle D.a D.b) →
            (∫ t in u..v, D.I u t / (t - u) ^ 2) ≤ Ktotal * ε := by
  obtain ⟨K, hK, hbound⟩ := P.theta_div_distance_integral_le_variation
  refine ⟨K + K, add_nonneg hK hK, ?_⟩
  intro D ha hb hP ε hε hsmall u v huv
  have hp := D.hT huv
  have hlt := huv.2.1
  have hi₁ : IntervalIntegrable
      (fun t => |D.S₁.theta u t| / (t - u)) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le).2
      (theta_div_distance_integrable D.h₁ hp.1)
  have hi₂ : IntervalIntegrable
      (fun t => |D.S₂.theta u t| / (t - u)) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le).2
      (theta_div_distance_integrable D.h₂ hp.2)
  have hsum : (∫ t in u..v,
      (|D.S₁.theta u t| + |D.S₂.theta u t|) / (t - u)) =
      (∫ t in u..v, |D.S₁.theta u t| / (t - u)) +
        (∫ t in u..v, |D.S₂.theta u t| / (t - u)) := by
    rw [← intervalIntegral.integral_add hi₁ hi₂]
    congr 1
    funext t
    simp only [add_div]
  have hsmallPair := hsmall u v huv
  calc
    (∫ t in u..v, D.I u t / (t - u) ^ 2) ≤
        ∫ t in u..v,
          (|D.S₁.theta u t| + |D.S₂.theta u t|) / (t - u) :=
      (D.I_hardy_le huv).2
    _ = (∫ t in u..v, |D.S₁.theta u t| / (t - u)) +
          (∫ t in u..v, |D.S₂.theta u t| / (t - u)) := hsum
    _ ≤ K * (eVariationOn (D.S₁.phi u) (Ioc u v)).toReal +
          K * (eVariationOn (D.S₂.phi u) (Ioc u v)).toReal :=
      add_le_add (hbound D ha hb hP u v huv D.S₁ (Or.inl rfl))
        (hbound D ha hb hP u v huv D.S₂ (Or.inr rfl))
    _ ≤ (K + K) * ε := by
      nlinarith only [hsmallPair.1, hsmallPair.2, hK]


end ChristodoulouBV.Uniqueness

end
