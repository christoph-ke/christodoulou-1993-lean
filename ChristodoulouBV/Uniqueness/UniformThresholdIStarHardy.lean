module

public import ChristodoulouBV.Uniqueness.UniformThresholdIncomingScalarHardy
public import ChristodoulouBV.Uniqueness.IncomingIStarBound

/-!
# Package-uniform terminal Hardy bound

The terminal scalar kernel uses a radius constant fixed by the package before
normalized comparison data are selected.
-/

@[expose] public section

open Set MeasureTheory

namespace ChristodoulouBV.Uniqueness

/-- The squared-distance Hardy integral of the incoming scalar primitive is
bounded by local incoming variation, with a constant chosen globally. -/
theorem UniformThresholdBounds.IStar_hardy_le_local_variation
    (P : UniformThresholdBounds) :
    ∃ Ktotal : ℝ, 0 ≤ Ktotal ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        ∀ u v ε, (u, v) ∈ triangle D.a D.b →
          (eVariationOn (fun s => D.S₁.phi s v) (Ico u v)).toReal ≤ ε →
          (eVariationOn (fun s => D.S₂.phi s v) (Ico u v)).toReal ≤ ε →
          (∫⁻ w in Ioc u v, ENNReal.ofReal
            (IStar D w v / (v - w) ^ 2)) ≤ ENNReal.ofReal (Ktotal * ε) := by
  obtain ⟨K, hK, hbound⟩ :=
    P.zeta_abs_div_distance_integral_le_local_variation
  refine ⟨K + K, add_nonneg hK hK, ?_⟩
  intro D ha hb hP u v ε huv hvar₁ hvar₂
  have hT₁ : triangle D.a D.b ⊆ D.U₁ := fun p hp => (D.hT hp).1
  have hT₂ : triangle D.a D.b ⊆ D.U₂ := fun p hp => (D.hT hp).2
  have hf₁ := zeta_abs_integrable D.h₁ hT₁ huv
  have hf₂ := zeta_abs_integrable D.h₂ hT₂ huv
  let f : ℝ → ℝ := fun s => |D.S₁.zeta s v| + |D.S₂.zeta s v|
  have hf : IntegrableOn f (Ioc u v) volume := hf₁.add hf₂
  have hw := (hardy_in_endpoint D huv).1
  have hw' : IntegrableOn (fun s => f s / (v - s)) (Ioc u v) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).1 hw
  have hfn : ∀ s ∈ Ico u v, 0 ≤ f s :=
    fun s _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hHardy := hardy_lintegral_le_weighted_Ico huv.2.1 hf hw' hfn
  have hweight : (∫ s in u..v, f s / (v - s)) ≤ (K + K) * ε := by
    have hh := add_le_add (hbound D ha hb hP u v ε huv D.S₁ (Or.inl rfl) hvar₁)
      (hbound D ha hb hP u v ε huv D.S₂ (Or.inr rfl) hvar₂)
    have heq : (∫ s in u..v, f s / (v - s)) =
        (∫ s in u..v, |D.S₁.zeta s v| / (v - s)) +
        (∫ s in u..v, |D.S₂.zeta s v| / (v - s)) := by
      have hw₁ := zeta_abs_div_distance_integrable D.h₁ hT₁ huv
      have hw₂ := zeta_abs_div_distance_integrable D.h₂ hT₂ huv
      rw [← intervalIntegral.integral_add
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).2 hw₁)
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).2 hw₂)]
      congr 1
      funext s
      dsimp [f]
      ring
    rw [heq]
    simpa only [add_mul] using hh
  calc
    (∫⁻ w in Ioc u v, ENNReal.ofReal (IStar D w v / (v - w) ^ 2)) ≤
        ENNReal.ofReal (∫ s in u..v, f s / (v - s)) := by
      simpa only [IStar, f] using hHardy
    _ ≤ ENNReal.ofReal ((K + K) * ε) := ENNReal.ofReal_le_ofReal hweight


end ChristodoulouBV.Uniqueness

end
