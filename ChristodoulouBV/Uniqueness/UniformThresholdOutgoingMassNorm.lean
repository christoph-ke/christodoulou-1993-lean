module

public import ChristodoulouBV.Uniqueness.UniformThresholdHardyIntegral
public import ChristodoulouBV.Uniqueness.OutgoingMassHardy

/-!
# Package-uniform outgoing mass norm

The outgoing mass Hardy estimate uses constants and a preliminary threshold
fixed by the numerical package before normalized comparison data.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- Stable replacement for (3.16): the outgoing weighted mass norm is
small compared with the good-ray scalar and radius norms. The coefficient
threshold and the final constant are fixed before the variation parameter
and are uniform as the compact top approaches the open top. -/
theorem UniformThresholdBounds.Gamma_le_epsilon_A_L
    (P : UniformThresholdBounds) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ P.gapThreshold →
          (∀ u v, (u, v) ∈ triangle D.a D.b →
            ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
              (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε ∧
              (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε) →
          ∀ V, D.a < V → V < D.b →
            (D.Gamma V).toReal ≤ C * ε * (D.A V + D.L V) := by
  obtain ⟨C₀, hC₀, hray⟩ := P.outgoing_mass_weight_le_I_hardy
  obtain ⟨K, hK, hHardy⟩ := P.I_hardy_le_small_variation
  refine ⟨2 * C₀ ^ 3 * K, by positivity, ?_⟩
  intro D ha hb hP ε hε hεle hsmall V haV hVb
  have hsmallOut : ∀ u v, (u, v) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ P.gapThreshold := by
    intro u v huv S hS
    exact (hsmall u v huv S hS).1.trans hεle
  have hvar : ∀ u v, (u, v) ∈ triangle D.a D.b →
      (eVariationOn (D.S₁.phi u) (Ioc u v)).toReal ≤ ε ∧
      (eVariationOn (D.S₂.phi u) (Ioc u v)).toReal ≤ ε := by
    intro u v huv
    exact ⟨(hsmall u v huv D.S₁ (Or.inl rfl)).1,
      (hsmall u v huv D.S₂ (Or.inr rfl)).1⟩
  have hA : 0 ≤ D.A V := D.A_nonneg V
  have hL : 0 ≤ D.L V := D.L_nonneg haV hVb
  have hM : 0 ≤ 2 * C₀ ^ 3 * (D.A V + D.L V) := by positivity
  have htarget : 0 ≤ 2 * C₀ ^ 3 * K * ε * (D.A V + D.L V) := by
    positivity
  have hbound : ∀ u ∈ Ico D.a V,
      (∫ t in Ioc u V,
        |D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2) ≤
        2 * C₀ ^ 3 * K * ε * (D.A V + D.L V) := by
    intro u hu
    have huv : (u, V) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨hu.1, hu.2, hVb⟩
    calc
      (∫ t in Ioc u V,
          |D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2) ≤
          2 * C₀ ^ 3 * (D.A V + D.L V) *
            (∫ t in u..V, D.I u t / (t - u) ^ 2) :=
        hray D ha hb hP hsmallOut V haV hVb u hu
      _ ≤ 2 * C₀ ^ 3 * (D.A V + D.L V) * (K * ε) :=
        mul_le_mul_of_nonneg_left (hHardy D ha hb hP ε hε hvar u V huv) hM
      _ = 2 * C₀ ^ 3 * K * ε * (D.A V + D.L V) := by ring
  have hGamma : D.Gamma V ≤
      ENNReal.ofReal (2 * C₀ ^ 3 * K * ε * (D.A V + D.L V)) := by
    unfold ComparisonData.Gamma
    apply iSup_le
    intro u
    apply iSup_le
    intro hu
    have hint := D.outgoing_mass_diff_weight_integrable hVb hu
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc u V)]
        (fun t => |D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2) := by
      apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro t _
      exact div_nonneg (abs_nonneg _) (sq_nonneg _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
    exact ENNReal.ofReal_le_ofReal (hbound u hu)
  have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hGamma
  simpa only [ENNReal.toReal_ofReal htarget] using htoReal


end ChristodoulouBV.Uniqueness

end
