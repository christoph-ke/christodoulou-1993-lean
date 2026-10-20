module

public import ChristodoulouBV.Uniqueness.UniformThresholdIncomingMassDifference
public import ChristodoulouBV.Uniqueness.UniformThresholdIStarHardy
public import ChristodoulouBV.Uniqueness.IncomingMassHardy

/-!
# Package-uniform incoming mass norm

The incoming mass difference and terminal Hardy bounds yield one common
coefficient before normalized comparison data are selected.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The stable incoming mass Hardy estimate on the full comparison triangle.
The incoming axis is available to both developments and both terminal mass
traces vanish. The coefficient is fixed before the variation and cutoff. -/
theorem UniformThresholdBounds.GammaStar_le_epsilon_B_N
    (P : UniformThresholdBounds) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ P.gapThreshold →
          (∀ u v, (u, v) ∈ triangle D.a D.b →
            ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
              (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε ∧
              (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε) →
          ∀ V, D.a < V → V < D.b →
            D.GammaStar V ≤ ENNReal.ofReal (C * ε * (D.B V + D.N V)) ∧
            (∀ v ∈ Ioo D.a V,
              (∀ u ∈ Ico D.a v, (u, v) ∈ D.U₁ ∧ (u, v) ∈ D.U₂) ∧
              Tendsto (fun u => D.S₁.m u v) (𝓝[<] v) (𝓝 (0 : ℝ)) ∧
              Tendsto (fun u => D.S₂.m u v) (𝓝[<] v) (𝓝 (0 : ℝ))) := by
  obtain ⟨Cm, hCm, hmass⟩ := P.mass_in_difference_le_IStar
  obtain ⟨K, hK, hHardy⟩ := P.IStar_hardy_le_local_variation
  let C := max (Cm * K) 1
  have hC : 1 ≤ C := le_max_right _ _
  refine ⟨C, hC, ?_⟩
  intro D ha hb hP ε hε hεle hsmall V haV hVb
  have hsmall₀ : ∀ u v, (u, v) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ P.gapThreshold := by
    intro u v huv S hS
    exact (hsmall u v huv S hS).1.trans hεle
  have hBN : 0 ≤ D.B V + D.N V :=
    add_nonneg (D.B_nonneg ha hVb.le) (D.N_nonneg haV hVb)
  let T := Cm * (D.B V + D.N V)
  have hT : 0 ≤ T := mul_nonneg (by linarith) hBN
  constructor
  · unfold ComparisonData.GammaStar
    apply iSup_le
    intro v
    apply iSup_le
    intro hv
    have hav : (D.a, v) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨le_rfl, hv.1, hv.2.trans hVb⟩
    have hvar₁ := (hsmall D.a v hav D.S₁ (Or.inl rfl)).2
    have hvar₂ := (hsmall D.a v hav D.S₂ (Or.inr rfl)).2
    have hHardy' := hHardy D ha hb hP D.a v ε hav hvar₁ hvar₂
    rw [← restrict_Ico_eq_restrict_Ioc] at hHardy'
    have hpoint : ∀ u ∈ Ico D.a v,
        ENNReal.ofReal
          (|D.S₁.m u v - D.S₂.m u v| / (v - u) ^ 2) ≤
          ENNReal.ofReal T *
            ENNReal.ofReal (IStar D u v / (v - u) ^ 2) := by
      intro u hu
      have huv : (u, v) ∈ triangle D.a V :=
        (mem_triangle).2 ⟨hu.1, hu.2, hv.2⟩
      have hmass' := hmass D ha hb hP hsmall₀ V u v haV hVb huv
      have hden : 0 ≤ (v - u) ^ 2 := sq_nonneg _
      have hreal : |D.S₁.m u v - D.S₂.m u v| / (v - u) ^ 2 ≤
          T * (IStar D u v / (v - u) ^ 2) := by
        calc
          _ ≤ (T * IStar D u v) / (v - u) ^ 2 :=
            div_le_div_of_nonneg_right hmass' hden
          _ = T * (IStar D u v / (v - u) ^ 2) := by ring
      rw [← ENNReal.ofReal_mul hT]
      exact ENNReal.ofReal_le_ofReal hreal
    have hCmk : Cm * K ≤ C := le_max_left _ _
    have hrealFinal : T * (K * ε) ≤ C * ε * (D.B V + D.N V) := by
      calc
        T * (K * ε) = (Cm * K * ε) * (D.B V + D.N V) := by
          dsimp [T]
          ring
        _ ≤ (C * ε) * (D.B V + D.N V) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCmk hε) hBN
        _ = C * ε * (D.B V + D.N V) := rfl
    calc
      (∫⁻ u in Ico D.a v, ENNReal.ofReal
        (|D.S₁.m u v - D.S₂.m u v| / (v - u) ^ 2)) ≤
          ∫⁻ u in Ico D.a v, ENNReal.ofReal T *
            ENNReal.ofReal (IStar D u v / (v - u) ^ 2) := by
        apply lintegral_mono_ae
        exact ae_restrict_of_forall_mem measurableSet_Ico hpoint
      _ = ENNReal.ofReal T *
          (∫⁻ u in Ico D.a v, ENNReal.ofReal
            (IStar D u v / (v - u) ^ 2)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal T * ENNReal.ofReal (K * ε) := by
        gcongr
      _ = ENNReal.ofReal (T * (K * ε)) := by
        rw [ENNReal.ofReal_mul hT]
      _ ≤ ENNReal.ofReal (C * ε * (D.B V + D.N V)) :=
        ENNReal.ofReal_le_ofReal hrealFinal
  · intro v hv
    have hav : (D.a, v) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨le_rfl, hv.1, hv.2.trans hVb⟩
    have hT₁ : triangle D.a D.b ⊆ D.U₁ :=
      fun p hp => (D.hT hp).1
    have hT₂ : triangle D.a D.b ⊆ D.U₂ :=
      fun p hp => (D.hT hp).2
    exact ⟨fun u hu => ⟨
        IsBVSolution.incoming_axis_access_of_triangle hT₁ hav u hu,
        IsBVSolution.incoming_axis_access_of_triangle hT₂ hav u hu⟩,
      IsBVSolution.incoming_mass_axis_trace_of_triangle D.h₁ hT₁ hav,
      IsBVSolution.incoming_mass_axis_trace_of_triangle D.h₂ hT₂ hav⟩


end ChristodoulouBV.Uniqueness

end
