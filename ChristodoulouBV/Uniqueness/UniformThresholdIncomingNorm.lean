module

public import ChristodoulouBV.Uniqueness.UniformThresholdIncomingDifferenceIntegral
public import ChristodoulouBV.Uniqueness.ExpansionNorms

/-!
# Package-uniform incoming expansion norm

The incoming transport constant is selected before normalized comparison data.
-/

@[expose] public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- Incoming transport gives `L ≤ C(ε N + Γ*)` on the fixed good rays. -/
theorem UniformThresholdBounds.lambda_goodV_transport_bound
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
            D.L V ≤ C * (ε * D.N V + (D.GammaStar V).toReal) := by
  obtain ⟨Ccoeff, hCcoeff, hcoeff⟩ :=
    P.incomingCoeff_difference_integral_uniform
  let K := P.C
  have hK : 0 ≤ K := P.C_nonneg
  let C := 1 + K * Ccoeff
  have hC : 1 ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hK (by linarith : 0 ≤ Ccoeff)]
  refine ⟨C, hC, ?_⟩
  intro D ha hb hP ε hε hεle hsmall V haV hVb
  have hN : 0 ≤ D.N V := D.N_nonneg haV hVb
  have hΓ : 0 ≤ (D.GammaStar V).toReal := ENNReal.toReal_nonneg
  have hM : 0 ≤ C * (ε * D.N V + (D.GammaStar V).toReal) :=
    mul_nonneg (by linarith) (add_nonneg (mul_nonneg hε hN) hΓ)
  change D.goodVNorm V
    (fun u v => D.S₁.lam u v - D.S₂.lam u v) ≤
      C * (ε * D.N V + (D.GammaStar V).toReal)
  apply D.goodVNorm_le hM
  intro u v huv hvG
  have hfull : (u, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨huv.1, huv.2.1, huv.2.2.trans hVb⟩
  have hInit : (D.a, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨le_rfl, huv.1.trans_lt huv.2.1,
      huv.2.2.trans hVb⟩
  have hp := D.hT hInit
  have hLamPos := D.h₁.solution.lam_pos (D.a, v) hp.1
  have hLamBound : |D.S₁.lam D.a v| ≤ K := by
    rw [abs_of_pos hLamPos]
    have hInit' : (D.a, v) ∈ triangle 0 1 := by
      simpa only [ha, hb] using hInit
    exact (hP D.a v hInit' D.S₁ (Or.inl rfl)).2.1
  have hIntPair := D.incomingCoeff_integrable_pair ha v
    ⟨huv.1.trans_lt huv.2.1, huv.2.2.trans hVb⟩
  have hInt : IntegrableOn (fun s =>
      |IsBVSolution.incomingCoeff D.S₁ s v -
        IsBVSolution.incomingCoeff D.S₂ s v|) (Ioc D.a v) volume :=
    (hIntPair.1.sub hIntPair.2).abs
  have hmono :
      (∫ s in D.a..u,
        |IsBVSolution.incomingCoeff D.S₁ s v -
          IsBVSolution.incomingCoeff D.S₂ s v|) ≤
      ∫ s in D.a..v,
        |IsBVSolution.incomingCoeff D.S₁ s v -
          IsBVSolution.incomingCoeff D.S₂ s v| := by
    exact intervalIntegral.integral_mono_interval le_rfl huv.1 huv.2.1.le
      (Filter.Eventually.of_forall (fun s => abs_nonneg _))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le
        (huv.1.trans_lt huv.2.1).le).2 hInt)
  have hfullCoeff := hcoeff D ha hb hP ε hε hεle hsmall V haV hVb v
    ⟨huv.1.trans_lt huv.2.1, huv.2.2⟩ hvG
  have hI := hmono.trans hfullCoeff
  have hIpos : 0 ≤ (∫ s in D.a..u,
      |IsBVSolution.incomingCoeff D.S₁ s v -
        IsBVSolution.incomingCoeff D.S₂ s v|) :=
    intervalIntegral.integral_nonneg huv.1 (fun s _ => abs_nonneg _)
  have hlam := D.lam_difference_le_integral_coeff hfull hvG
  calc
    |D.S₁.lam u v - D.S₂.lam u v| ≤
      |D.S₁.lam D.a v| *
        (∫ s in D.a..u,
          |IsBVSolution.incomingCoeff D.S₁ s v -
            IsBVSolution.incomingCoeff D.S₂ s v|) := hlam
    _ ≤ K * (∫ s in D.a..u,
        |IsBVSolution.incomingCoeff D.S₁ s v -
          IsBVSolution.incomingCoeff D.S₂ s v|) :=
      mul_le_mul_of_nonneg_right hLamBound hIpos
    _ ≤ K * (Ccoeff * (ε * D.N V + (D.GammaStar V).toReal)) :=
      mul_le_mul_of_nonneg_left hI hK
    _ ≤ C * (ε * D.N V + (D.GammaStar V).toReal) := by
      dsimp [C]
      have hbase : 0 ≤ ε * D.N V + (D.GammaStar V).toReal :=
        add_nonneg (mul_nonneg hε hN) hΓ
      nlinarith [hbase]


end ChristodoulouBV.Uniqueness

end
