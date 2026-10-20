module

public import ChristodoulouBV.Uniqueness.ExpansionCoeffIncomingIntegral
public import ChristodoulouBV.Uniqueness.ExpansionAbsorption

/-!
# Representative-stable expansion norm estimates

The outgoing axis trace and the good initial incoming rays close the two
transport estimates. A final variation threshold absorbs the feedback of
the incoming estimate into the outgoing one.
-/

@[expose] public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- Outgoing transport gives `N ≤ C(L + Γ)` with a constant fixed after the
preliminary coefficient choice and independent of the compact top. -/
theorem ComparisonData.nu_goodV_transport_bound
    (D : ComparisonData) (ha : D.a = 0) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∃ C₁ : ℝ, 4 ≤ C₁ ∧ ∃ C : ℝ, 1 ≤ C ∧
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀ ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε₀) →
        ∀ V, D.a < V → V < D.b →
          D.N V ≤ C * (D.L V + (D.Gamma V).toReal)) := by
  obtain ⟨C₀, hC₀, ε₀, hε₀, C₁, hC₁, Ccoeff, hCcoeff, hcoeff⟩ :=
    D.nuCoeff_difference_integral_uniform ha
  obtain ⟨Ctransport, hCtransport, htransport⟩ :=
    D.nu_difference_le_integral_coeff
  let C := Ctransport * (1 + Ccoeff)
  have hC : 1 ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg (sub_nonneg.mpr hCtransport)
      (by linarith : 0 ≤ Ccoeff)]
  refine ⟨C₀, hC₀, ε₀, hε₀, C₁, hC₁, C, hC, ?_⟩
  intro hsmall V haV hVb
  have hL : 0 ≤ D.L V := D.L_nonneg haV hVb
  have hΓ : 0 ≤ (D.Gamma V).toReal := ENNReal.toReal_nonneg
  have hM : 0 ≤ C * (D.L V + (D.Gamma V).toReal) :=
    mul_nonneg (by linarith) (add_nonneg hL hΓ)
  change D.goodVNorm V
    (fun u v => D.S₁.nu u v - D.S₂.nu u v) ≤
      C * (D.L V + (D.Gamma V).toReal)
  apply D.goodVNorm_le hM
  intro u v huv hvG
  have hu : u ∈ Ico D.a V := ⟨huv.1, huv.2.1.trans huv.2.2⟩
  have hInt := D.nuCoeff_difference_integrable hVb hu
  have hmono :
      (∫ t in u..v,
        |IsBVSolution.nuCoeff D.S₁ u t -
          IsBVSolution.nuCoeff D.S₂ u t|) ≤
      ∫ t in u..V,
        |IsBVSolution.nuCoeff D.S₁ u t -
          IsBVSolution.nuCoeff D.S₂ u t| := by
    exact intervalIntegral.integral_mono_interval le_rfl huv.2.1.le
      huv.2.2.le
      (Filter.Eventually.of_forall (fun t => abs_nonneg _))
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hu.2.le).2 hInt)
  have hfull := hcoeff hsmall V haV hVb u hu
  have hI := hmono.trans hfull
  have hν := htransport V haV hVb u v huv hvG
  calc
    |D.S₁.nu u v - D.S₂.nu u v| ≤
      Ctransport * (D.L V +
        ∫ t in u..v,
          |IsBVSolution.nuCoeff D.S₁ u t -
            IsBVSolution.nuCoeff D.S₂ u t|) := hν
    _ ≤ Ctransport * (D.L V +
        Ccoeff * (D.L V + (D.Gamma V).toReal)) := by
      have hCtransportNonneg : 0 ≤ Ctransport := by linarith
      exact mul_le_mul_of_nonneg_left (by linarith only [hI]) hCtransportNonneg
    _ ≤ C * (D.L V + (D.Gamma V).toReal) := by
      dsimp [C]
      nlinarith [mul_nonneg (mul_nonneg
        (by linarith : 0 ≤ Ctransport) hΓ)
        (by linarith : 0 ≤ Ccoeff)]

/-- Incoming transport gives `L ≤ C(ε N + Γ*)` on the fixed good rays. -/
theorem ComparisonData.lambda_goodV_transport_bound
    (D : ComparisonData) (ha : D.a = 0) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∃ C₁ : ℝ, 4 ≤ C₁ ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
          (∀ u v, (u, v) ∈ triangle D.a D.b →
            ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
              (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε ∧
              (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε) →
          ∀ V, D.a < V → V < D.b →
            D.L V ≤ C * (ε * D.N V + (D.GammaStar V).toReal) := by
  obtain ⟨C₀, hC₀, ε₀, hε₀, C₁, hC₁, Ccoeff, hCcoeff, hcoeff⟩ :=
    D.incomingCoeff_difference_integral_uniform ha
  obtain ⟨K₀, hK₀, _⟩ := D.h₁.exists_uniform_radius_upper
  let K := max K₀ 0
  have hK : 0 ≤ K := le_max_right _ _
  let C := 1 + K * Ccoeff
  have hC : 1 ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hK (by linarith : 0 ≤ Ccoeff)]
  refine ⟨C₀, hC₀, ε₀, hε₀, C₁, hC₁, C, hC, ?_⟩
  intro ε hε hε₀le hsmall V haV hVb
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
    exact (hK₀ (D.a, v) hp.1).trans (le_max_left _ _)
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
  have hfullCoeff := hcoeff ε hε hε₀le hsmall V haV hVb v
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
