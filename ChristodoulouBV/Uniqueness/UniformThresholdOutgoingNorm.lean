module

public import ChristodoulouBV.Uniqueness.UniformThresholdOutgoingTransport
public import ChristodoulouBV.Uniqueness.ExpansionNorms

/-!
# Package-uniform outgoing expansion norm

The outgoing transport and coefficient integral constants are selected
before the normalized comparison data.
-/

@[expose] public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- Outgoing transport gives `N ≤ C(L + Γ)` with a constant fixed after the
preliminary coefficient choice and independent of the compact top. -/
theorem UniformThresholdBounds.nu_goodV_transport_bound
    (P : UniformThresholdBounds) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        P.VariationHoldsOne D.U₁ D.S₁ →
        P.VariationHoldsOne D.U₂ D.S₂ →
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ P.gapThreshold) →
        ∀ V, D.a < V → V < D.b →
          D.N V ≤ C * (D.L V + (D.Gamma V).toReal)) := by
  obtain ⟨Ccoeff, hCcoeff, hcoeff⟩ :=
    P.nuCoeff_difference_integral_uniform
  obtain ⟨Ctransport, hCtransport, htransport⟩ :=
    P.nu_difference_le_integral_coeff
  let C := Ctransport * (1 + Ccoeff)
  have hC : 1 ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg (sub_nonneg.mpr hCtransport)
      (by linarith : 0 ≤ Ccoeff)]
  refine ⟨C, hC, ?_⟩
  intro D ha hb hP hvar₁ hvar₂ hsmall V haV hVb
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
  have hfull := hcoeff D ha hb hP hvar₁ hvar₂ hsmall V haV hVb u hu
  have hI := hmono.trans hfull
  have hν := htransport D ha hb hP hvar₁ hvar₂ V haV hVb u v huv hvG
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

end ChristodoulouBV.Uniqueness

end
