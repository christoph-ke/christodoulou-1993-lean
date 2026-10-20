module

public import ChristodoulouBV.Uniqueness.UniformThresholdOutgoingDifferenceIntegral
public import ChristodoulouBV.Uniqueness.ExpansionCoeffBounds

/-!
# Outgoing expansion transport from a shared package

The exponential transport constant is chosen from the package bounds before
comparison data are selected.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The outgoing expansion difference is bounded by the good-ray axis trace
and an integral of the absolute coefficient difference. The same constant
works as the compact top approaches the open top of the triangle. -/
theorem UniformThresholdBounds.nu_difference_le_integral_coeff
    (P : UniformThresholdBounds) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        P.VariationHoldsOne D.U₁ D.S₁ →
        P.VariationHoldsOne D.U₂ D.S₂ →
      ∀ V, D.a < V → V < D.b →
        ∀ u v, (u, v) ∈ triangle D.a V → v ∈ D.goodV →
          |D.S₁.nu u v - D.S₂.nu u v| ≤
            C * (D.L V +
              ∫ t in u..v,
                |IsBVSolution.nuCoeff D.S₁ u t -
                  IsBVSolution.nuCoeff D.S₂ u t|) := by
  obtain ⟨M, hM, hcoeff⟩ := P.nuCoeff_integral_uniform_pair
  let C : ℝ := Real.exp M * (1 + P.C)
  have hExp : 1 ≤ Real.exp M := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hM
  have hKnonneg : 0 ≤ P.C := P.C_nonneg
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [mul_nonneg (sub_nonneg.mpr hExp) hKnonneg]
  refine ⟨C, hC, ?_⟩
  intro D ha hb hP hvar₁ hvar₂ V haV hVb u v huv hvG
  have hfull : (u, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨huv.1, huv.2.1, huv.2.2.trans hVb⟩
  have hp := D.hT hfull
  obtain ⟨l₁, l₂, haxis, hlim₂, hformula⟩ :=
    D.nu_difference_axis_formula haV hVb huv
  have htrace₂ : |l₂| ≤ P.C := by
    have hevent : ∀ᶠ t in 𝓝[>] u, |D.S₂.lam u t| ≤ P.C := by
      filter_upwards [Ioo_mem_nhdsGT hfull.2.1] with t ht
      have htT : (u, t) ∈ triangle D.a D.b :=
        (mem_triangle).2 ⟨huv.1, ht.1, (ht.2.trans huv.2.2).trans hVb⟩
      have htT' : (u, t) ∈ triangle 0 1 := by simpa only [ha, hb] using htT
      have hlam := (hP u t htT' D.S₂ (Or.inr rfl)).2.1
      have htU := (D.hT htT).2
      rw [abs_of_pos (D.h₂.solution.lam_pos (u, t) htU)]
      exact hlam
    exact le_of_tendsto hlim₂.abs hevent
  have hA₁ : 0 ≤ ∫ t in u..v, IsBVSolution.nuCoeff D.S₁ u t :=
    nuCoeff_integral_nonneg D.h₁ hp.1
  have hA₂ : 0 ≤ ∫ t in u..v, IsBVSolution.nuCoeff D.S₂ u t :=
    nuCoeff_integral_nonneg D.h₂ hp.2
  have hupper := hcoeff D ha hb hP hvar₁ hvar₂ v
    (huv.1.trans_lt huv.2.1) (huv.2.2.trans hVb)
    u ⟨huv.1, huv.2.1⟩
  have hExpDiff := exp_abs_sub_le_of_Icc
    ⟨hA₁, hupper.1⟩ ⟨hA₂, hupper.2⟩
  obtain ⟨Q₁, _, hQ₁⟩ := D.h₁.exists_theta_div_lam_bound_out hp.1
  obtain ⟨Q₂, _, hQ₂⟩ := D.h₂.exists_theta_div_lam_bound_out hp.2
  have hk₁ : IntervalIntegrable (IsBVSolution.nuCoeff D.S₁ u) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).2
      (D.h₁.nu_coeff_integrable_axis hp.1 hQ₁)
  have hk₂ : IntervalIntegrable (IsBVSolution.nuCoeff D.S₂ u) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).2
      (D.h₂.nu_coeff_integrable_axis hp.2 hQ₂)
  have hIntEq :
      (∫ t in u..v, IsBVSolution.nuCoeff D.S₁ u t) -
        (∫ t in u..v, IsBVSolution.nuCoeff D.S₂ u t) =
      ∫ t in u..v,
        (IsBVSolution.nuCoeff D.S₁ u t -
          IsBVSolution.nuCoeff D.S₂ u t) :=
    (intervalIntegral.integral_sub hk₁ hk₂).symm
  have hIntAbs :
      |(∫ t in u..v, IsBVSolution.nuCoeff D.S₁ u t) -
        (∫ t in u..v, IsBVSolution.nuCoeff D.S₂ u t)| ≤
      ∫ t in u..v,
        |IsBVSolution.nuCoeff D.S₁ u t -
          IsBVSolution.nuCoeff D.S₂ u t| := by
    rw [hIntEq]
    exact intervalIntegral.abs_integral_le_integral_abs huv.2.1.le
  have hLnonneg : 0 ≤ D.L V := (abs_nonneg _).trans haxis
  have hInonneg : 0 ≤ ∫ t in u..v,
      |IsBVSolution.nuCoeff D.S₁ u t -
        IsBVSolution.nuCoeff D.S₂ u t| :=
    intervalIntegral.integral_nonneg huv.2.1.le (fun _ _ => abs_nonneg _)
  rw [hformula]
  calc
    |-(l₁ - l₂) * Real.exp (∫ t in u..v, IsBVSolution.nuCoeff D.S₁ u t) -
        l₂ * (Real.exp (∫ t in u..v, IsBVSolution.nuCoeff D.S₁ u t) -
          Real.exp (∫ t in u..v, IsBVSolution.nuCoeff D.S₂ u t))| ≤
      |l₁ - l₂| * Real.exp M +
        |l₂| * (Real.exp M *
          ∫ t in u..v,
            |IsBVSolution.nuCoeff D.S₁ u t -
              IsBVSolution.nuCoeff D.S₂ u t|) := by
      have hExpBound := Real.exp_le_exp.mpr hupper.1
      calc
        _ ≤ |l₁ - l₂| *
            Real.exp (∫ t in u..v, IsBVSolution.nuCoeff D.S₁ u t) +
          |l₂| *
            |Real.exp (∫ t in u..v, IsBVSolution.nuCoeff D.S₁ u t) -
              Real.exp (∫ t in u..v, IsBVSolution.nuCoeff D.S₂ u t)| := by
          simpa only [abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)] using
            abs_sub (-(l₁ - l₂) * Real.exp
              (∫ t in u..v, IsBVSolution.nuCoeff D.S₁ u t))
              (l₂ * (Real.exp
                (∫ t in u..v, IsBVSolution.nuCoeff D.S₁ u t) -
                Real.exp
                (∫ t in u..v, IsBVSolution.nuCoeff D.S₂ u t)))
        _ ≤ _ := add_le_add
          (mul_le_mul_of_nonneg_left hExpBound (abs_nonneg _))
          (mul_le_mul_of_nonneg_left
            (hExpDiff.trans (mul_le_mul_of_nonneg_left hIntAbs
              (Real.exp_pos _).le)) (abs_nonneg _))
    _ ≤ C * (D.L V +
        ∫ t in u..v,
          |IsBVSolution.nuCoeff D.S₁ u t -
            IsBVSolution.nuCoeff D.S₂ u t|) := by
      dsimp [C]
      nlinarith [mul_nonneg hKnonneg hLnonneg,
        mul_nonneg hKnonneg hInonneg,
        mul_nonneg (Real.exp_pos M).le hLnonneg,
        mul_nonneg (Real.exp_pos M).le hInonneg]


end ChristodoulouBV.Uniqueness

end
