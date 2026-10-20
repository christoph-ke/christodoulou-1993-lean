module

public import ChristodoulouBV.Uniqueness.UniformThresholdIncomingNorm
public import ChristodoulouBV.Uniqueness.ExpansionFirstAbsorption

/-!
# Package-uniform expansion absorption

The two transport constants determine a common expansion threshold before
any normalized comparison data are selected.
-/

@[expose] public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The representative-stable expansion estimates and their first
absorption. The final variation threshold is strictly positive and is chosen
after the common transport constant. -/
theorem UniformThresholdBounds.expansion_norms_le_mass_norms
    (P : UniformThresholdBounds) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ εfinal : ℝ, 0 < εfinal ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        P.VariationHoldsOne D.U₁ D.S₁ →
        P.VariationHoldsOne D.U₂ D.S₂ →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ εfinal →
          (∀ u v, (u, v) ∈ triangle D.a D.b →
            ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
              (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε ∧
              (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε) →
          ∀ V, D.a < V → V < D.b →
            D.N V ≤ C * (D.L V + (D.Gamma V).toReal) ∧
            D.L V ≤ C * (ε * D.N V + (D.GammaStar V).toReal) ∧
            D.L V ≤ 2 * C ^ 2 *
              ((D.Gamma V).toReal + (D.GammaStar V).toReal) ∧
            D.N V ≤ 2 * C ^ 2 *
              ((D.Gamma V).toReal + (D.GammaStar V).toReal) := by
  obtain ⟨Cout, hCout, hOut⟩ := P.nu_goodV_transport_bound
  obtain ⟨Cin, hCin, hIn⟩ := P.lambda_goodV_transport_bound
  let C := max Cout Cin
  let εfinal := min P.gapThreshold (1 / (2 * C ^ 2))
  have hC : 1 ≤ C := hCout.trans (le_max_left _ _)
  have hCpos : 0 < C := by linarith
  have hεfinal : 0 < εfinal :=
    lt_min P.gapThreshold_pos
      (one_div_pos.mpr (by positivity : 0 < 2 * C ^ 2))
  refine ⟨C, hC, εfinal, hεfinal, ?_⟩
  intro D ha hb hP hvar₁ hvar₂ ε hε hεfinalLe hsmall V haV hVb
  have hεgap : ε ≤ P.gapThreshold := hεfinalLe.trans (min_le_left _ _)
  have hsmallOut : ∀ u v, (u, v) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ P.gapThreshold := by
    intro u v huv S hS
    exact (hsmall u v huv S hS).1.trans hεgap
  have hOutV := hOut D ha hb hP hvar₁ hvar₂ hsmallOut V haV hVb
  have hInV := hIn D ha hb hP ε hε hεgap hsmall V haV hVb
  have hL : 0 ≤ D.L V := D.L_nonneg haV hVb
  have hN : 0 ≤ D.N V := D.N_nonneg haV hVb
  have hΓ : 0 ≤ (D.Gamma V).toReal := ENNReal.toReal_nonneg
  have hΓstar : 0 ≤ (D.GammaStar V).toReal := ENNReal.toReal_nonneg
  have hOutBound : D.N V ≤ C * (D.L V + (D.Gamma V).toReal) :=
    hOutV.trans (mul_le_mul_of_nonneg_right (le_max_left Cout Cin)
      (add_nonneg hL hΓ))
  have hInBound : D.L V ≤ C * (ε * D.N V + (D.GammaStar V).toReal) :=
    hInV.trans (mul_le_mul_of_nonneg_right (le_max_right Cout Cin)
      (add_nonneg (mul_nonneg hε hN) hΓstar))
  have hεsmall : C ^ 2 * ε ≤ 1 / 2 := by
    have hupper : ε ≤ 1 / (2 * C ^ 2) :=
      hεfinalLe.trans (min_le_right _ _)
    have hmul := mul_le_mul_of_nonneg_left hupper (sq_nonneg C)
    have heq : C ^ 2 * (1 / (2 * C ^ 2)) = 1 / 2 := by
      field_simp [hCpos.ne']
    rw [heq] at hmul
    exact hmul
  obtain ⟨hLbound, hNbound⟩ := expansion_bounds_of_transport
    hC hε hεsmall hN hΓ hΓstar hOutBound hInBound
  exact ⟨hOutBound, hInBound, hLbound, hNbound⟩


end ChristodoulouBV.Uniqueness

end
