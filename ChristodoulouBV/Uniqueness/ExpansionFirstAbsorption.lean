module

public import ChristodoulouBV.Uniqueness.ExpansionNorms

/-!
# First absorption in the stable expansion comparison

The fixed pair first supplies baseline and preliminary coefficient constants.
The final variation threshold is then chosen from the two transport constants.
All estimates are uniform as the compact top rises in the open triangle.
-/

@[expose] public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The representative-stable expansion estimates and their first
absorption. The final variation threshold is strictly positive and is chosen
after the common transport constant. -/
theorem ComparisonData.expansion_norms_le_mass_norms
    (D : ComparisonData) (ha : D.a = 0) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∃ C₁ : ℝ, 4 ≤ C₁ ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∃ εfinal : ℝ, 0 < εfinal ∧
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
  obtain ⟨C₀out, hC₀out, ε₀out, hε₀out, C₁out, hC₁out,
    Cout, hCout, hOut⟩ := D.nu_goodV_transport_bound ha
  obtain ⟨C₀in, hC₀in, ε₀in, hε₀in, C₁in, hC₁in,
    Cin, hCin, hIn⟩ := D.lambda_goodV_transport_bound ha
  let C₀ := max C₀out C₀in
  let ε₀ := min ε₀out ε₀in
  let C₁ := max C₁out C₁in
  let C := max Cout Cin
  let εfinal := min ε₀ (1 / (2 * C ^ 2))
  have hC₀ : 1 ≤ C₀ := hC₀out.trans (le_max_left _ _)
  have hε₀ : 0 < ε₀ := lt_min hε₀out hε₀in
  have hC₁ : 4 ≤ C₁ := hC₁out.trans (le_max_left _ _)
  have hC : 1 ≤ C := hCout.trans (le_max_left _ _)
  have hCpos : 0 < C := by linarith
  have hεfinal : 0 < εfinal :=
    lt_min hε₀ (one_div_pos.mpr (by positivity : 0 < 2 * C ^ 2))
  refine ⟨C₀, hC₀, ε₀, hε₀, C₁, hC₁, C, hC,
    εfinal, hεfinal, ?_⟩
  intro ε hε hεfinalLe hsmall V haV hVb
  have hε₀Le : ε ≤ ε₀ := hεfinalLe.trans (min_le_left _ _)
  have hεout : ε ≤ ε₀out := hε₀Le.trans (min_le_left _ _)
  have hεin : ε ≤ ε₀in := hε₀Le.trans (min_le_right _ _)
  have hsmallOut : ∀ u v, (u, v) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀out ∧
        (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε₀out := by
    intro u v huv S hS
    have hh := hsmall u v huv S hS
    exact ⟨hh.1.trans hεout, hh.2.trans hεout⟩
  have hOutV := hOut hsmallOut V haV hVb
  have hInV := hIn ε hε hεin hsmall V haV hVb
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
