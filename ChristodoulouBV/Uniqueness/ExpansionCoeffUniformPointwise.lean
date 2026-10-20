module

public import ChristodoulouBV.Uniqueness.ExpansionCoefficientWeights

/-!
# Fixed pointwise expansion coefficient comparison bounds

The preliminary variation threshold is chosen before the coefficient
constant. All resulting bounds hold on every compact top of the same full
comparison triangle.
-/

@[expose] public section

open Set

namespace ChristodoulouBV.Uniqueness

private theorem inv_abs_le_of_lower {x C : ℝ}
    (hC : 0 < C) (hlo : 1 / C ≤ |x|) : 1 / |x| ≤ C := by
  have hx : 0 < |x| := (one_div_pos.mpr hC).trans_le hlo
  apply (div_le_iff₀ hx).2
  have hh := mul_le_mul_of_nonneg_left hlo hC.le
  have heq : C * (1 / C) = 1 := by field_simp [hC.ne']
  rw [← heq]
  nlinarith only [hh]

private theorem abs_div_le_sq_of_lower {x y C : ℝ}
    (hC : 0 < C) (hx : |x| ≤ C) (hy : 1 / C ≤ |y|) :
    |x / y| ≤ C ^ 2 := by
  have hInv := inv_abs_le_of_lower hC hy
  rw [abs_div, div_eq_mul_inv, ← one_div]
  calc
    |x| * (1 / |y|) ≤ C * C := by gcongr
    _ = C ^ 2 := by ring

private theorem distance_div_radius_le_of_lower {d r C : ℝ}
    (hd : 0 < d) (hr : 0 < r) (hC : 0 < C)
    (hlo : 1 / C ≤ r / d) : d / r ≤ C := by
  have hstep : (1 / C) * d ≤ r := (le_div_iff₀ hd).1 hlo
  apply (div_le_iff₀ hr).2
  have hh := mul_le_mul_of_nonneg_left hstep hC.le
  have heq : C * ((1 / C) * d) = d := by field_simp [hC.ne']
  rw [heq] at hh
  simpa only [mul_comm] using hh

/-- The coefficient bounds of the fixed BV pair supply one common numerical
weight for both characteristic coefficient differences. The bound is chosen
after the preliminary variation threshold and before a compact cutoff. -/
theorem ComparisonData.expansion_coefficient_pointwise_uniform
    (D : ComparisonData) (ha : D.a = 0) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∃ C₁ : ℝ, 4 ≤ C₁ ∧
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀ ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε₀) →
        ∀ V, D.a < V → V < D.b →
          ∀ u v, (u, v) ∈ triangle D.a V → v ∈ D.goodV →
            |IsBVSolution.nuCoeff D.S₁ u v -
              IsBVSolution.nuCoeff D.S₂ u v| ≤
              (C₁ ^ 2 + (C₁ ^ 2) ^ 2 + (C₁ ^ 2) ^ 4) *
                D.L V * IsBVSolution.nuCoeff D.S₂ u v +
              2 * (C₁ ^ 2) ^ 5 *
                (|D.S₁.m u v - D.S₂.m u v| / (v - u) ^ 2) ∧
            |IsBVSolution.incomingCoeff D.S₁ u v -
              IsBVSolution.incomingCoeff D.S₂ u v| ≤
              (C₁ ^ 2 + (C₁ ^ 2) ^ 2 + (C₁ ^ 2) ^ 4) *
                D.N V * (-IsBVSolution.incomingCoeff D.S₂ u v) +
              2 * (C₁ ^ 2) ^ 5 *
                (|D.S₁.m u v - D.S₂.m u v| / (v - u) ^ 2)) := by
  let w := (D.a + D.b) / 2
  have hw : w ∈ Ioo D.a D.b := by dsimp [w]; constructor <;> linarith [D.hab]
  have hpoint : (D.a, w) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨le_rfl, hw.1, hw.2⟩
  have href : (0, w) ∈ D.U₁ ∩ D.U₂ := by
    simpa only [ha] using D.hT hpoint
  have hdata : D.S₁.phi 0 w = D.S₂.phi 0 w := by
    simpa only [ha] using (D.hdata w hw).2
  obtain ⟨C₀, hC₀, ε₀, hε₀, C₁, hC₁, hfield⟩ :=
    D.h₁.coefficient_bounds D.h₂ href hdata
  refine ⟨C₀, hC₀, ε₀, hε₀, C₁, hC₁, ?_⟩
  intro hsmall V haV hVb u v huv hvG
  have hfull : (u, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨huv.1, huv.2.1, huv.2.2.trans hVb⟩
  have hb₁ := hfield D.a D.b D.hT hsmall u v hfull D.S₁ (Or.inl rfl)
  have hb₂ := hfield D.a D.b D.hT hsmall u v hfull D.S₂ (Or.inr rfl)
  rcases hb₁ with ⟨_, hlam₁hi, _, hnu₁hi, _, _, _, hr₁lo, _, _,
    hg₁inv, _, _, _, _, _, _, _, _, _⟩
  rcases hb₂ with ⟨hlam₂lo, _, hnu₂lo, _, _, _, _, _, _, _,
    hg₂inv, _, _, _, _, _, _, _, _, hcross₂⟩
  have hp := D.hT hfull
  have hr₁ := D.h₁.solution.radius_pos (u, v) hp.1
  have hd : 0 < v - u := sub_pos.mpr huv.2.1
  have hC₁pos : 0 < C₁ := by linarith
  have hC₁sq : C₁ ≤ C₁ ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ C₁ - 1)
      (by linarith : 0 ≤ C₁)]
  have hlam₁abs : |D.S₁.lam u v| ≤ C₁ := by
    rw [abs_of_pos (D.h₁.solution.lam_pos (u, v) hp.1)]
    exact hlam₁hi
  have hrratio : D.S₂.r u v / D.S₁.r u v ≤ C₁ :=
    (hcross₂ D.S₁ (Or.inl rfl)).2.2
  have hdrratio : (v - u) / D.S₁.r u v ≤ C₁ :=
    distance_div_radius_le_of_lower hd hr₁ hC₁pos hr₁lo
  have hOutBounds :
      1 / |D.S₂.lam u v| ≤ C₁ ^ 2 ∧
      |D.S₁.lam u v / D.S₂.lam u v| ≤ C₁ ^ 2 ∧
      D.S₂.r u v / D.S₁.r u v ≤ C₁ ^ 2 ∧
      (v - u) / D.S₁.r u v ≤ C₁ ^ 2 ∧
      |D.S₁.lam u v| ≤ C₁ ^ 2 ∧
      1 / (1 - IsBVSolution.mu D.S₁ u v) ≤ C₁ ^ 2 ∧
      1 / (1 - IsBVSolution.mu D.S₂ u v) ≤ C₁ ^ 2 := by
    refine ⟨(inv_abs_le_of_lower hC₁pos ?_).trans hC₁sq,
      (abs_div_le_sq_of_lower hC₁pos hlam₁abs ?_),
      hrratio.trans hC₁sq, hdrratio.trans hC₁sq,
      hlam₁abs.trans hC₁sq,
      (by simpa only [one_div] using hg₁inv.trans hC₁sq),
      (by simpa only [one_div] using hg₂inv.trans hC₁sq)⟩
    · rw [abs_of_pos (D.h₂.solution.lam_pos (u, v) hp.2)]
      exact hlam₂lo
    · rw [abs_of_pos (D.h₂.solution.lam_pos (u, v) hp.2)]
      exact hlam₂lo
  have hInBounds :
      1 / |D.S₂.nu u v| ≤ C₁ ^ 2 ∧
      |D.S₁.nu u v / D.S₂.nu u v| ≤ C₁ ^ 2 ∧
      D.S₂.r u v / D.S₁.r u v ≤ C₁ ^ 2 ∧
      (v - u) / D.S₁.r u v ≤ C₁ ^ 2 ∧
      |D.S₁.nu u v| ≤ C₁ ^ 2 ∧
      1 / (1 - IsBVSolution.mu D.S₁ u v) ≤ C₁ ^ 2 ∧
      1 / (1 - IsBVSolution.mu D.S₂ u v) ≤ C₁ ^ 2 :=
    ⟨(inv_abs_le_of_lower hC₁pos hnu₂lo).trans hC₁sq,
      abs_div_le_sq_of_lower hC₁pos hnu₁hi hnu₂lo,
      hrratio.trans hC₁sq, hdrratio.trans hC₁sq,
      hnu₁hi.trans hC₁sq,
      (by simpa only [one_div] using hg₁inv.trans hC₁sq),
      (by simpa only [one_div] using hg₂inv.trans hC₁sq)⟩
  exact ⟨D.nuCoeff_difference_weighted hVb.le huv hvG
      (sq_nonneg C₁) hOutBounds,
    D.incomingCoeff_difference_weighted hVb huv hvG
      (sq_nonneg C₁) hInBounds⟩

end ChristodoulouBV.Uniqueness

end
