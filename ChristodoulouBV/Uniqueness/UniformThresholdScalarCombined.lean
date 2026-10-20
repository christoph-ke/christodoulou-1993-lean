module

public import ChristodoulouBV.Uniqueness.UniformThresholdScalarOutgoing
public import ChristodoulouBV.Uniqueness.UniformThresholdScalarIncoming
public import ChristodoulouBV.Uniqueness.ScalarCombined

/-!
# Package-uniform joint scalar comparison
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The constant is selected from the numerical package before normalized comparison data. -/
theorem UniformThresholdBounds.radius_scalar_goodV_bounds
    (P : UniformThresholdBounds) :
    ∃ C : ℝ, 4 ≤ C ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ P.gapThreshold ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ P.gapThreshold) →
          ∀ V u v, V < D.b → (u, v) ∈ triangle D.a V →
            |D.S₁.r u v - D.S₂.r u v| / (v - u) ≤ D.L V ∧
            |D.S₁.r u v - D.S₂.r u v| / (v - u) ≤ D.N V ∧
            |D.S₁.phi u v - D.S₂.phi u v| ≤
              C * (D.A V + D.L V) ∧
            |D.S₁.phi u v - D.S₂.phi u v| ≤
              C * (D.B V + D.N V)) := by
  obtain ⟨Co, hCo, hout⟩ := P.phi_diff_outgoing_le
  obtain ⟨Ci, hCi, hin⟩ := P.phi_diff_incoming_le
  let C := max (2 * Co ^ 2) (2 * Ci ^ 2)
  have hCoPos : 0 < 2 * Co ^ 2 := by positivity
  have hCiPos : 0 < 2 * Ci ^ 2 := by positivity
  have hC : 4 ≤ C := by
    dsimp [C]
    have hh : 4 ≤ 2 * Co ^ 2 := by nlinarith [sq_nonneg (Co - 4)]
    exact hh.trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro D ha hb hP hsmall V u v hVb huv
  have hsmallO : ∀ x y, (x, y) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        (eVariationOn (S.phi x) (Ioc x y)).toReal ≤ P.gapThreshold := by
    intro x y hxy S hS
    exact (hsmall x y hxy S hS).1
  have hφo := hout D ha hb hP hsmallO V u v hVb huv
  have hφi := hin D ha hb hP hsmallO V u v hVb huv
  have hAo : 0 ≤ D.A V + D.L V := by
    by_contra hh
    have hneg : D.A V + D.L V < 0 := lt_of_not_ge hh
    have := mul_neg_of_pos_of_neg hCoPos hneg
    linarith [abs_nonneg (D.S₁.phi u v - D.S₂.phi u v)]
  have hBi : 0 ≤ D.B V + D.N V := by
    by_contra hh
    have hneg : D.B V + D.N V < 0 := lt_of_not_ge hh
    have := mul_neg_of_pos_of_neg hCiPos hneg
    linarith [abs_nonneg (D.S₁.phi u v - D.S₂.phi u v)]
  have hdist : 0 < v - u := sub_pos.mpr huv.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (div_le_iff₀ hdist).2 (by
      simpa only [mul_comm] using D.radius_diff_le_L hVb.le huv)
  · exact (div_le_iff₀ hdist).2 (by
      simpa only [mul_comm] using D.radius_diff_le_N hVb huv)
  · exact hφo.trans (mul_le_mul_of_nonneg_right
      (show 2 * Co ^ 2 ≤ C from le_max_left _ _) hAo)
  · exact hφi.trans (mul_le_mul_of_nonneg_right
      (show 2 * Ci ^ 2 ≤ C from le_max_right _ _) hBi)

end ChristodoulouBV.Uniqueness

end
