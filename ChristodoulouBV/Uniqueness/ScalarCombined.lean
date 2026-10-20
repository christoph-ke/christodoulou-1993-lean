module

public import ChristodoulouBV.Uniqueness.ScalarOutgoing
public import ChristodoulouBV.Uniqueness.ScalarIncoming

/-!
# Joint radius and scalar comparison estimates

The two scalar characteristic arguments share one preliminary threshold and
one cutoff-independent coefficient after taking maxima and minima.
-/

@[expose] public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Representative-stable versions of (3.3) and (3.7), jointly on every
compact top. The radius and scalar estimates hold even at exceptional
incoming coordinates, where λ and α themselves are not compared. -/
theorem ComparisonData.radius_scalar_goodV_bounds (D : ComparisonData)
    (ha : D.a = 0) (hb : D.b = 1) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∃ C : ℝ, 4 ≤ C ∧
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀ ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε₀) →
          ∀ V u v, V < D.b → (u, v) ∈ triangle D.a V →
            |D.S₁.r u v - D.S₂.r u v| / (v - u) ≤ D.L V ∧
            |D.S₁.r u v - D.S₂.r u v| / (v - u) ≤ D.N V ∧
            |D.S₁.phi u v - D.S₂.phi u v| ≤
              C * (D.A V + D.L V) ∧
            |D.S₁.phi u v - D.S₂.phi u v| ≤
              C * (D.B V + D.N V)) := by
  obtain ⟨C₀o, hC₀o, εo, hεo, Co, hCo, hout⟩ :=
    D.phi_diff_outgoing_le ha hb
  obtain ⟨C₀i, hC₀i, εi, hεi, Ci, hCi, hin⟩ :=
    D.phi_diff_incoming_le ha hb
  let C₀ := max C₀o C₀i
  let ε₀ := min εo εi
  let C := max (2 * Co ^ 2) (2 * Ci ^ 2)
  have hC₀ : 1 ≤ C₀ := hC₀o.trans (le_max_left _ _)
  have hε₀ : 0 < ε₀ := lt_min hεo hεi
  have hCoPos : 0 < 2 * Co ^ 2 := by positivity
  have hCiPos : 0 < 2 * Ci ^ 2 := by positivity
  have hC : 4 ≤ C := by
    dsimp [C]
    have hh : 4 ≤ 2 * Co ^ 2 := by nlinarith [sq_nonneg (Co - 4)]
    exact hh.trans (le_max_left _ _)
  refine ⟨C₀, hC₀, ε₀, hε₀, C, hC, ?_⟩
  intro hsmall V u v hVb huv
  have hsmallO : ∀ x y, (x, y) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        (eVariationOn (S.phi x) (Ioc x y)).toReal ≤ εo ∧
        (eVariationOn (fun s => S.phi s y) (Ico x y)).toReal ≤ εo := by
    intro x y hxy S hS
    obtain ⟨h₁, h₂⟩ := hsmall x y hxy S hS
    exact ⟨h₁.trans (min_le_left _ _), h₂.trans (min_le_left _ _)⟩
  have hsmallI : ∀ x y, (x, y) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        (eVariationOn (S.phi x) (Ioc x y)).toReal ≤ εi ∧
        (eVariationOn (fun s => S.phi s y) (Ico x y)).toReal ≤ εi := by
    intro x y hxy S hS
    obtain ⟨h₁, h₂⟩ := hsmall x y hxy S hS
    exact ⟨h₁.trans (min_le_right _ _), h₂.trans (min_le_right _ _)⟩
  have hφo := hout hsmallO V u v hVb huv
  have hφi := hin hsmallI V u v hVb huv
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
