module

public import ChristodoulouBV.Uniqueness.UniformThresholdScalarOutgoing
public import ChristodoulouBV.Uniqueness.ThetaGood

/-!
# Package-uniform outgoing density difference

The scalar and coefficient comparison weights determine a common theta
comparison constant before normalized data are selected.
-/

@[expose] public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The θ difference estimate (3.8a) holds at good outgoing density points.
Its constant does not depend on the compact comparison top. -/
theorem UniformThresholdBounds.theta_diff_goodV_le
    (P : UniformThresholdBounds) :
    ∃ C : ℝ, 4 ≤ C ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ P.gapThreshold) →
          ∀ V u v, V < D.b → (u, v) ∈ triangle D.a V →
            v ∈ D.goodV →
            |D.S₁.theta u v - D.S₂.theta u v| ≤
              C * (D.A V + D.L V)) := by
  obtain ⟨Cs, hCs, hscalar⟩ := P.phi_diff_outgoing_le
  obtain ⟨Cc, hCc, hcoeff⟩ := P.coefficient_bounds_normalized
  let C := Cc * (1 + 2 * Cs ^ 2)
  have hC : 4 ≤ C := by
    dsimp [C]
    nlinarith [sq_nonneg Cs, mul_nonneg (show 0 ≤ Cc by linarith) (sq_nonneg Cs)]
  refine ⟨C, hC, ?_⟩
  intro D ha hb hP hsmall V u v hVb huv hvG
  have hfield (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V)
      (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :=
    hcoeff D ha hb hP hsmall x y
      ((mem_triangle).2 ⟨hxy.1, hxy.2.1, hxy.2.2.trans hVb⟩) S hS
  have hbg (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V) :
      |D.S₁.lam x y| ≤ Cc ∧
      |D.S₂.theta x y / D.S₂.lam x y| ≤ Cc ∧
      |D.S₁.alpha x y / D.S₁.lam x y| ≤ Cc ∧
      |D.S₂.alpha x y / D.S₂.lam x y| ≤ Cc ∧
      |D.S₂.lam x y| ≤ Cc := by
    have hp := D.hT ((mem_triangle).2
      ⟨hxy.1, hxy.2.1, hxy.2.2.trans hVb⟩)
    rcases hfield x y hxy D.S₁ (Or.inl rfl) with
      ⟨_, hlam₁, _, _, _, _, _, _, _, _, _, _, _, hq₁,
        _, _, _, _, _, _⟩
    rcases hfield x y hxy D.S₂ (Or.inr rfl) with
      ⟨_, hlam₂, _, _, _, _, _, _, _, _, _, hθ₂, _, hq₂,
        _, _, _, _, _, _⟩
    exact ⟨by simpa only [abs_of_pos (D.h₁.solution.lam_pos (x,y) hp.1)] using hlam₁,
      hθ₂, hq₁, hq₂,
      by simpa only [abs_of_pos (D.h₂.solution.lam_pos (x,y) hp.2)] using hlam₂⟩
  have htwo : 0 ≤ 2 * Cc := by linarith
  have hLbound (x y : ℝ) (hxy : (x,y) ∈ triangle D.a V)
      (_hyG : y ∈ D.goodV) :
      |D.S₁.lam x y - D.S₂.lam x y| ≤ 2 * Cc := by
    have h := hbg x y hxy
    calc
      |D.S₁.lam x y - D.S₂.lam x y| ≤
          |D.S₁.lam x y| + |D.S₂.lam x y| := abs_sub _ _
      _ ≤ Cc + Cc := add_le_add h.1 h.2.2.2.2
      _ = 2 * Cc := by ring
  have hAbound (x y : ℝ) (hxy : (x,y) ∈ triangle D.a V)
      (_hyG : y ∈ D.goodV) :
      |D.S₁.alpha x y / D.S₁.lam x y -
        D.S₂.alpha x y / D.S₂.lam x y| ≤ 2 * Cc := by
    have h := hbg x y hxy
    calc
      |D.S₁.alpha x y / D.S₁.lam x y -
        D.S₂.alpha x y / D.S₂.lam x y| ≤
          |D.S₁.alpha x y / D.S₁.lam x y| +
          |D.S₂.alpha x y / D.S₂.lam x y| := abs_sub _ _
      _ ≤ Cc + Cc := add_le_add h.2.2.1 h.2.2.2.1
      _ = 2 * Cc := by ring
  have hLpoint : |D.S₁.lam u v - D.S₂.lam u v| ≤ D.L V :=
    D.le_goodVNorm htwo hLbound huv hvG
  have hApoint : |D.S₁.alpha u v / D.S₁.lam u v -
      D.S₂.alpha u v / D.S₂.lam u v| ≤ D.A V :=
    D.le_goodVNorm htwo hAbound huv hvG
  have hφ := hscalar D ha hb hP hsmall V u v hVb huv
  have hθ := D.theta_diff_pointwise_le
    ((mem_triangle).2 ⟨huv.1, huv.2.1, huv.2.2.trans hVb⟩)
    (show 0 ≤ Cc by linarith) (hbg u v huv).1
    (hbg u v huv).2.1 hApoint hLpoint hφ
  convert hθ using 1
  dsimp [C]
  ring


end ChristodoulouBV.Uniqueness

end
