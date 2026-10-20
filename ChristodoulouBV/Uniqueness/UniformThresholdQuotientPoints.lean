module

public import ChristodoulouBV.Uniqueness.UniformThresholdCoefficient
public import ChristodoulouBV.Uniqueness.QuotientNormPoints

/-!
# Package-uniform quotient point bounds
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The constant is selected from the numerical package before normalized comparison data. -/
theorem UniformThresholdBounds.quotient_differences_le_norms
    (P : UniformThresholdBounds) :
    ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
      P.Holds D.S₁ D.S₂ →
      ((∀ u v, (u, v) ∈ triangle D.a D.b →
        ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
          (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ P.gapThreshold ∧
          (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ P.gapThreshold) →
      ∀ V, D.a < V → V < D.b →
        ∀ u v, (u, v) ∈ triangle D.a V →
          (v ∈ D.goodV →
            |D.S₁.alpha u v / D.S₁.lam u v -
              D.S₂.alpha u v / D.S₂.lam u v| ≤ D.A V) ∧
          |D.S₁.beta u v / D.S₁.nu u v -
            D.S₂.beta u v / D.S₂.nu u v| ≤ D.B V) := by
  obtain ⟨C₁, hC₁, hcoef⟩ := P.coefficient_bounds_normalized
  intro D ha hb hP hsmall V haV hVb u v huv
  have hM : 0 ≤ 2 * C₁ := by linarith
  have hfield (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V)
      (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :=
    hcoef D ha hb hP (fun x y hxy S hS => (hsmall x y hxy S hS).1) x y
      ((mem_triangle).2 ⟨hxy.1, hxy.2.1, hxy.2.2.trans hVb⟩)
      S hS
  have hqbound (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V) :
      |D.S₁.alpha x y / D.S₁.lam x y -
        D.S₂.alpha x y / D.S₂.lam x y| ≤ 2 * C₁ ∧
      |D.S₁.beta x y / D.S₁.nu x y -
        D.S₂.beta x y / D.S₂.nu x y| ≤ 2 * C₁ := by
    rcases hfield x y hxy D.S₁ (Or.inl rfl) with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hα₁, hβ₁,
        _, _, _, _, _⟩
    rcases hfield x y hxy D.S₂ (Or.inr rfl) with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hα₂, hβ₂,
        _, _, _, _, _⟩
    constructor
    · calc
        |D.S₁.alpha x y / D.S₁.lam x y -
          D.S₂.alpha x y / D.S₂.lam x y| ≤
            |D.S₁.alpha x y / D.S₁.lam x y| +
              |D.S₂.alpha x y / D.S₂.lam x y| := abs_sub _ _
        _ ≤ C₁ + C₁ := add_le_add hα₁ hα₂
        _ = 2 * C₁ := by ring
    · calc
        |D.S₁.beta x y / D.S₁.nu x y -
          D.S₂.beta x y / D.S₂.nu x y| ≤
            |D.S₁.beta x y / D.S₁.nu x y| +
              |D.S₂.beta x y / D.S₂.nu x y| := abs_sub _ _
        _ ≤ C₁ + C₁ := add_le_add hβ₁ hβ₂
        _ = 2 * C₁ := by ring
  have hαgood (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V)
      (hyG : y ∈ D.goodV) :
      |D.S₁.alpha x y / D.S₁.lam x y -
        D.S₂.alpha x y / D.S₂.lam x y| ≤ D.A V :=
    D.le_goodVNorm hM (fun x y hxy _ => (hqbound x y hxy).1)
      hxy hyG
  have hβgood (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V)
      (hyG : y ∈ D.goodV) :
      |D.S₁.beta x y / D.S₁.nu x y -
        D.S₂.beta x y / D.S₂.nu x y| ≤ D.B V :=
    D.le_goodVNorm hM (fun x y hxy _ => (hqbound x y hxy).2)
      hxy hyG
  have hcont (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :
      ContinuousOn (fun t => S.beta u t / S.nu u t) (Ioo u V) := by
    obtain ⟨_, _, _, hnu, hbeta⟩ :=
      D.outgoing_continuous_primitives huv.1 hVb.le S hS
    have hnuNe : ∀ t ∈ Ioo u V, S.nu u t ≠ 0 := by
      intro t ht
      have htT : (u, t) ∈ triangle D.a D.b :=
        (mem_triangle).2 ⟨huv.1, ht.1, ht.2.trans hVb⟩
      rcases hS with rfl | rfl
      · obtain ⟨c, hc, hlam⟩ := D.h₁.lam_bounded_below
        have hn := D.h₁.nu_le_neg_lower hc hlam (D.hT htT).1
        exact ne_of_lt (hn.trans_lt (neg_lt_zero.mpr hc))
      · obtain ⟨c, hc, hlam⟩ := D.h₂.lam_bounded_below
        have hn := D.h₂.nu_le_neg_lower hc hlam (D.hT htT).2
        exact ne_of_lt (hn.trans_lt (neg_lt_zero.mpr hc))
    exact hbeta.div hnu hnuNe
  have hf : ContinuousOn
      (fun t => D.S₁.beta u t / D.S₁.nu u t -
        D.S₂.beta u t / D.S₂.nu u t) (Ioo u V) :=
    (hcont D.S₁ (Or.inl rfl)).sub (hcont D.S₂ (Or.inr rfl))
  constructor
  · exact hαgood u v huv
  · apply goodV_continuous_extension (D.goodV_properties).2.1 hf
    · intro t ht htG
      exact hβgood u t ((mem_triangle).2 ⟨huv.1, ht.1, ht.2⟩) htG
    · exact ⟨huv.2.1, huv.2.2⟩

end ChristodoulouBV.Uniqueness

end
