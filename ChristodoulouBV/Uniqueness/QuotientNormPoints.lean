module

public import ChristodoulouBV.Uniqueness.QuotientForcingFactors

/-!
# Pointwise access to the stable quotient norms

The `α/λ` norm samples only the fixed good incoming rays. Continuity of
`β/ν` in the outgoing coordinate extends its good-ray norm to every point.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- Under the fixed preliminary coefficient choice, `A` bounds the outgoing
scalar quotient difference on good rays and `B` bounds the incoming scalar
quotient difference everywhere on the compact triangle. -/
theorem ComparisonData.quotient_differences_le_norms (D : ComparisonData)
    (ha : D.a = 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ((∀ u v, (u, v) ∈ triangle D.a D.b →
        ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
          (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀ ∧
          (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε₀) →
      ∀ V, D.a < V → V < D.b →
        ∀ u v, (u, v) ∈ triangle D.a V →
          (v ∈ D.goodV →
            |D.S₁.alpha u v / D.S₁.lam u v -
              D.S₂.alpha u v / D.S₂.lam u v| ≤ D.A V) ∧
          |D.S₁.beta u v / D.S₁.nu u v -
            D.S₂.beta u v / D.S₂.nu u v| ≤ D.B V) := by
  let w := (D.a + D.b) / 2
  have hw : w ∈ Ioo D.a D.b := by
    dsimp [w]
    constructor <;> linarith [D.hab]
  have href : (0, w) ∈ D.U₁ ∩ D.U₂ := by
    simpa only [ha] using D.hT ((mem_triangle).2 ⟨le_rfl, hw.1, hw.2⟩)
  have hdata : D.S₁.phi 0 w = D.S₂.phi 0 w := by
    simpa only [ha] using (D.hdata w hw).2
  obtain ⟨_, _, ε₀, hε₀, C₁, hC₁, hcoef⟩ :=
    D.h₁.coefficient_bounds D.h₂ href hdata
  refine ⟨ε₀, hε₀, ?_⟩
  intro hsmall V haV hVb u v huv
  have hM : 0 ≤ 2 * C₁ := by linarith
  have hfield (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V)
      (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :=
    hcoef D.a D.b D.hT hsmall x y
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
