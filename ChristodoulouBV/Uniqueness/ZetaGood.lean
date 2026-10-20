module

public import ChristodoulouBV.Uniqueness.ThetaZetaPointwise
public import ChristodoulouBV.Uniqueness.ScalarIncoming

/-!
# Good-ray zeta comparison

The preliminary variation threshold and coefficient constants are chosen
before the final contraction parameter and uniformly in the compact top.
-/

@[expose] public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The ζ difference estimate (3.8b) holds at good incoming rays.
Its constant does not depend on the compact comparison top. -/
theorem ComparisonData.zeta_diff_goodV_le (D : ComparisonData)
    (ha : D.a = 0) (hb : D.b = 1) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∃ C : ℝ, 4 ≤ C ∧
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀ ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε₀) →
          ∀ V u v, V < D.b → (u, v) ∈ triangle D.a V →
            v ∈ D.goodV →
            |D.S₁.zeta u v - D.S₂.zeta u v| ≤
              C * (D.B V + D.N V)) := by
  obtain ⟨C₀s, hC₀s, εs, hεs, Cs, hCs, hscalar⟩ :=
    D.phi_diff_incoming_le ha hb
  have hw : (D.a, (1 / 2 : ℝ)) ∈ triangle D.a D.b := by
    rw [ha, hb]
    exact initial_edge_of_triangle (by norm_num) (by norm_num)
  have href : (0, (1 / 2 : ℝ)) ∈ D.U₁ ∩ D.U₂ := by
    simpa only [ha] using D.hT hw
  have hdatum : D.S₁.phi 0 (1 / 2 : ℝ) = D.S₂.phi 0 (1 / 2 : ℝ) := by
    have hh := (D.hdata (1 / 2 : ℝ)
      (by rw [ha, hb]; constructor <;> norm_num)).2
    simpa only [ha] using hh
  obtain ⟨C₀c, hC₀c, εc, hεc, Cc, hCc, hcoeff⟩ :=
    D.h₁.coefficient_bounds D.h₂ href hdatum
  let C₀ := max C₀s C₀c
  let ε₀ := min εs εc
  let C := Cc * (1 + 2 * Cs ^ 2)
  have hC₀ : 1 ≤ C₀ := hC₀s.trans (le_max_left _ _)
  have hε₀ : 0 < ε₀ := lt_min hεs hεc
  have hC : 4 ≤ C := by
    dsimp [C]
    nlinarith [sq_nonneg Cs, mul_nonneg (show 0 ≤ Cc by linarith) (sq_nonneg Cs)]
  refine ⟨C₀, hC₀, ε₀, hε₀, C, hC, ?_⟩
  intro hsmall V u v hVb huv hvG
  have hsmallS : ∀ x y, (x, y) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        (eVariationOn (S.phi x) (Ioc x y)).toReal ≤ εs ∧
        (eVariationOn (fun s => S.phi s y) (Ico x y)).toReal ≤ εs := by
    intro x y hxy S hS
    obtain ⟨h₁, h₂⟩ := hsmall x y hxy S hS
    exact ⟨h₁.trans (min_le_left _ _), h₂.trans (min_le_left _ _)⟩
  have hsmallC : ∀ x y, (x, y) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        (eVariationOn (S.phi x) (Ioc x y)).toReal ≤ εc ∧
        (eVariationOn (fun s => S.phi s y) (Ico x y)).toReal ≤ εc := by
    intro x y hxy S hS
    obtain ⟨h₁, h₂⟩ := hsmall x y hxy S hS
    exact ⟨h₁.trans (min_le_right _ _), h₂.trans (min_le_right _ _)⟩
  have hfield (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V)
      (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :=
    hcoeff D.a D.b D.hT hsmallC x y
      ((mem_triangle).2 ⟨hxy.1, hxy.2.1, hxy.2.2.trans hVb⟩) S hS
  have hbg (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V) :
      |D.S₁.nu x y| ≤ Cc ∧
      |D.S₂.zeta x y / D.S₂.nu x y| ≤ Cc ∧
      |D.S₁.beta x y / D.S₁.nu x y| ≤ Cc ∧
      |D.S₂.beta x y / D.S₂.nu x y| ≤ Cc ∧
      |D.S₂.nu x y| ≤ Cc := by
    rcases hfield x y hxy D.S₁ (Or.inl rfl) with
      ⟨_, _, _, hnu₁, _, _, _, _, _, _, _, _, _, _, hq₁,
        _, _, _, _, _⟩
    rcases hfield x y hxy D.S₂ (Or.inr rfl) with
      ⟨_, _, _, hnu₂, _, _, _, _, _, _, _, _, hζ₂, _, hq₂,
        _, _, _, _, _⟩
    exact ⟨hnu₁, hζ₂, hq₁, hq₂, hnu₂⟩
  have htwo : 0 ≤ 2 * Cc := by linarith
  have hNbound (x y : ℝ) (hxy : (x,y) ∈ triangle D.a V)
      (_hyG : y ∈ D.goodV) :
      |D.S₁.nu x y - D.S₂.nu x y| ≤ 2 * Cc := by
    have h := hbg x y hxy
    calc
      |D.S₁.nu x y - D.S₂.nu x y| ≤
          |D.S₁.nu x y| + |D.S₂.nu x y| := abs_sub _ _
      _ ≤ Cc + Cc := add_le_add h.1 h.2.2.2.2
      _ = 2 * Cc := by ring
  have hBbound (x y : ℝ) (hxy : (x,y) ∈ triangle D.a V)
      (_hyG : y ∈ D.goodV) :
      |D.S₁.beta x y / D.S₁.nu x y -
        D.S₂.beta x y / D.S₂.nu x y| ≤ 2 * Cc := by
    have h := hbg x y hxy
    calc
      |D.S₁.beta x y / D.S₁.nu x y -
        D.S₂.beta x y / D.S₂.nu x y| ≤
          |D.S₁.beta x y / D.S₁.nu x y| +
          |D.S₂.beta x y / D.S₂.nu x y| := abs_sub _ _
      _ ≤ Cc + Cc := add_le_add h.2.2.1 h.2.2.2.1
      _ = 2 * Cc := by ring
  have hNpoint : |D.S₁.nu u v - D.S₂.nu u v| ≤ D.N V :=
    D.le_goodVNorm htwo hNbound huv hvG
  have hBpoint : |D.S₁.beta u v / D.S₁.nu u v -
      D.S₂.beta u v / D.S₂.nu u v| ≤ D.B V :=
    D.le_goodVNorm htwo hBbound huv hvG
  have hφ := hscalar hsmallS V u v hVb huv
  have hζ := D.zeta_diff_pointwise_le
    ((mem_triangle).2 ⟨huv.1, huv.2.1, huv.2.2.trans hVb⟩)
    (show 0 ≤ Cc by linarith) (hbg u v huv).1
    (hbg u v huv).2.1 hBpoint hNpoint hφ
  convert hζ using 1
  dsimp [C]
  ring

/-- Continuity of β, ν, and φ carries the ζ comparison from good incoming
rays to every point of the truncated triangle, including exceptional values
of the derivative representatives. -/
theorem ComparisonData.zeta_diff_le (D : ComparisonData)
    (ha : D.a = 0) (hb : D.b = 1) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∃ C : ℝ, 4 ≤ C ∧
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀ ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε₀) →
          ∀ V u v, V < D.b → (u, v) ∈ triangle D.a V →
            |D.S₁.zeta u v - D.S₂.zeta u v| ≤
              C * (D.B V + D.N V)) := by
  obtain ⟨C₀, hC₀, ε₀, hε₀, C, hC, hgood⟩ :=
    D.zeta_diff_goodV_le ha hb
  refine ⟨C₀, hC₀, ε₀, hε₀, C, hC, ?_⟩
  intro hsmall V u v hVb huv
  have hcont (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :
      ContinuousOn (S.zeta u) (Ioo u V) := by
    obtain ⟨_, _, _, hnu, hbeta⟩ :=
      D.outgoing_continuous_primitives huv.1 hVb.le S hS
    have hphi := D.phi_continuousOn_outgoing huv.1 hVb.le S hS
    change ContinuousOn
      (fun t => S.beta u t - S.nu u t * S.phi u t) (Ioo u V)
    exact hbeta.sub (hnu.mul hphi)
  have hf : ContinuousOn
      (fun t => D.S₁.zeta u t - D.S₂.zeta u t)
      (Ioo u V) :=
    (hcont D.S₁ (Or.inl rfl)).sub (hcont D.S₂ (Or.inr rfl))
  apply goodV_continuous_extension (D.goodV_properties).2.1 hf
  · intro t ht htG
    exact hgood hsmall V u t hVb
      ((mem_triangle).2 ⟨huv.1, ht.1, ht.2⟩) htG
  · exact ⟨huv.2.1, huv.2.2⟩

end ChristodoulouBV.Uniqueness

end
