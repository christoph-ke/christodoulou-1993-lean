module

public import ChristodoulouBV.Uniqueness.UniformThresholdScalarIncoming
public import ChristodoulouBV.Uniqueness.ZetaGood

/-!
# Package-uniform incoming density difference

The scalar and coefficient constants give one zeta comparison constant
before normalized comparison data are selected.
-/

@[expose] public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The ζ difference estimate (3.8b) holds at good incoming rays.
Its constant does not depend on the compact comparison top. -/
theorem UniformThresholdBounds.zeta_diff_goodV_le
    (P : UniformThresholdBounds) :
    ∃ C : ℝ, 4 ≤ C ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ P.gapThreshold) →
          ∀ V u v, V < D.b → (u, v) ∈ triangle D.a V →
            v ∈ D.goodV →
            |D.S₁.zeta u v - D.S₂.zeta u v| ≤
              C * (D.B V + D.N V)) := by
  obtain ⟨Cs, hCs, hscalar⟩ := P.phi_diff_incoming_le
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
  have hφ := hscalar D ha hb hP hsmall V u v hVb huv
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
theorem UniformThresholdBounds.zeta_diff_le
    (P : UniformThresholdBounds) :
    ∃ C : ℝ, 4 ≤ C ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ P.gapThreshold) →
          ∀ V u v, V < D.b → (u, v) ∈ triangle D.a V →
            |D.S₁.zeta u v - D.S₂.zeta u v| ≤
              C * (D.B V + D.N V)) := by
  obtain ⟨C, hC, hgood⟩ := P.zeta_diff_goodV_le
  refine ⟨C, hC, ?_⟩
  intro D ha hb hP hsmall V u v hVb huv
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
    exact hgood D ha hb hP hsmall V u t hVb
      ((mem_triangle).2 ⟨huv.1, ht.1, ht.2⟩) htG
  · exact ⟨huv.2.1, huv.2.2⟩


end ChristodoulouBV.Uniqueness

end
