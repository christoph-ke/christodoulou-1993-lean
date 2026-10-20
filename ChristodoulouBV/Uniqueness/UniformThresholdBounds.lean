module

public import ChristodoulouBV.Uniqueness.Rescaling
public import ChristodoulouBV.BVSolution.PrelocalFieldBounds

/-!
# Bounds shared by all normalized charts of a fixed BV pair

The numbers in `UniformThresholdBounds` bound the coefficients and scalar
amplitudes on the unit comparison triangle. They are chosen from the original
solutions before the axis point and rescaling width are selected.
-/

@[expose] public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A numerical lower and upper bound for the basic comparison fields. -/
structure UniformThresholdBounds where
  c : ℝ
  C : ℝ
  variation : ℝ
  radiusLower : ℝ
  radiusUpper : ℝ
  c_pos : 0 < c
  C_nonneg : 0 ≤ C
  variation_nonneg : 0 ≤ variation
  radiusLower_pos : 0 < radiusLower

/-- One field has all three global BV variation bounds with the same number. -/
def UniformThresholdBounds.VariationHoldsOne (P : UniformThresholdBounds)
    (U : Set (ℝ × ℝ)) (S : Fields) : Prop :=
  (∀ u, eVariationOn (S.lam u) {v | (u, v) ∈ U} ≤
      ENNReal.ofReal P.variation) ∧
  (∀ v, eVariationOn (fun u => S.nu u v) {u | (u, v) ∈ U} ≤
      ENNReal.ofReal P.variation) ∧
  (∀ u, eVariationOn (S.phi u) {v | (u, v) ∈ U} ≤
      ENNReal.ofReal P.variation) ∧
  (∀ v, eVariationOn (fun u => S.phi u v) {u | (u, v) ∈ U} ≤
      ENNReal.ofReal P.variation) ∧
  (∀ u, eVariationOn (S.theta u) {v | (u, v) ∈ U} ≤
      ENNReal.ofReal P.variation) ∧
  (∀ v, eVariationOn (fun u => S.zeta u v) {u | (u, v) ∈ U} ≤
      ENNReal.ofReal P.variation)

/-- Both fields of a normalized comparison satisfy the same basic bounds. -/
def UniformThresholdBounds.Holds (P : UniformThresholdBounds)
    (S₁ S₂ : Fields) : Prop :=
  ∀ u v, (u, v) ∈ triangle 0 1 →
    ∀ S : Fields, (S = S₁ ∨ S = S₂) →
      P.c ≤ S.lam u v ∧ S.lam u v ≤ P.C ∧
      P.c ≤ |S.nu u v| ∧ |S.nu u v| ≤ P.C ∧
      |S.phi u v| ≤ P.C ∧ |S.theta u v| ≤ P.C ∧
      |S.zeta u v| ≤ P.C ∧
      P.radiusLower * (v - u) ≤ S.r u v ∧
      S.r u v ≤ P.radiusUpper * (v - u)

/-- Radius-to-axis-distance bounds are unchanged by positive affine charts. -/
private theorem rescaled_radius_bounds_of_source (S : Fields)
    {a h u v d K : ℝ} (hh : 0 < h)
    (hr : d * (affineCoordinate a h v - affineCoordinate a h u) ≤
        S.r (affineCoordinate a h u) (affineCoordinate a h v) ∧
      S.r (affineCoordinate a h u) (affineCoordinate a h v) ≤
        K * (affineCoordinate a h v - affineCoordinate a h u)) :
    d * (v - u) ≤ (rescaledFields S a h).r u v ∧
      (rescaledFields S a h).r u v ≤ K * (v - u) := by
  have heq : affineCoordinate a h v - affineCoordinate a h u = h * (v - u) := by
    dsimp [affineCoordinate]
    ring
  rw [heq] at hr
  constructor
  · change d * (v - u) ≤
      S.r (affineCoordinate a h u) (affineCoordinate a h v) / h
    apply (le_div_iff₀ hh).2
    nlinarith only [hr.1]
  · change S.r (affineCoordinate a h u) (affineCoordinate a h v) / h ≤
      K * (v - u)
    apply (div_le_iff₀ hh).2
    nlinarith only [hr.2]

/-- One package obtained from the original global BV bounds works in every
positive affine chart whose complete local triangle belongs to both domains.
The two scalar reference values may differ away from the common initial edge. -/
theorem exists_uniform_threshold_bounds_of_fixed_pair
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {w₁ w₂ : ℝ} (href₁ : (0, w₁) ∈ U₁) (href₂ : (0, w₂) ∈ U₂) :
    ∃ P : UniformThresholdBounds,
      ∀ a h : ℝ, 0 < h → triangle a (a + h) ⊆ U₁ ∩ U₂ →
        P.Holds (rescaledFields S₁ a h) (rescaledFields S₂ a h) ∧
        P.VariationHoldsOne (rescaledDomain U₁ a h) (rescaledFields S₁ a h) ∧
        P.VariationHoldsOne (rescaledDomain U₂ a h) (rescaledFields S₂ a h) := by
  obtain ⟨c₁, C₁, hc₁, _, hb₁⟩ := h₁.exists_preloc_field_bounds href₁
  obtain ⟨c₂, C₂, hc₂, hC₂, hb₂⟩ := h₂.exists_preloc_field_bounds href₂
  obtain ⟨d₁, K₁, hd₁, hr₁⟩ := h₁.exists_uniform_radius_bounds
  obtain ⟨d₂, K₂, hd₂, hr₂⟩ := h₂.exists_uniform_radius_bounds
  obtain ⟨V₁₁, hV₁₁o, hV₁₁i⟩ := h₁.item1
  obtain ⟨V₁₃, hV₁₃o, hV₁₃i⟩ := h₁.item3_variation
  obtain ⟨V₁₅, hV₁₅o, hV₁₅i⟩ := h₁.item5
  obtain ⟨V₂₁, hV₂₁o, hV₂₁i⟩ := h₂.item1
  obtain ⟨V₂₃, hV₂₃o, hV₂₃i⟩ := h₂.item3_variation
  obtain ⟨V₂₅, hV₂₅o, hV₂₅i⟩ := h₂.item5
  let V := max 0 V₁₁ + max 0 V₁₃ + max 0 V₁₅ +
    max 0 V₂₁ + max 0 V₂₃ + max 0 V₂₅
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have ⟨hV₁₁, hV₁₃, hV₁₅, hV₂₁, hV₂₃, hV₂₅⟩ :
      V₁₁ ≤ V ∧ V₁₃ ≤ V ∧ V₁₅ ≤ V ∧
      V₂₁ ≤ V ∧ V₂₃ ≤ V ∧ V₂₅ ≤ V := by
    dsimp [V]
    have h₁₁ := le_max_left (0 : ℝ) V₁₁
    have h₁₃ := le_max_left (0 : ℝ) V₁₃
    have h₁₅ := le_max_left (0 : ℝ) V₁₅
    have h₂₁ := le_max_left (0 : ℝ) V₂₁
    have h₂₃ := le_max_left (0 : ℝ) V₂₃
    have h₂₅ := le_max_left (0 : ℝ) V₂₅
    have g₁₁ := le_max_right (0 : ℝ) V₁₁
    have g₁₃ := le_max_right (0 : ℝ) V₁₃
    have g₁₅ := le_max_right (0 : ℝ) V₁₅
    have g₂₁ := le_max_right (0 : ℝ) V₂₁
    have g₂₃ := le_max_right (0 : ℝ) V₂₃
    have g₂₅ := le_max_right (0 : ℝ) V₂₅
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  let P : UniformThresholdBounds :=
    ⟨min c₁ c₂, max C₁ C₂, V, min d₁ d₂, max K₁ K₂,
      lt_min hc₁ hc₂, hC₂.trans (le_max_right _ _), hV, lt_min hd₁ hd₂⟩
  refine ⟨P, ?_⟩
  intro a h hh hT
  constructor
  · intro u v huv S hS
    have hmap : (affineCoordinate a h u, affineCoordinate a h v) ∈
        triangle a (a + h) := by
      rw [← affinePair_image_triangle a hh]
      exact ⟨(u, v), huv, rfl⟩
    rcases hS with rfl | rfl
    · have hT₁ : triangle a (a + h) ⊆ U₁ := fun p hp => (hT hp).1
      obtain ⟨hlo, hhi, hnlo, hnhi, hphi, htheta, hzeta⟩ :=
        hb₁ a (a + h) _ _ hT₁ hmap
      change P.c ≤ (rescaledFields S₁ a h).lam u v ∧
      (rescaledFields S₁ a h).lam u v ≤ P.C ∧
      P.c ≤ |(rescaledFields S₁ a h).nu u v| ∧
      |(rescaledFields S₁ a h).nu u v| ≤ P.C ∧
      |(rescaledFields S₁ a h).phi u v| ≤ P.C ∧
      |(rescaledFields S₁ a h).theta u v| ≤ P.C ∧
      |(rescaledFields S₁ a h).zeta u v| ≤ P.C ∧
      P.radiusLower * (v - u) ≤ (rescaledFields S₁ a h).r u v ∧
      (rescaledFields S₁ a h).r u v ≤ P.radiusUpper * (v - u)
      rw [rescaled_theta S₁ a h u v, rescaled_zeta S₁ a h u v]
      have hr := rescaled_radius_bounds_of_source S₁ hh
        (hr₁ _ _ (hT hmap).1)
      have hd : 0 ≤ v - u := sub_nonneg.mpr huv.2.1.le
      have hradLo : min d₁ d₂ * (v - u) ≤
          (rescaledFields S₁ a h).r u v :=
        (mul_le_mul_of_nonneg_right (min_le_left _ _) hd).trans hr.1
      have hradHi : (rescaledFields S₁ a h).r u v ≤
          max K₁ K₂ * (v - u) :=
        hr.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd)
      simpa only [P, rescaledFields] using
      (show min c₁ c₂ ≤ S₁.lam (affineCoordinate a h u) (affineCoordinate a h v) ∧
        S₁.lam (affineCoordinate a h u) (affineCoordinate a h v) ≤ max C₁ C₂ ∧
        min c₁ c₂ ≤ |S₁.nu (affineCoordinate a h u) (affineCoordinate a h v)| ∧
        |S₁.nu (affineCoordinate a h u) (affineCoordinate a h v)| ≤ max C₁ C₂ ∧
        |S₁.phi (affineCoordinate a h u) (affineCoordinate a h v)| ≤ max C₁ C₂ ∧
        |S₁.theta (affineCoordinate a h u) (affineCoordinate a h v)| ≤ max C₁ C₂ ∧
        |S₁.zeta (affineCoordinate a h u) (affineCoordinate a h v)| ≤ max C₁ C₂ ∧
        min d₁ d₂ * (v - u) ≤ (rescaledFields S₁ a h).r u v ∧
        (rescaledFields S₁ a h).r u v ≤ max K₁ K₂ * (v - u) from
        ⟨(min_le_left _ _).trans hlo, hhi.trans (le_max_left _ _),
          (min_le_left _ _).trans hnlo, hnhi.trans (le_max_left _ _),
          hphi.trans (le_max_left _ _), htheta.trans (le_max_left _ _),
          hzeta.trans (le_max_left _ _), hradLo, hradHi⟩)
    · have hT₂ : triangle a (a + h) ⊆ U₂ := fun p hp => (hT hp).2
      obtain ⟨hlo, hhi, hnlo, hnhi, hphi, htheta, hzeta⟩ :=
        hb₂ a (a + h) _ _ hT₂ hmap
      change P.c ≤ (rescaledFields S₂ a h).lam u v ∧
      (rescaledFields S₂ a h).lam u v ≤ P.C ∧
      P.c ≤ |(rescaledFields S₂ a h).nu u v| ∧
      |(rescaledFields S₂ a h).nu u v| ≤ P.C ∧
      |(rescaledFields S₂ a h).phi u v| ≤ P.C ∧
      |(rescaledFields S₂ a h).theta u v| ≤ P.C ∧
      |(rescaledFields S₂ a h).zeta u v| ≤ P.C ∧
      P.radiusLower * (v - u) ≤ (rescaledFields S₂ a h).r u v ∧
      (rescaledFields S₂ a h).r u v ≤ P.radiusUpper * (v - u)
      rw [rescaled_theta S₂ a h u v, rescaled_zeta S₂ a h u v]
      have hr := rescaled_radius_bounds_of_source S₂ hh
        (hr₂ _ _ (hT hmap).2)
      have hd : 0 ≤ v - u := sub_nonneg.mpr huv.2.1.le
      have hradLo : min d₁ d₂ * (v - u) ≤
          (rescaledFields S₂ a h).r u v :=
        (mul_le_mul_of_nonneg_right (min_le_right _ _) hd).trans hr.1
      have hradHi : (rescaledFields S₂ a h).r u v ≤
          max K₁ K₂ * (v - u) :=
        hr.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hd)
      simpa only [P, rescaledFields] using
      (show min c₁ c₂ ≤ S₂.lam (affineCoordinate a h u) (affineCoordinate a h v) ∧
        S₂.lam (affineCoordinate a h u) (affineCoordinate a h v) ≤ max C₁ C₂ ∧
        min c₁ c₂ ≤ |S₂.nu (affineCoordinate a h u) (affineCoordinate a h v)| ∧
        |S₂.nu (affineCoordinate a h u) (affineCoordinate a h v)| ≤ max C₁ C₂ ∧
        |S₂.phi (affineCoordinate a h u) (affineCoordinate a h v)| ≤ max C₁ C₂ ∧
        |S₂.theta (affineCoordinate a h u) (affineCoordinate a h v)| ≤ max C₁ C₂ ∧
        |S₂.zeta (affineCoordinate a h u) (affineCoordinate a h v)| ≤ max C₁ C₂ ∧
        min d₁ d₂ * (v - u) ≤ (rescaledFields S₂ a h).r u v ∧
        (rescaledFields S₂ a h).r u v ≤ max K₁ K₂ * (v - u) from
        ⟨(min_le_right _ _).trans hlo, hhi.trans (le_max_right _ _),
          (min_le_right _ _).trans hnlo, hnhi.trans (le_max_right _ _),
          hphi.trans (le_max_right _ _), htheta.trans (le_max_right _ _),
          hzeta.trans (le_max_right _ _), hradLo, hradHi⟩)
  constructor
  · unfold UniformThresholdBounds.VariationHoldsOne
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u
      exact (rescaled_outVariation_le (f := S₁.lam) hh u).trans
        ((hV₁₁o _).trans (ENNReal.ofReal_le_ofReal hV₁₁))
    · intro v
      exact (rescaled_inVariation_le (f := S₁.nu) hh v).trans
        ((hV₁₁i _).trans (ENNReal.ofReal_le_ofReal hV₁₁))
    · intro u
      exact (rescaled_outVariation_le (f := S₁.phi) hh u).trans
        ((hV₁₃o _).trans (ENNReal.ofReal_le_ofReal hV₁₃))
    · intro v
      exact (rescaled_inVariation_le (f := S₁.phi) hh v).trans
        ((hV₁₃i _).trans (ENNReal.ofReal_le_ofReal hV₁₃))
    · intro u
      change eVariationOn (fun v => S₁.theta (affineCoordinate a h u)
        (affineCoordinate a h v)) _ ≤ _
      exact (rescaled_outVariation_le (f := S₁.theta) hh u).trans
        ((hV₁₅o _).trans (ENNReal.ofReal_le_ofReal hV₁₅))
    · intro v
      change eVariationOn (fun u => S₁.zeta (affineCoordinate a h u)
        (affineCoordinate a h v)) _ ≤ _
      exact (rescaled_inVariation_le (f := S₁.zeta) hh v).trans
        ((hV₁₅i _).trans (ENNReal.ofReal_le_ofReal hV₁₅))
  · unfold UniformThresholdBounds.VariationHoldsOne
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u
      exact (rescaled_outVariation_le (f := S₂.lam) hh u).trans
        ((hV₂₁o _).trans (ENNReal.ofReal_le_ofReal hV₂₁))
    · intro v
      exact (rescaled_inVariation_le (f := S₂.nu) hh v).trans
        ((hV₂₁i _).trans (ENNReal.ofReal_le_ofReal hV₂₁))
    · intro u
      exact (rescaled_outVariation_le (f := S₂.phi) hh u).trans
        ((hV₂₃o _).trans (ENNReal.ofReal_le_ofReal hV₂₃))
    · intro v
      exact (rescaled_inVariation_le (f := S₂.phi) hh v).trans
        ((hV₂₃i _).trans (ENNReal.ofReal_le_ofReal hV₂₃))
    · intro u
      change eVariationOn (fun v => S₂.theta (affineCoordinate a h u)
        (affineCoordinate a h v)) _ ≤ _
      exact (rescaled_outVariation_le (f := S₂.theta) hh u).trans
        ((hV₂₅o _).trans (ENNReal.ofReal_le_ofReal hV₂₅))
    · intro v
      change eVariationOn (fun u => S₂.zeta (affineCoordinate a h u)
        (affineCoordinate a h v)) _ ≤ _
      exact (rescaled_inVariation_le (f := S₂.zeta) hh v).trans
        ((hV₂₅i _).trans (ENNReal.ofReal_le_ofReal hV₂₅))

end ChristodoulouBV.Uniqueness

end
