module

public import ChristodoulouBV.Uniqueness.UniformThresholdContraction
public import ChristodoulouBV.Uniqueness.AxisLocalization

/-!
# Axis localization with a uniform threshold

The numerical package selects the threshold before any local scale.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- Affine normalization preserves the package-dependent uniqueness threshold. -/
theorem UniformThresholdBounds.scaled_local_unique
    (P : UniformThresholdBounds) :
    ∃ εfinal : ℝ, 0 < εfinal ∧
      ∀ {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields} {a h : ℝ},
        IsBVSolution U₁ S₁ → IsBVSolution U₂ S₂ →
        0 ≤ a → 0 < h →
        triangle a (a + h) ⊆ U₁ ∩ U₂ →
        (∀ v ∈ Ioo a (a + h),
          S₁.r a v = S₂.r a v ∧ S₁.phi a v = S₂.phi a v) →
        P.Holds (rescaledFields S₁ a h) (rescaledFields S₂ a h) →
        P.VariationHoldsOne (rescaledDomain U₁ a h) (rescaledFields S₁ a h) →
        P.VariationHoldsOne (rescaledDomain U₂ a h) (rescaledFields S₂ a h) →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ εfinal →
        (∀ u v, (u, v) ∈ triangle a (a + h) →
          ∀ S : Fields, (S = S₁ ∨ S = S₂) →
            eVariationOn (S.phi u) (Ioo u v) ≤ ENNReal.ofReal ε ∧
            eVariationOn (fun s => S.phi s v) (Ioo u v) ≤ ENNReal.ofReal ε) →
        ∀ u v, (u, v) ∈ triangle a (a + h) →
          S₁.r u v = S₂.r u v ∧
          S₁.phi u v = S₂.phi u v ∧
          S₁.m u v = S₂.m u v := by
  obtain ⟨εfinal, hεfinal, huniform⟩ := P.local_unique
  refine ⟨εfinal, hεfinal, ?_⟩
  intro U₁ U₂ S₁ S₂ a h h₁ h₂ ha hh hT hdata hP hvar₁ hvar₂
    ε hε hεfinal hsmall u v huv
  let R₁ := rescaledFields S₁ a h
  let R₂ := rescaledFields S₂ a h
  let W₁ := rescaledDomain U₁ a h
  let W₂ := rescaledDomain U₂ a h
  have hT' : triangle 0 1 ⊆ W₁ ∩ W₂ := by
    intro p hp
    have hsource : affinePair a h p ∈ triangle a (a + h) := by
      rw [← affinePair_image_triangle a hh]
      exact ⟨p, hp, rfl⟩
    obtain ⟨hu₁, hu₂⟩ := hT hsource
    exact ⟨⟨hp.1, hu₁⟩, ⟨hp.1, hu₂⟩⟩
  have hdata' : ∀ v ∈ Ioo 0 1,
      R₁.r 0 v = R₂.r 0 v ∧ R₁.phi 0 v = R₂.phi 0 v := by
    intro v hv
    have hvp : (0, v) ∈ triangle 0 1 := initial_edge_of_triangle hv.1 hv.2
    have hsource : (a, affineCoordinate a h v) ∈ triangle a (a + h) := by
      have hh' := (affinePair_image_triangle a hh).symm
      have hmem : affinePair a h (0, v) ∈ triangle a (a + h) := by
        rw [← affinePair_image_triangle a hh]
        exact ⟨(0, v), hvp, rfl⟩
      simpa only [affinePair, affineCoordinate, mul_zero, add_zero] using hmem
    have hvI : affineCoordinate a h v ∈ Ioo a (a + h) :=
      ⟨hsource.2.1, hsource.2.2⟩
    obtain ⟨hr, hφ⟩ := hdata _ hvI
    exact ⟨by simpa only [R₁, R₂, rescaledFields, affineCoordinate,
        mul_zero, add_zero] using congrArg (fun x : ℝ => x / h) hr,
      by simpa only [R₁, R₂, rescaledFields, affineCoordinate,
        mul_zero, add_zero] using hφ⟩
  let D : ComparisonData := {
    U₁ := W₁
    U₂ := W₂
    S₁ := R₁
    S₂ := R₂
    a := 0
    b := 1
    hab := by norm_num
    h₁ := rescaled_isBVSolution h₁ ha hh
    h₂ := rescaled_isBVSolution h₂ ha hh
    hT := hT'
    hdata := hdata' }
  have hlocal := huniform D rfl rfl hP hvar₁ hvar₂
  have hsmall' : ∀ x y, (x, y) ∈ triangle D.a D.b →
      ∀ R : Fields, (R = D.S₁ ∨ R = D.S₂) →
        (eVariationOn (R.phi x) (Ioc x y)).toReal ≤ ε ∧
        (eVariationOn (fun s => R.phi s y) (Ico x y)).toReal ≤ ε := by
    intro x y hxy R hR
    have hxy' : (x, y) ∈ triangle 0 1 := hxy
    have hsrc : (affineCoordinate a h x, affineCoordinate a h y) ∈
        triangle a (a + h) := by
      have hmem : affinePair a h (x, y) ∈ triangle a (a + h) := by
        rw [← affinePair_image_triangle a hh]
        exact ⟨(x, y), hxy', rfl⟩
      exact hmem
    rcases hR with rfl | rfl
    · have heq := characteristic_variations_eq_open (a := 0) (h := 1)
          (rescaled_isBVSolution h₁ ha hh)
          (by intro p hp; exact (hT' (by simpa only [zero_add] using hp)).1)
          (by simpa only [zero_add] using hxy')
      have hbound := hsmall _ _ hsrc S₁ (Or.inl rfl)
      constructor
      · rw [heq.1, rescaled_outgoing_variation_eq S₁ hh x y]
        exact (ENNReal.toReal_mono (by simp) hbound.1).trans_eq
          (ENNReal.toReal_ofReal hε)
      · rw [heq.2, rescaled_incoming_variation_eq S₁ hh y x]
        exact (ENNReal.toReal_mono (by simp) hbound.2).trans_eq
          (ENNReal.toReal_ofReal hε)
    · have heq := characteristic_variations_eq_open (a := 0) (h := 1)
          (rescaled_isBVSolution h₂ ha hh)
          (by intro p hp; exact (hT' (by simpa only [zero_add] using hp)).2)
          (by simpa only [zero_add] using hxy')
      have hbound := hsmall _ _ hsrc S₂ (Or.inr rfl)
      constructor
      · rw [heq.1, rescaled_outgoing_variation_eq S₂ hh x y]
        exact (ENNReal.toReal_mono (by simp) hbound.1).trans_eq
          (ENNReal.toReal_ofReal hε)
      · rw [heq.2, rescaled_incoming_variation_eq S₂ hh y x]
        exact (ENNReal.toReal_mono (by simp) hbound.2).trans_eq
          (ENNReal.toReal_ofReal hε)
  have hinv : inverseAffinePair a h (u, v) ∈ triangle 0 1 := by
    rw [← rescaledDomain_triangle a hh]
    exact ⟨by dsimp [inverseAffinePair]; exact div_nonneg (sub_nonneg.mpr huv.1) hh.le,
      by change affinePair a h (inverseAffinePair a h (u, v)) ∈ triangle a (a + h)
         rw [affinePair_inverse a hh]
         exact huv⟩
  obtain ⟨hr, hφ, hm⟩ := hlocal ε hε hεfinal hsmall'
    _ _ hinv
  have hu : affineCoordinate a h ((u - a) / h) = u := by
    dsimp [affineCoordinate]
    field_simp [hh.ne']
    ring
  have hv : affineCoordinate a h ((v - a) / h) = v := by
    dsimp [affineCoordinate]
    field_simp [hh.ne']
    ring
  have hr' : S₁.r u v / h = S₂.r u v / h := by
    simpa only [D, R₁, R₂, rescaledFields, Prod.fst, Prod.snd,
      inverseAffinePair, hu, hv] using hr
  have hφ' : S₁.phi u v = S₂.phi u v := by
    simpa only [D, R₁, R₂, rescaledFields, Prod.fst, Prod.snd,
      inverseAffinePair, hu, hv] using hφ
  have hm' : S₁.m u v / h = S₂.m u v / h := by
    simpa only [D, R₁, R₂, rescaledFields, Prod.fst, Prod.snd,
      inverseAffinePair, hu, hv] using hm
  constructor
  · apply (div_left_inj' hh.ne').mp
    exact hr'
  constructor
  · exact hφ'
  · apply (div_left_inj' hh.ne').mp
    exact hm'


/-- One threshold selected from two original reference points works for
every later axis point and future witness of the fixed pair. The localization
radius is chosen after the positive variation allowance. -/
theorem fixed_pair_axis_local_agreement_from_refs
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    {w₁ w₂ : ℝ} (href₁ : (0, w₁) ∈ U₁) (href₂ : (0, w₂) ∈ U₂) :
    ∃ εfinal : ℝ, 0 < εfinal ∧
      ∀ {a A V : ℝ}, (A, V) ∈ U₁ ∩ U₂ → 0 ≤ a → a < A →
        (∀ v, (a, v) ∈ U₁ ∩ U₂ →
          S₁.r a v = S₂.r a v ∧ S₁.phi a v = S₂.phi a v) →
      ∀ ε : ℝ, 0 < ε → ε ≤ εfinal →
        ∃ h : ℝ, 0 < h ∧ triangle a (a + h) ⊆ U₁ ∩ U₂ ∧
          ∀ u v, (u, v) ∈ triangle a (a + h) →
            S₁.r u v = S₂.r u v ∧
            S₁.phi u v = S₂.phi u v ∧
            S₁.m u v = S₂.m u v := by
  obtain ⟨P, hpackage⟩ :=
    exists_uniform_threshold_bounds_of_fixed_pair h₁ h₂ href₁ href₂
  obtain ⟨εfinal, hεfinal, hlocal⟩ := P.scaled_local_unique
  refine ⟨εfinal, hεfinal, ?_⟩
  intro a A V hp ha haA hdata ε hε hεle
  obtain ⟨h, hh, hT, hdata', _, _, _, _, hvar⟩ :=
    common_axis_variations_small h₁ h₂ hp ha haA hdata hε
  obtain ⟨hP, hvar₁, hvar₂⟩ := hpackage a h hh hT
  refine ⟨h, hh, hT, ?_⟩
  apply hlocal h₁ h₂ ha hh hT hdata' hP hvar₁ hvar₂ ε hε.le hεle
  intro u v huv S hS
  obtain ⟨ho₁, hi₁, ho₂, hi₂⟩ := hvar u v huv
  rcases hS with rfl | rfl
  · exact ⟨ho₁, hi₁⟩
  · exact ⟨ho₂, hi₂⟩

/-- A common future witness itself supplies original reference points,
so no extra reference-point hypothesis is needed for axis localization. -/
theorem fixed_pair_axis_local_agreement
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields} {a A V : ℝ}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hp : (A, V) ∈ U₁ ∩ U₂) (ha : 0 ≤ a) (haA : a < A)
    (hdata : ∀ v, (a, v) ∈ U₁ ∩ U₂ →
      S₁.r a v = S₂.r a v ∧ S₁.phi a v = S₂.phi a v) :
    ∃ εfinal : ℝ, 0 < εfinal ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εfinal →
        ∃ h : ℝ, 0 < h ∧ triangle a (a + h) ⊆ U₁ ∩ U₂ ∧
          ∀ u v, (u, v) ∈ triangle a (a + h) →
            S₁.r u v = S₂.r u v ∧
            S₁.phi u v = S₂.phi u v ∧
            S₁.m u v = S₂.m u v := by
  have hApos : 0 < A := lt_of_le_of_lt ha haA
  have hAV : A < V := (h₁.solution.development.wedge hp.1).2
  have hT₀ : triangle 0 A ⊆ U₁ ∩ U₂ :=
    common_triangle h₁.solution.development h₂.solution.development
      hp (by norm_num) le_rfl hAV.le
  have href : (0, A / 2) ∈ U₁ ∩ U₂ :=
    hT₀ ((mem_triangle).2 ⟨le_rfl, by linarith, by linarith⟩)
  obtain ⟨εfinal, hεfinal, hlocal⟩ :=
    fixed_pair_axis_local_agreement_from_refs h₁ h₂ href.1 href.2
  exact ⟨εfinal, hεfinal,
    fun ε hε hεle => hlocal hp ha haA hdata ε hε hεle⟩

end ChristodoulouBV.Uniqueness

end
