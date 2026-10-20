module

public import ChristodoulouBV.Uniqueness.UnionRepresentatives

/-!
# Canonical representatives on mixed incoming terminal segments

A source containing the upper incoming endpoint `(b,v)` contains every point
of the segment strictly below `v`. The common left-trace convention therefore
selects that source's traces along the whole terminal segment, even where the
source does not itself contain `(s,v)`.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- If the first source contains the upper endpoint of an incoming union
segment, its left traces give the canonical `λ, α` at every segment point. -/
theorem common_lam_alpha_on_incoming_segment_of_first_top
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b : ℝ} (_hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) (hb : (b, v) ∈ U₁) :
    ∀ s ∈ Icc a b,
      commonLam U₁ S₁ S₂ s v = (S₁.lam s).leftLim v ∧
      commonAlpha U₁ S₁ S₂ s v = (S₁.alpha s).leftLim v := by
  intro s hs
  have hsvp : (s, v) ∈ U₁ ∪ U₂ := hseg (by simp [inSeg, hs])
  by_cases hs₁ : (s, v) ∈ U₁
  · exact common_lam_alpha_eq_first hs₁
  · have hs₂ : (s, v) ∈ U₂ := hsvp.resolve_left hs₁
    have hs0 : 0 ≤ s := (h₂.solution.development.wedge hs₂).1
    have hsv : s < v := (h₂.solution.development.wedge hs₂).2
    have hcommon : ∀ t ∈ Ioo s v, (s, t) ∈ U₁ ∩ U₂ := by
      intro t ht
      exact ⟨h₁.solution.development.past_mem hb hs0 hs.2 ht.1 ht.2,
        h₂.solution.development.outgoing_mem hs₂ ht.1 ht.2.le⟩
    obtain ⟨hLam, hAlpha⟩ :=
      source_lam_alpha_leftLim_eq_of_punctured_overlap h₁ h₂ hdata hsv hcommon
    classical
    simp only [commonLam, commonAlpha, hs₁, ↓reduceIte]
    exact ⟨hLam.symm, hAlpha.symm⟩

/-- The symmetric mixed terminal case, when the second source contains the
upper incoming endpoint. -/
theorem common_lam_alpha_on_incoming_segment_of_second_top
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b : ℝ} (_hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) (hb : (b, v) ∈ U₂) :
    ∀ s ∈ Icc a b,
      commonLam U₁ S₁ S₂ s v = (S₂.lam s).leftLim v ∧
      commonAlpha U₁ S₁ S₂ s v = (S₂.alpha s).leftLim v := by
  intro s hs
  have hsvp : (s, v) ∈ U₁ ∪ U₂ := hseg (by simp [inSeg, hs])
  classical
  by_cases hs₁ : (s, v) ∈ U₁
  · have hs0 : 0 ≤ s := (h₁.solution.development.wedge hs₁).1
    have hsv : s < v := (h₁.solution.development.wedge hs₁).2
    have hcommon : ∀ t ∈ Ioo s v, (s, t) ∈ U₁ ∩ U₂ := by
      intro t ht
      exact ⟨h₁.solution.development.outgoing_mem hs₁ ht.1 ht.2.le,
        h₂.solution.development.past_mem hb hs0 hs.2 ht.1 ht.2⟩
    obtain ⟨hLam, hAlpha⟩ :=
      source_lam_alpha_leftLim_eq_of_punctured_overlap h₁ h₂ hdata hsv hcommon
    simpa only [commonLam, commonAlpha, hs₁, ↓reduceIte] using
      (show (S₁.lam s).leftLim v = (S₂.lam s).leftLim v ∧
        (S₁.alpha s).leftLim v = (S₂.alpha s).leftLim v from ⟨hLam, hAlpha⟩)
  · simp [commonLam, commonAlpha, hs₁]

/-- On every complete outgoing segment in the union, the common radius density
is the left trace of whichever source contains the endpoint. Its variation
therefore has no new terminal cost. -/
theorem commonLam_variation_outgoing_le_source
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {u v : ℝ} (hp : (u, v) ∈ U₁ ∪ U₂) :
    eVariationOn (fun t => commonLam U₁ S₁ S₂ u t) (Ioc u v) ≤
      max (eVariationOn (S₁.lam u) {t | (u, t) ∈ U₁})
        (eVariationOn (S₂.lam u) {t | (u, t) ∈ U₂}) := by
  classical
  rcases hp with hp₁ | hp₂
  · calc
      eVariationOn (fun t => commonLam U₁ S₁ S₂ u t) (Ioc u v) ≤
          eVariationOn (S₁.lam u) {t | (u, t) ∈ U₁} := by
            have hEq : EqOn (fun t => commonLam U₁ S₁ S₂ u t)
                (S₁.lam u).leftLim (Ioc u v) := by
              intro t ht
              exact (common_lam_alpha_eq_first
                (h₁.solution.development.outgoing_mem hp₁ ht.1 ht.2)).1
            calc
              eVariationOn (fun t => commonLam U₁ S₁ S₂ u t) (Ioc u v) =
                  eVariationOn (S₁.lam u).leftLim (Ioc u v) :=
                    eVariationOn.eq_of_eqOn hEq
              _ ≤ _ := source_lam_leftLim_variation_outgoing_le h₁ hp₁
      _ ≤ _ := le_max_left _ _
  · calc
      eVariationOn (fun t => commonLam U₁ S₁ S₂ u t) (Ioc u v) ≤
          eVariationOn (S₂.lam u) {t | (u, t) ∈ U₂} := by
            have hEq : EqOn (fun t => commonLam U₁ S₁ S₂ u t)
                (S₂.lam u).leftLim (Ioc u v) := by
              intro t ht
              exact (common_lam_alpha_eq_second h₁ h₂ hdata
                (h₂.solution.development.outgoing_mem hp₂ ht.1 ht.2)).1
            calc
              eVariationOn (fun t => commonLam U₁ S₁ S₂ u t) (Ioc u v) =
                  eVariationOn (S₂.lam u).leftLim (Ioc u v) :=
                    eVariationOn.eq_of_eqOn hEq
              _ ≤ _ := source_lam_leftLim_variation_outgoing_le h₂ hp₂
      _ ≤ _ := le_max_right _ _

/-- The scalar-radius density admits the same zero-cost outgoing endpoint
estimate on the union. -/
theorem commonAlpha_variation_outgoing_le_source
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {u v : ℝ} (hp : (u, v) ∈ U₁ ∪ U₂) :
    eVariationOn (fun t => commonAlpha U₁ S₁ S₂ u t) (Ioc u v) ≤
      max (eVariationOn (S₁.alpha u) {t | (u, t) ∈ U₁})
        (eVariationOn (S₂.alpha u) {t | (u, t) ∈ U₂}) := by
  classical
  rcases hp with hp₁ | hp₂
  · calc
      eVariationOn (fun t => commonAlpha U₁ S₁ S₂ u t) (Ioc u v) ≤
          eVariationOn (S₁.alpha u) {t | (u, t) ∈ U₁} := by
            have hEq : EqOn (fun t => commonAlpha U₁ S₁ S₂ u t)
                (S₁.alpha u).leftLim (Ioc u v) := by
              intro t ht
              exact (common_lam_alpha_eq_first
                (h₁.solution.development.outgoing_mem hp₁ ht.1 ht.2)).2
            calc
              eVariationOn (fun t => commonAlpha U₁ S₁ S₂ u t) (Ioc u v) =
                  eVariationOn (S₁.alpha u).leftLim (Ioc u v) :=
                    eVariationOn.eq_of_eqOn hEq
              _ ≤ _ := source_alpha_leftLim_variation_outgoing_le h₁ hp₁
      _ ≤ _ := le_max_left _ _
  · calc
      eVariationOn (fun t => commonAlpha U₁ S₁ S₂ u t) (Ioc u v) ≤
          eVariationOn (S₂.alpha u) {t | (u, t) ∈ U₂} := by
            have hEq : EqOn (fun t => commonAlpha U₁ S₁ S₂ u t)
                (S₂.alpha u).leftLim (Ioc u v) := by
              intro t ht
              exact (common_lam_alpha_eq_second h₁ h₂ hdata
                (h₂.solution.development.outgoing_mem hp₂ ht.1 ht.2)).2
            calc
              eVariationOn (fun t => commonAlpha U₁ S₁ S₂ u t) (Ioc u v) =
                  eVariationOn (S₂.alpha u).leftLim (Ioc u v) :=
                    eVariationOn.eq_of_eqOn hEq
              _ ≤ _ := source_alpha_leftLim_variation_outgoing_le h₂ hp₂
      _ ≤ _ := le_max_right _ _

end ChristodoulouBV.Uniqueness

end
