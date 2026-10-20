module

public import ChristodoulouBV.Uniqueness.UnionBVOutgoing
public import ChristodoulouBV.ForMathlib.BoundedVariation.ACQuotient

/-!
# Absolute continuity and pointwise bounds on the union

Incoming scalar absolute continuity follows from the radius and scalar
radius primitives of the glued solution and positivity of the radius.
-/

@[expose] public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The glued scalar is absolutely continuous on every complete outgoing
segment of the union. -/
theorem glued_phi_ac_out
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    (u a b : ℝ) (hab : a ≤ b)
    (hseg : outSeg u a b ⊆ U₁ ∪ U₂) :
    AbsolutelyContinuousOnInterval ((gluedFields U₁ S₁ S₂).phi u) a b := by
  have ha : (u, a) ∈ U₁ ∪ U₂ := hseg (by
    change u ∈ ({u} : Set ℝ) ∧ a ∈ Icc a b
    exact ⟨rfl, ⟨le_rfl, hab⟩⟩)
  have hua : u < a := by
    rcases ha with ha₁ | ha₂
    · exact (h₁.solution.development.wedge ha₁).2
    · exact (h₂.solution.development.wedge ha₂).2
  have hb : (u, b) ∈ U₁ ∪ U₂ := hseg (by
    change u ∈ ({u} : Set ℝ) ∧ b ∈ Icc a b
    exact ⟨rfl, ⟨hab, le_rfl⟩⟩)
  rcases hb with hb₁ | hb₂
  · have hseg₁ := h₁.solution.development.out_seg_subset hb₁ hua hab le_rfl
    apply (h₁.item3_ac_out u a b hab hseg₁).congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact (gluedFields_eq_first (S₂ := S₂)
      (hseg₁ (by change u ∈ ({u} : Set ℝ) ∧ t ∈ Icc a b
                 exact ⟨rfl, ht⟩))).2.1.symm
  · have hseg₂ := h₂.solution.development.out_seg_subset hb₂ hua hab le_rfl
    apply (h₂.item3_ac_out u a b hab hseg₂).congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact (gluedFields_eq_second h₁ h₂ hdata
      (hseg₂ (by change u ∈ ({u} : Set ℝ) ∧ t ∈ Icc a b
                 exact ⟨rfl, ht⟩))).2.1.symm

/-- The glued scalar is absolutely continuous on every complete incoming
segment, including one assembled from two terminal source slices. -/
theorem glued_phi_ac_in
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    (v a b : ℝ) (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) :
    AbsolutelyContinuousOnInterval
      (fun u => (gluedFields U₁ S₁ S₂).phi u v) a b := by
  let G := gluedFields U₁ S₁ S₂
  have hsol := glued_isSolution h₁ h₂ hdata
  have hR := (hsol.radius_in_ac_ae hab hseg).1
  have hP := (hsol.scalar_radius_in_ac_ae hab hseg).1
  have hpos : ∀ u ∈ Icc a b, 0 < G.r u v := by
    intro u hu
    exact hsol.radius_pos (u, v) (hseg (by
      change u ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
      exact ⟨hu, rfl⟩))
  have hdiv := AbsolutelyContinuousOnInterval.div_of_pos hab hP hR hpos
  apply hdiv.congr
  intro u hu
  have huI : u ∈ Icc a b := by simpa only [uIcc_of_le hab] using hu
  change G.r u v * G.phi u v / G.r u v = G.phi u v
  exact mul_div_cancel_left₀ _ (ne_of_gt (hpos u huI))

/-- The selected incoming expansion has a finite global upper bound on
its negative. -/
theorem glued_nu_bounded_below
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w) :
    ∃ N : ℝ, ∀ p ∈ U₁ ∪ U₂,
      -(gluedFields U₁ S₁ S₂).nu p.1 p.2 ≤ N := by
  obtain ⟨N₁, hN₁⟩ := h₁.nu_bounded_below
  obtain ⟨N₂, hN₂⟩ := h₂.nu_bounded_below
  refine ⟨max N₁ N₂, ?_⟩
  intro p hp
  rcases hp with hp₁ | hp₂
  · rw [(gluedFields_eq_first (S₂ := S₂) hp₁).2.2.2.1]
    exact (hN₁ p hp₁).trans (le_max_left _ _)
  · rw [(gluedFields_eq_second h₁ h₂ hdata hp₂).2.2.2.1]
    exact (hN₂ p hp₂).trans (le_max_right _ _)

/-- The selected outgoing expansion has a strictly positive global lower
bound on the union. -/
theorem glued_lam_bounded_below
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ U₁ ∪ U₂,
      c ≤ (gluedFields U₁ S₁ S₂).lam p.1 p.2 := by
  obtain ⟨c₁, hc₁, hlow₁⟩ := h₁.lam_bounded_below
  obtain ⟨c₂, hc₂, hlow₂⟩ := h₂.lam_bounded_below
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, ?_⟩
  intro p hp
  rcases hp with hp₁ | hp₂
  · rw [(gluedFields_lam_alpha_eq_first (S₂ := S₂) hp₁).1]
    exact (min_le_left _ _).trans
      (source_lam_leftLim_ge_lower h₁ hlow₁ hp₁)
  · rw [(gluedFields_lam_alpha_eq_second h₁ h₂ hdata hp₂).1]
    exact (min_le_right _ _).trans
      (source_lam_leftLim_ge_lower h₂ hlow₂ hp₂)

end ChristodoulouBV.Uniqueness

end
