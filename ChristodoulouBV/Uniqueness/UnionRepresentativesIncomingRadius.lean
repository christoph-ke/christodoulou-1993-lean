module

public import ChristodoulouBV.Uniqueness.UnionRepresentativesOutgoing

/-!
# Incoming radius primitive on a mixed terminal segment

The globally bounded incoming expansion provides the dominating density for
passing the radius primitive to a mixed terminal level.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The selected radius and incoming expansion satisfy the incoming radius
primitive on a segment whose upper endpoint belongs to the first source. -/
theorem first_source_radius_in_mixed_top
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) (hb : (b, v) ∈ U₁) :
    IntervalPrimitive
      (fun s => (gluedFields U₁ S₁ S₂).r s v)
      (fun s => (gluedFields U₁ S₁ S₂).nu s v) a b := by
  let G := gluedFields U₁ S₁ S₂
  have ha : (a, v) ∈ U₁ ∪ U₂ := hseg (by
    change a ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨⟨le_rfl, hab⟩, rfl⟩)
  have ha0 : 0 ≤ a := by
    rcases ha with ha₁ | ha₂
    · exact (h₁.solution.development.wedge ha₁).1
    · exact (h₂.solution.development.wedge ha₂).1
  have hbv : b < v := (h₁.solution.development.wedge hb).2
  have hstrip : ∀ᶠ t in 𝓝[<] v, inSeg t a b ⊆ U₁ := by
    filter_upwards [Ioo_mem_nhdsLT hbv] with t ht
    exact h₁.solution.development.in_seg_subset hb ha0 hab le_rfl ht.1 ht.2
  have hsource : ∀ᶠ t in 𝓝[<] v,
      IntervalPrimitive (fun s => S₁.r s t) (fun s => S₁.nu s t) a b :=
    hstrip.mono (fun t ht => h₁.solution.radius_in t a b hab ht)
  obtain ⟨N, hN⟩ := h₁.nu_bounded_below
  obtain ⟨c, hc, hlow⟩ := h₁.lam_bounded_below
  have hN0 : 0 ≤ N := by
    have hnu := h₁.nu_le_neg_lower hc hlow hb
    have hnuUpper := hN (b, v) hb
    linarith
  have hbound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ t in 𝓝[<] v, ∀ s ∈ Icc a b, |S₁.nu s t| ≤ C := by
    refine ⟨N, hN0, ?_⟩
    filter_upwards [hstrip] with t ht s hs
    have hsU : (s, t) ∈ U₁ := ht (by
      change s ∈ Icc a b ∧ t ∈ ({t} : Set ℝ)
      exact ⟨hs, rfl⟩)
    have hneg := h₁.nu_le_neg_lower hc hlow hsU
    rw [abs_of_nonpos (by linarith : S₁.nu s t ≤ 0)]
    exact hN (s, t) hsU
  have hLim (s : ℝ) (hs : s ∈ Icc a b) :=
    first_source_fields_tendsto_mixed_top h₁ h₂ hdata hab hseg hb hs
  obtain ⟨hTargetInt, hIntegralLimit⟩ :=
    intervalIntegrable_and_tendsto_integral_of_eventually_bounded
      hab (hsource.mono (fun _ ht => ht.1)) hbound
      (fun s hs => (hLim s hs).2.2.2.1)
  have hA := (hLim a ⟨le_rfl, hab⟩).1
  have hB := (hLim b ⟨hab, le_rfl⟩).1
  have hEqEv : ∀ᶠ t in 𝓝[<] v,
      S₁.r b t - S₁.r a t = ∫ s in a..b, S₁.nu s t :=
    hsource.mono (fun _ ht => ht.2)
  have hEq : G.r b v - G.r a v = ∫ s in a..b, G.nu s v := by
    have hleft := hB.sub hA
    have hright := hIntegralLimit.congr' (hEqEv.mono fun _ ht => ht.symm)
    exact tendsto_nhds_unique hleft hright
  exact ⟨hTargetInt, hEq⟩

end ChristodoulouBV.Uniqueness

end
