module

public import ChristodoulouBV.Uniqueness.UnionRepresentativesIncomingScalar

/-!
# Incoming geometric primitives on the union

Symmetry transfers the mixed terminal arguments to either source. Thus the
selected radius and scalar radius satisfy their incoming primitives on every
closed incoming segment in the union.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The incoming radius and scalar-radius primitives hold when the terminal
endpoint of a mixed segment belongs to the second source. -/
theorem second_source_radius_scalar_in_mixed_top
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) (hb : (b, v) ∈ U₂) :
    IntervalPrimitive
      (fun s => (gluedFields U₁ S₁ S₂).r s v)
      (fun s => (gluedFields U₁ S₁ S₂).nu s v) a b ∧
    IntervalPrimitive
      (fun s => (gluedFields U₁ S₁ S₂).r s v *
        (gluedFields U₁ S₁ S₂).phi s v)
      (fun s => (gluedFields U₁ S₁ S₂).beta s v) a b := by
  let G₁ := gluedFields U₁ S₁ S₂
  let G₂ := gluedFields U₂ S₂ S₁
  have hseg' : inSeg v a b ⊆ U₂ ∪ U₁ := by
    intro p hp
    exact (hseg hp).symm
  have hdata' := swapped_initial_agreement hdata
  have hprimeR := first_source_radius_in_mixed_top h₂ h₁ hdata' hab hseg' hb
  have hprimeP := first_source_scalar_radius_in_mixed_top h₂ h₁ hdata' hab hseg' hb
  have heq (s : ℝ) (hs : s ∈ Icc a b) :=
    gluedFields_swap_eq_on_union h₁ h₂ hdata
      (hseg (by
        change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
        exact ⟨hs, rfl⟩))
  have hr : EqOn (fun s => G₂.r s v) (fun s => G₁.r s v) (Icc a b) :=
    fun s hs => (heq s hs).1
  have hp : EqOn (fun s => G₂.r s v * G₂.phi s v)
      (fun s => G₁.r s v * G₁.phi s v) (Icc a b) := by
    intro s hs
    change G₂.r s v * G₂.phi s v = G₁.r s v * G₁.phi s v
    dsimp only [G₁, G₂]
    rw [(heq s hs).1, (heq s hs).2.1]
  have hnu : ∀ᵐ s ∂volume, s ∈ Ioc a b → G₂.nu s v = G₁.nu s v :=
    Filter.Eventually.of_forall fun s hs => (heq s ⟨hs.1.le, hs.2⟩).2.2.2.2.1
  have hbeta : ∀ᵐ s ∂volume, s ∈ Ioc a b → G₂.beta s v = G₁.beta s v :=
    Filter.Eventually.of_forall fun s hs => (heq s ⟨hs.1.le, hs.2⟩).2.2.2.2.2.2
  exact ⟨IntervalPrimitive.congr_on_segment hab hprimeR hr hnu,
    IntervalPrimitive.congr_on_segment hab hprimeP hp hbeta⟩

/-- Both incoming geometric primitives hold on every incoming segment of
the union, including mixed terminal segments. -/
theorem gluedFields_radius_scalar_in
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) :
    IntervalPrimitive
      (fun s => (gluedFields U₁ S₁ S₂).r s v)
      (fun s => (gluedFields U₁ S₁ S₂).nu s v) a b ∧
    IntervalPrimitive
      (fun s => (gluedFields U₁ S₁ S₂).r s v *
        (gluedFields U₁ S₁ S₂).phi s v)
      (fun s => (gluedFields U₁ S₁ S₂).beta s v) a b := by
  have hb : (b, v) ∈ U₁ ∪ U₂ := hseg (by
    change b ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨⟨hab, le_rfl⟩, rfl⟩)
  rcases hb with hb₁ | hb₂
  · exact ⟨first_source_radius_in_mixed_top h₁ h₂ hdata hab hseg hb₁,
      first_source_scalar_radius_in_mixed_top h₁ h₂ hdata hab hseg hb₁⟩
  · exact second_source_radius_scalar_in_mixed_top h₁ h₂ hdata hab hseg hb₂

end ChristodoulouBV.Uniqueness

end
