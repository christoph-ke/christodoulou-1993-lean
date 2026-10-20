module

public import ChristodoulouBV.Uniqueness.UnionEquationsIncomingMass

/-!
# Incoming mass equation on the union

The mixed terminal mass equation is symmetric in the two source solutions,
and therefore holds on every closed incoming segment of their union.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The incoming mass primitive on a mixed segment whose upper endpoint
belongs to the second source. -/
theorem second_source_mass_in_mixed_top
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) (hb : (b, v) ∈ U₂) :
    IntervalPrimitive (fun s => (gluedFields U₁ S₁ S₂).m s v)
      (fun s => (1 - 2 * (gluedFields U₁ S₁ S₂).m s v /
        (gluedFields U₁ S₁ S₂).r s v) *
        ((gluedFields U₁ S₁ S₂).zeta s v) ^ 2 /
        (2 * (gluedFields U₁ S₁ S₂).nu s v)) a b := by
  let G₁ := gluedFields U₁ S₁ S₂
  let G₂ := gluedFields U₂ S₂ S₁
  have hseg' : inSeg v a b ⊆ U₂ ∪ U₁ := by
    intro p hp
    exact (hseg hp).symm
  have hprime := first_source_mass_in_mixed_top h₂ h₁
    (swapped_initial_agreement hdata) hab hseg' hb
  have heq (s : ℝ) (hs : s ∈ Icc a b) :=
    gluedFields_swap_eq_on_union h₁ h₂ hdata
      (hseg (by
        change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
        exact ⟨hs, rfl⟩))
  have hm : EqOn (fun s => G₂.m s v) (fun s => G₁.m s v) (Icc a b) :=
    fun s hs => (heq s hs).2.2.1
  have hdens : ∀ᵐ s ∂volume, s ∈ Ioc a b →
      (1 - 2 * G₂.m s v / G₂.r s v) * (G₂.zeta s v) ^ 2 /
        (2 * G₂.nu s v) =
      (1 - 2 * G₁.m s v / G₁.r s v) * (G₁.zeta s v) ^ 2 /
        (2 * G₁.nu s v) := by
    apply Filter.Eventually.of_forall
    intro s hs
    obtain ⟨hr, hphi, hm, _, hnu, _, hbeta⟩ :=
      heq s ⟨hs.1.le, hs.2⟩
    simp only [Fields.zeta, G₁, G₂] at *
    rw [hr, hphi, hm, hnu, hbeta]
  exact IntervalPrimitive.congr_on_segment hab hprime hm hdens

/-- The incoming mass primitive holds on every closed incoming segment of
the union. -/
theorem gluedFields_mass_in
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) :
    IntervalPrimitive (fun s => (gluedFields U₁ S₁ S₂).m s v)
      (fun s => (1 - 2 * (gluedFields U₁ S₁ S₂).m s v /
        (gluedFields U₁ S₁ S₂).r s v) *
        ((gluedFields U₁ S₁ S₂).zeta s v) ^ 2 /
        (2 * (gluedFields U₁ S₁ S₂).nu s v)) a b := by
  have hb : (b, v) ∈ U₁ ∪ U₂ := hseg (by
    change b ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨⟨hab, le_rfl⟩, rfl⟩)
  rcases hb with hb₁ | hb₂
  · exact first_source_mass_in_mixed_top h₁ h₂ hdata hab hseg hb₁
  · exact second_source_mass_in_mixed_top h₁ h₂ hdata hab hseg hb₂

end ChristodoulouBV.Uniqueness

end
