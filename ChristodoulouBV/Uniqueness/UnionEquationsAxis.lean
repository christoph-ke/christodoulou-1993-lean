module

public import ChristodoulouBV.Uniqueness.UnionEquationsSigns

/-!
# Regular-axis limits on the union

A right-axis filter restricted to the union splits into the supremum of its
two source filters. Each source limit transfers along its slice, including
when that slice is empty.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- A source axis limit is valid at every axis parameter: when the source
does not approach that parameter, the restricted filter is bottom. -/
theorem source_axis_tendsto_or_empty
    {U : Set (ℝ × ℝ)} {f : ℝ → ℝ → ℝ}
    (hdev : IsDomainOfDevelopment U)
    (hlim : ∀ a ∈ adjacentAxis U,
      Tendsto (f a)
        (𝓝[>] a ⊓ 𝓟 {t | (a, t) ∈ U}) (𝓝 (0 : ℝ)))
    (a : ℝ) :
    Tendsto (f a)
      (𝓝[>] a ⊓ 𝓟 {t | (a, t) ∈ U}) (𝓝 (0 : ℝ)) := by
  by_cases ha : a ∈ adjacentAxis U
  · exact hlim a ha
  · have hempty : {t : ℝ | (a, t) ∈ U} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun ht => ha (hdev.axis_mem ht)
    simp [hempty]

/-- Two source axis limits glue whenever the values agree with a selected
function on their respective slices. -/
theorem tendsto_union_axis_of_source_limits
    {U₁ U₂ : Set (ℝ × ℝ)} {f₁ f₂ g : ℝ → ℝ → ℝ}
    (hdev₁ : IsDomainOfDevelopment U₁)
    (hdev₂ : IsDomainOfDevelopment U₂)
    (hlim₁ : ∀ a ∈ adjacentAxis U₁,
      Tendsto (f₁ a)
        (𝓝[>] a ⊓ 𝓟 {t | (a, t) ∈ U₁}) (𝓝 (0 : ℝ)))
    (hlim₂ : ∀ a ∈ adjacentAxis U₂,
      Tendsto (f₂ a)
        (𝓝[>] a ⊓ 𝓟 {t | (a, t) ∈ U₂}) (𝓝 (0 : ℝ)))
    (heq₁ : ∀ p ∈ U₁, g p.1 p.2 = f₁ p.1 p.2)
    (heq₂ : ∀ p ∈ U₂, g p.1 p.2 = f₂ p.1 p.2)
    (a : ℝ) :
    Tendsto (g a)
      (𝓝[>] a ⊓ 𝓟 {t | (a, t) ∈ U₁ ∪ U₂}) (𝓝 (0 : ℝ)) := by
  let A₁ : Set ℝ := {t | (a, t) ∈ U₁}
  let A₂ : Set ℝ := {t | (a, t) ∈ U₂}
  have h₁ := source_axis_tendsto_or_empty hdev₁ hlim₁ a
  have h₂ := source_axis_tendsto_or_empty hdev₂ hlim₂ a
  have heqEv₁ : ∀ᶠ t in 𝓝[>] a ⊓ 𝓟 A₁, f₁ a t = g a t := by
    filter_upwards [show A₁ ∈ 𝓝[>] a ⊓ 𝓟 A₁ from
      le_principal_iff.mp inf_le_right] with t ht
    exact (heq₁ (a, t) ht).symm
  have heqEv₂ : ∀ᶠ t in 𝓝[>] a ⊓ 𝓟 A₂, f₂ a t = g a t := by
    filter_upwards [show A₂ ∈ 𝓝[>] a ⊓ 𝓟 A₂ from
      le_principal_iff.mp inf_le_right] with t ht
    exact (heq₂ (a, t) ht).symm
  have h₁' : Tendsto (g a) (𝓝[>] a ⊓ 𝓟 A₁) (𝓝 (0 : ℝ)) :=
    h₁.congr' heqEv₁
  have h₂' : Tendsto (g a) (𝓝[>] a ⊓ 𝓟 A₂) (𝓝 (0 : ℝ)) :=
    h₂.congr' heqEv₂
  have hFilt : (𝓝[>] a ⊓ 𝓟 A₁) ⊔ (𝓝[>] a ⊓ 𝓟 A₂) =
      𝓝[>] a ⊓ 𝓟 {t | (a, t) ∈ U₁ ∪ U₂} := by
    rw [← inf_sup_left, Filter.sup_principal]
    congr 1
  rw [← hFilt]
  exact Filter.tendsto_sup.mpr ⟨h₁', h₂'⟩

/-- The selected radius and mass both vanish at every adjacent axis point
of the union. -/
theorem gluedFields_radius_mass_axis
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    (a : ℝ) :
    Tendsto ((gluedFields U₁ S₁ S₂).r a)
      (𝓝[>] a ⊓ 𝓟 {t | (a, t) ∈ U₁ ∪ U₂}) (𝓝 (0 : ℝ)) ∧
    Tendsto ((gluedFields U₁ S₁ S₂).m a)
      (𝓝[>] a ⊓ 𝓟 {t | (a, t) ∈ U₁ ∪ U₂}) (𝓝 (0 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · apply tendsto_union_axis_of_source_limits h₁.solution.development
      h₂.solution.development h₁.solution.radius_axis h₂.solution.radius_axis
      (fun p hp => (gluedFields_eq_first (S₁ := S₁) (S₂ := S₂) hp).1)
      (fun p hp => (gluedFields_eq_second h₁ h₂ hdata hp).1) a
  · apply tendsto_union_axis_of_source_limits h₁.solution.development
      h₂.solution.development h₁.solution.mass_axis h₂.solution.mass_axis
      (fun p hp => (gluedFields_eq_first (S₁ := S₁) (S₂ := S₂) hp).2.2.1)
      (fun p hp => (gluedFields_eq_second h₁ h₂ hdata hp).2.2.1) a

end ChristodoulouBV.Uniqueness

end
