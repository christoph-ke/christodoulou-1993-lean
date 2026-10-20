module

public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Finite partition gluing for variation

The source supplying a finite ordered partition may depend on the partition.
This is useful when two interval-like domains have different included top
points, so neither source contains the entire union.
-/

public section

open Set

namespace eVariationOn

/-- If every finite ordered partition of `s` agrees with one source on its
partition points, its variation is bounded by the larger source variation. -/
theorem le_max_of_finite_partition_source
    {α M : Type*} [LinearOrder α] [PseudoEMetricSpace M]
    {f f₁ f₂ : α → M} {s s₁ s₂ : Set α}
    (hsource : ∀ n (u : ℕ → α), Monotone u → (∀ i, u i ∈ s) →
      (∀ i ≤ n, u i ∈ s₁ ∧ f (u i) = f₁ (u i)) ∨
      (∀ i ≤ n, u i ∈ s₂ ∧ f (u i) = f₂ (u i))) :
    eVariationOn f s ≤ max (eVariationOn f₁ s₁) (eVariationOn f₂ s₂) := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  rcases hsource n u hu hus with h₁ | h₂
  · have heq :
        (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) =
          ∑ i ∈ Finset.range n, edist (f₁ (u (i + 1))) (f₁ (u i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      rw [(h₁ (i + 1) (Nat.succ_le_of_lt hin)).2,
        (h₁ i (Nat.le_of_lt hin)).2]
    rw [heq]
    exact (eVariationOn.sum_le_of_monotoneOn_Iic (hu.monotoneOn _)
      (fun i hi => (h₁ i hi).1)).trans (le_max_left _ _)
  · have heq :
        (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) =
          ∑ i ∈ Finset.range n, edist (f₂ (u (i + 1))) (f₂ (u i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      rw [(h₂ (i + 1) (Nat.succ_le_of_lt hin)).2,
        (h₂ i (Nat.le_of_lt hin)).2]
    rw [heq]
    exact (eVariationOn.sum_le_of_monotoneOn_Iic (hu.monotoneOn _)
      (fun i hi => (h₂ i hi).1)).trans (le_max_right _ _)

end eVariationOn

end
