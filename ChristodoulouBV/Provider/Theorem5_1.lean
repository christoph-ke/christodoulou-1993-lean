module

public import ChristodoulouBV.Frozen.IsC1Solution
public import ChristodoulouBV.Frozen.OpenDevelopment
public import ChristodoulouBV.Frozen.DevelopmentWithInitialEdge
public import ChristodoulouBV.Uniqueness.RouteBAssemblyFinal

/-!
# Provider for Theorem 5.1

The universal constant is `ε₁ = (5 - 2√6)/3` (p. 1176). The extension is the
Route B assembly `Uniqueness.exists_routeB_extension`.
-/

public section

namespace ChristodoulouBV.Provider

/-- The printed constant `(5 - 2√6)/3` is positive. -/
theorem theorem5_1_eps_pos : 0 < (5 - 2 * Real.sqrt 6) / 3 := by
  have h6 : Real.sqrt 6 < 5 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith

/-- Theorem 5.1, with the exact frozen statement. -/
theorem theorem5_1 :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ (alpha₀ : ℝ → ℝ) (vStar : ℝ), 0 < vStar →
        ContDiffOn ℝ 1 alpha₀ (Set.Ici 0) →
        ∀ S : ℝ → Fields,
          (∀ v₀ ∈ Set.Ioo (0 : ℝ) vStar,
            IsC1Solution (developmentWithInitialEdge v₀) (S v₀) ∧
            (∀ v ∈ Set.Ioo (0 : ℝ) v₀,
              (S v₀).r 0 v = v / 2 ∧ (S v₀).alpha 0 v = alpha₀ v)) →
          (∃ u₀ ∈ Set.Ioo (0 : ℝ) vStar, ∃ η : ℝ, η < ε₁ ∧
            ∀ v₀ ∈ Set.Ioo (0 : ℝ) vStar,
              ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge v₀,
                2 * (S v₀).m p.1 p.2 / (S v₀).r p.1 p.2 ≤ η) →
          ∃ v₁ : ℝ, vStar < v₁ ∧ ∃ T : Fields,
            IsC1Solution (developmentWithInitialEdge v₁) T ∧
            (∀ v ∈ Set.Ioo (0 : ℝ) v₁,
              T.r 0 v = v / 2 ∧ T.alpha 0 v = alpha₀ v) := by
  refine ⟨(5 - 2 * Real.sqrt 6) / 3, theorem5_1_eps_pos, ?_⟩
  intro alpha₀ vStar _ hα S hfamily htail
  obtain ⟨u₀, hu₀, η, hη, hbound⟩ := htail
  exact Uniqueness.exists_routeB_extension hu₀ hα hfamily hη hbound

end ChristodoulouBV.Provider

end
