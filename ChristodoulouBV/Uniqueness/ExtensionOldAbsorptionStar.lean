module

public import ChristodoulouBV.Uniqueness.ExtensionOldAbsorption
public import ChristodoulouBV.Uniqueness.ExtensionIncomingWeighted

/-!
# The weighted bound (5.12) before `vStar`

Combining the conditional weighted absorption estimate with the incoming
bound `incoming_weighted_bound_before_star` proves (5.12) from the frozen
family, initial data, and tail hypotheses only.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- (5.12): on the whole compatible development above `u₀`, the weighted values `r^{1/2}|α′|` are bounded,
and their supremum is at most `D′/(1 - ε/ε₁)` with `ε₁ = (5 - 2√6)/3`. -/
theorem weightedAlphaPrime_bound_before_star
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε0 : 0 ≤ ε)
    (hε1 : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    BddAbove (weightedAlphaPrimeValuesBeforeStar u₀ vStar ((1 : ℝ) / 2) S) ∧
      weightedAlphaPrimeSupBeforeStar u₀ vStar ((1 : ℝ) / 2) S ≤
        incomingWeightedAlphaPrimeSup u₀ vStar ((1 : ℝ) / 2) S /
          (1 - ε / ((5 - 2 * Real.sqrt 6) / 3)) := by
  have hsqrt : 1 < Real.sqrt 6 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hη : ε < 1 := by linarith
  exact weightedAlphaPrime_bound_before_star_of_incoming_bddAbove hu₀ hα hfamily hε0 hε1 htail
    (incoming_weighted_bound_before_star hu₀.1 hu₀.2 hη (by norm_num) hα hfamily htail)

end ChristodoulouBV.Uniqueness

end
