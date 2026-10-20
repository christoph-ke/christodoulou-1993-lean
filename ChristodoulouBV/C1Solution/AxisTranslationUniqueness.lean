module

public import ChristodoulouBV.C1Solution.AxisTranslationFrozen
public import ChristodoulouBV.C1Solution.UniquenessTheorem
import Mathlib.Tactic

/-!
# Uniqueness across a translated axis corner

The frozen initial-edge uniqueness theorem is stated here in the original
coordinates of two solutions translated by the same incoming-edge parameter.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

open ChristodoulouBV.Uniqueness

/-- Translated frozen C¹ solutions with equal radius and scalar trace at
`u = a` agree in every field on their common shifted development. -/
theorem shifted_c1_solution_unique_on_common_development
    {a c₁ c₂ : ℝ} {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge (c₁ - a))
      (rescaledFields S₁ a 1))
    (H₂ : IsC1Solution (developmentWithInitialEdge (c₂ - a))
      (rescaledFields S₂ a 1))
    (hdata : ∀ w, a < w → w < min c₁ c₂ →
      S₁.r a w = S₂.r a w ∧ S₁.phi a w = S₂.phi a w)
    {u v : ℝ} (hau : a ≤ u) (huv : u < v) (hvc : v < min c₁ c₂) :
    S₁.r u v = S₂.r u v ∧ S₁.phi u v = S₂.phi u v ∧
    S₁.m u v = S₂.m u v ∧ S₁.lam u v = S₂.lam u v ∧
    S₁.nu u v = S₂.nu u v ∧ S₁.alpha u v = S₂.alpha u v ∧
    S₁.beta u v = S₂.beta u v ∧ S₁.theta u v = S₂.theta u v ∧
    S₁.zeta u v = S₂.zeta u v := by
  have hdata' : ∀ w, (0, w) ∈
      developmentWithInitialEdge (c₁ - a) ∩
        developmentWithInitialEdge (c₂ - a) →
      (rescaledFields S₁ a 1).r 0 w = (rescaledFields S₂ a 1).r 0 w ∧
      (rescaledFields S₁ a 1).phi 0 w = (rescaledFields S₂ a 1).phi 0 w := by
    intro w hw
    have hwpos : 0 < w := hw.1.2.1
    have hw₁ : w < c₁ - a := hw.1.2.2
    have hw₂ : w < c₂ - a := hw.2.2.2
    have h := hdata (a + w) (by linarith)
      (lt_min (by linarith) (by linarith))
    simpa only [rescaledFields, affineCoordinate, one_mul, add_zero,
      div_one] using h
  have hp₁ : (u - a, v - a) ∈
      developmentWithInitialEdge (c₁ - a) := by
    change 0 ≤ u - a ∧ u - a < v - a ∧ v - a < c₁ - a
    have hv₁ : v < c₁ := lt_of_lt_of_le hvc (min_le_left _ _)
    exact ⟨by linarith, by linarith, by linarith⟩
  have hp₂ : (u - a, v - a) ∈
      developmentWithInitialEdge (c₂ - a) := by
    change 0 ≤ u - a ∧ u - a < v - a ∧ v - a < c₂ - a
    have hv₂ : v < c₂ := lt_of_lt_of_le hvc (min_le_right _ _)
    exact ⟨by linarith, by linarith, by linarith⟩
  have heq := c1_solution_unique_on_common_development H₁ H₂
    hdata' hp₁ hp₂
  simpa [rescaledFields, affineCoordinate, Fields.theta, Fields.zeta] using heq

/-- A new classical axis triangle and an old frozen initial-edge solution
agree on their overlap when their radius and scalar data agree at `u = a`. -/
theorem classical_axis_solution_eq_old_on_overlap
    {a b c d : ℝ} {T S : Fields}
    (HT : AxisClassicalSolution a d T) (had : a < d)
    (HS : IsC1Solution (developmentWithInitialEdge b) S)
    (ha : 0 ≤ a) (hcb : c ≤ b)
    (hdata : ∀ w, a < w → w < min d c →
      T.r a w = S.r a w ∧ T.phi a w = S.phi a w)
    {u v : ℝ} (hau : a ≤ u) (huv : u < v) (hvc : v < min d c) :
    T.r u v = S.r u v ∧ T.phi u v = S.phi u v ∧
    T.m u v = S.m u v ∧ T.lam u v = S.lam u v ∧
    T.nu u v = S.nu u v ∧ T.alpha u v = S.alpha u v ∧
    T.beta u v = S.beta u v ∧ T.theta u v = S.theta u v ∧
    T.zeta u v = S.zeta u v := by
  exact shifted_c1_solution_unique_on_common_development
    (HT.shift_isC1Solution had)
    (isC1Solution_restrict_and_shift HS ha hcb)
    hdata hau huv hvc

end ChristodoulouBV.C1Solution

end
