module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesEndpoint
import Mathlib.Tactic

/-!
# Frozen-premise lower physical strip

The lower rectangle state reconstructs seven physical fields, and both
their values and full first jets match the canonical old off-axis trace.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Frozen premises yield the C¹ classical lower physical strip, its gauge,
and full field matching on the common off-axis terminal edge. -/
theorem exists_routeB_lower_cover_fields
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε a vBar L : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hL : 0 < L)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε1 : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    ∃ P : OffAxisTerminalC1Packet a vBar vStar S,
      ∃ η : ℝ, 0 < η ∧ η < L ∧
        ∃ Z : ℝ × ℝ → C1Solution.RectangleState,
          let Kold := Goursat.rectangle 0 a vBar vStar
          let Knew := Goursat.rectangle 0 a vStar (vStar + η)
          ContDiffOn ℝ 1 Z Knew ∧
          (∀ p ∈ Knew, C1Solution.IsSafeRectangleState (Z p)) ∧
          RouteBFieldsC1On (rectangleStateFields Z) Knew ∧
          RouteBClassicalJetOn (vStar + η) Knew
            (rectangleStateFields Z) ∧
          (∀ t ∈ Icc 0 a,
            Z (t, vStar) = P.state.rectangleState (t, vStar)) ∧
          (∀ v ∈ Icc vStar (vStar + η),
            (Z (0, v)).1 = (1 / 2, alpha₀ v)) ∧
          (∀ v ∈ Icc vStar (vStar + η),
            C1Solution.stateRadius (Z (0, v)) = v / 2) ∧
          RouteBFieldsEqOn
            (rectangleStateFields P.state.rectangleState)
            (rectangleStateFields Z) (Kold ∩ Knew) ∧
          RouteBFieldsJetEqOn
            (rectangleStateFields P.state.rectangleState)
            (rectangleStateFields Z) Kold Knew := by
  obtain ⟨P, η, hη, hηL, Z, hZ, hsafe, hfieldsC1, hclassical,
    htrace, hinit, hradius, _⟩ := exists_routeB_lower_cover_state
      hu₀ ha haBar hBarStar hL hα hfamily hε1 htail
  obtain ⟨J⟩ := P.exists_routeBTerminalBaseJets
    ha haBar hBarStar hu₀ hα hfamily hε1 htail
  obtain ⟨c, hc, hfloor⟩ := exists_expansion_floor_before_star
    hu₀ hα hfamily hε1 htail
  have hTop : vStar + η < vStar + L := by linarith only [hηL]
  obtain ⟨hval, hjet⟩ := J.physical_fields_eq_lower_strip_on_top
    ha haBar hBarStar hc hη hTop hα hfamily hfloor
    Z hZ hsafe hclassical htrace hinit
  exact ⟨P, η, hη, hηL, Z, hZ, hsafe, hfieldsC1,
    hclassical.mono_endpoint hTop.le,
    htrace, hinit, hradius, hval, hjet⟩

end ChristodoulouBV.Uniqueness

end
