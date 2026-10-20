module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesTopSeam
import Mathlib.Tactic

/-!
# Frozen-premise lower cover with a full terminal seven-state seam

The finite safe tile march produces a classical C¹ lower strip. Its terminal
state and full seven-state first jets coincide with the old off-axis base.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Frozen family and tail premises provide a positive-height safe lower
strip, the initial gauge, and the complete terminal seven-state seam. -/
theorem exists_routeB_lower_cover_state
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
          ContDiffOn ℝ 1 Z
            (Goursat.rectangle 0 a vStar (vStar + η)) ∧
          (∀ p ∈ Goursat.rectangle 0 a vStar (vStar + η),
            C1Solution.IsSafeRectangleState (Z p)) ∧
          RouteBFieldsC1On (rectangleStateFields Z)
            (Goursat.rectangle 0 a vStar (vStar + η)) ∧
          RouteBClassicalJetOn (vStar + L)
            (Goursat.rectangle 0 a vStar (vStar + η))
            (rectangleStateFields Z) ∧
          (∀ t ∈ Icc 0 a,
            Z (t, vStar) = P.state.rectangleState (t, vStar)) ∧
          (∀ v ∈ Icc vStar (vStar + η),
            (Z (0, v)).1 = (1 / 2, alpha₀ v)) ∧
          (∀ v ∈ Icc vStar (vStar + η),
            C1Solution.stateRadius (Z (0, v)) = v / 2) ∧
          (∀ t ∈ Icc 0 a,
            fderivWithin ℝ (fun p => (P.state.rectangleState p).1)
              (Goursat.rectangle 0 a vBar vStar) (t, vStar) =
              fderivWithin ℝ (fun p => (Z p).1)
                (Goursat.rectangle 0 a vStar (vStar + η)) (t, vStar) ∧
            fderivWithin ℝ (fun p => (P.state.rectangleState p).2)
              (Goursat.rectangle 0 a vBar vStar) (t, vStar) =
              fderivWithin ℝ (fun p => (Z p).2)
                (Goursat.rectangle 0 a vStar (vStar + η)) (t, vStar)) := by
  obtain ⟨P, η, hη, hηL, Z, hZ, hsafe, hfieldsC1, hclassical,
    htrace, hinit, hradius⟩ := exists_routeB_safe_lower_strip_state
      hu₀ ha haBar hBarStar hL hα hfamily hε1 htail
  obtain ⟨J⟩ := P.exists_routeBTerminalBaseJets
    ha haBar hBarStar hu₀ hα hfamily hε1 htail
  obtain ⟨c, hc, hfloor⟩ := exists_expansion_floor_before_star
    hu₀ hα hfamily hε1 htail
  have hTop : vStar + η < vStar + L := by linarith only [hηL]
  have hjet := J.full_jets_eq_lower_strip_on_top ha haBar hBarStar
    hc hη hTop hα hfamily hfloor Z hZ hsafe hclassical htrace hinit
  exact ⟨P, η, hη, hηL, Z, hZ, hsafe, hfieldsC1,
    hclassical, htrace, hinit, hradius, hjet⟩

end ChristodoulouBV.Uniqueness

end
