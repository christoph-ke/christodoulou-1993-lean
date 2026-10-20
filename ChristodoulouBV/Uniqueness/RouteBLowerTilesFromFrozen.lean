module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesFromBaseJets
public import ChristodoulouBV.Uniqueness.RouteBLowerTilesExistence
public import ChristodoulouBV.Uniqueness.RouteBLowerCover
import Mathlib.Tactic

/-!
# A safe lower strip from the old family

The canonical terminal trace data and its full first jets instantiate the
constrained tile interface. Compact safe boxes then give a positive-height
relative C¹ strip with the prescribed initial gauge.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Frozen family and tail premises yield a safe lower seven-state strip
whose terminal edge is the old family's canonical trace. -/
theorem exists_routeB_safe_lower_strip_state
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
            C1Solution.stateRadius (Z (0, v)) = v / 2) := by
  obtain ⟨P, δ, hδ, hboxesP⟩ :=
    exists_uniform_terminal_safe_boxes_on_lower_base
      hu₀ ha haBar hBarStar hα hfamily hε1 htail
  obtain ⟨J⟩ := P.exists_routeBTerminalBaseJets
    ha haBar hBarStar hu₀ hα hfamily hε1 htail
  obtain ⟨D, hDalpha, hDbase⟩ :=
    J.exists_lowerCoverBaseData alpha₀ ha haBar hBarStar hL hα hfamily
  have hboxesD : ∀ t ∈ Icc 0 a,
      ∃ B : C1Solution.SafeRectangleBox,
        B.center = D.base t ∧ B.radius = δ := by
    intro t ht
    obtain ⟨B, hc, hr⟩ := hboxesP t ht
    exact ⟨B, hc.trans (hDbase t ht).symm, hr⟩
  obtain ⟨η, hη, hηL, Z, hZ, hsafe, hclassical, hbase, hinit, hradius⟩ :=
    D.exists_safe_lower_strip_state (b := vStar + L)
      ha hL (haBar.trans hBarStar)
      hboxesD
  refine ⟨P, η, hη, hηL, Z, hZ, hsafe,
    routeBFieldsC1On_rectangleStateFields hZ hsafe,
    hclassical, ?_, ?_, hradius⟩
  · intro t ht
    exact (hbase t ht).trans (hDbase t ht)
  · intro v hv
    simpa only [hDalpha] using hinit v hv

end ChristodoulouBV.Uniqueness

end
