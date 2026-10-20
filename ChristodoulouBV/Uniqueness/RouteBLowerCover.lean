module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverSafety
public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseOutgoing
public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseIncomingOutgoingC1
public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseMass
public import ChristodoulouBV.Uniqueness.RouteBLowerCoverTransverseCoefficients
public import ChristodoulouBV.Uniqueness.RouteBLowerCoverVerticalODE
public import ChristodoulouBV.Uniqueness.RouteBLowerCoverVerticalODEInteriorParameter
import ChristodoulouBV.Uniqueness.ExtensionStarTraceFamilyExpansion

/-!
# Local safety input for the Route B lower cover

This file establishes safe seven-state centers along the canonical terminal
base from the frozen family and tail premises. It also exports the algebraic
mass jet and the outgoing transport tools for the transverse jets. The
transverse traces and finite rectangle cover require further work.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- For a fixed positive lower-base endpoint, the canonical terminal trace data
have safe state boxes of one common positive radius all along its top edge.
The box centers follow the canonical trace. -/
theorem exists_uniform_terminal_safe_boxes_on_lower_base
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε a vBar : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
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
      ∃ δ : ℝ, 0 < δ ∧
        ∀ u ∈ Icc 0 a,
          ∃ B : C1Solution.SafeRectangleBox,
            B.center = P.state.rectangleState (u, vStar) ∧
              B.radius = δ := by
  obtain ⟨P⟩ := exists_offAxisTerminalC1Packet
    hu₀ ha haBar hBarStar hα hfamily hε1 htail
  obtain ⟨c, hc, hfloor⟩ :=
    exists_expansion_floor_before_star hu₀ hα hfamily hε1 htail
  exact ⟨P, P.state.exists_uniform_safeRectangleBox_radius
    ha haBar hBarStar hc hfamily hfloor⟩

end ChristodoulouBV.Uniqueness

end
