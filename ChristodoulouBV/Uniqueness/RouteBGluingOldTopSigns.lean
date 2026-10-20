module

public import ChristodoulouBV.Uniqueness.RouteBGluingOldTerminal
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceFamilyExpansion
import ChristodoulouBV.C1Solution.Extraction
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# Physical signs on the closed old terminal rectangle

The terminal traces carry positive radius, expansion and mass-gap floors.
The uniform finite-family expansion floor makes the incoming expansion
strictly negative also at the terminal edge.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- All four physical signs hold on the closed terminal rectangle. -/
theorem OffAxisTerminalC1Packet.terminalFields_signs
    {alpha₀ : ℝ → ℝ} {a vBar vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ d ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge d) (S d) ∧
      (∀ v ∈ Ioo (0 : ℝ) d,
        (S d).r 0 v = v / 2 ∧ (S d).alpha 0 v = alpha₀ v))
    (hε : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ d ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge d,
        2 * (S d).m p.1 p.2 / (S d).r p.1 p.2 ≤ ε) :
    ∀ p ∈ routeBLowerRegion a vBar vStar,
      0 < P.terminalFields.r p.1 p.2 ∧
      0 < P.terminalFields.lam p.1 p.2 ∧
      P.terminalFields.nu p.1 p.2 < 0 ∧
      0 < 1 - 2 * P.terminalFields.m p.1 p.2 /
        P.terminalFields.r p.1 p.2 := by
  obtain ⟨c, hc, hfloor⟩ :=
    exists_expansion_floor_before_star hu₀ hα hfamily hε htail
  intro p hp
  have hvalues := P.state.floors p.1 hp.1 p.2 hp.2
  have hnu : P.state.nu p < 0 := by
    rcases lt_or_eq_of_le hp.2.2 with hvStar | hvStar
    · let d := (p.2 + vStar) / 2
      let B := (p.2 + d) / 2
      have hvD : p.2 < d := by dsimp [d]; linarith only [hvStar]
      have hdStar : d < vStar := by dsimp [d]; linarith only [hvStar]
      have hd : d ∈ Ioo (0 : ℝ) vStar :=
        ⟨(ha.trans (haBar.trans_le hp.2.1)).trans hvD, hdStar⟩
      have hvB : p.2 ≤ B := by dsimp [B]; linarith only [hvD]
      have hBd : B < d := by dsimp [B]; linarith only [hvD]
      have hB : 0 < B :=
        (ha.trans (haBar.trans_le hp.2.1)).trans_le hvB
      have hpB : p ∈ closedCoordTriangle 0 B :=
        ⟨hp.1.1, hp.1.2.trans (haBar.le.trans hp.2.1), hvB⟩
      have hmatch := (P.state.match_old d hd p.1 hp.1 p.2
        ⟨hp.2.1, hvD⟩).2.2.2.1
      rw [hmatch]
      exact C1Solution.nu_neg_closed_triangle hB hBd (hfamily d hd).1 hpB
    · have hpoint : p = (p.1, vStar) := Prod.ext rfl hvStar
      rw [hpoint]
      exact (P.state.nu_le_neg_floor ha haBar hBarStar hc hfamily hfloor
        hp.1).trans_lt (by linarith only [hc])
  exact ⟨P.state.radius_pos.trans_le hvalues.1,
    P.state.expansion_pos.trans_le hvalues.2.1,
    hnu, P.state.gap_pos.trans_le hvalues.2.2⟩

end ChristodoulouBV.Uniqueness

end
