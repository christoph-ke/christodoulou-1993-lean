module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesTerminalOutgoing
public import ChristodoulouBV.Uniqueness.RouteBLowerTilesLocalJet
import Mathlib.Tactic

/-!
# Incoming transport on the terminal base

The old family's full lambda and alpha jets give the two incoming
characteristic equations needed by every lower tile.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

private theorem grav_coefficient_identity
    {r m lam nu : ℝ} (hr : 0 < r)
    (hgap : 0 < 1 - 2 * m / r) :
    lam * (nu * ((2 * m / r) / ((1 - 2 * m / r) * r))) =
      2 * m * lam * nu / (r * (r - 2 * m)) := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hgapne : 1 - 2 * m / r ≠ 0 := ne_of_gt hgap
  have hmass : r - 2 * m ≠ 0 := by
    intro heq
    have hident : (1 - 2 * m / r) * r = r - 2 * m := by
      field_simp [hrne]
    have hz : (1 - 2 * m / r) * r = 0 := hident.trans heq
    exact (mul_ne_zero hgapne hrne) hz
  field_simp [hrne, hgapne, hmass]

/-- The canonical terminal pair solves the incoming semilinear equation. -/
theorem RouteBTerminalBaseJets.incoming_deriv
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    {P : OffAxisTerminalC1Packet a vBar vStar S}
    (J : RouteBTerminalBaseJets P)
    (hBarStar : vBar ≤ vStar)
    {u : ℝ} (hu : u ∈ Icc 0 a) :
    HasDerivWithinAt
      (fun t => (P.state.rectangleState (t, vStar)).1)
      (C1Solution.rectangleF (P.state.rectangleState (u, vStar)))
      (Icc 0 a) u := by
  let p : ℝ × ℝ := (u, vStar)
  have hfloor := P.state.floors u hu vStar ⟨hBarStar, le_rfl⟩
  have hr : 0 < P.state.r p := P.state.radius_pos.trans_le hfloor.1
  have hgap : 0 < P.state.massGap p :=
    P.state.gap_pos.trans_le hfloor.2.2
  have hgrav : P.state.lam p * P.state.lambdaVCoefficient p =
      C1Solution.stateGrav (P.state.rectangleState p) := by
    change P.state.lam p *
        (P.state.nu p *
          ((2 * P.state.m p / P.state.r p) /
            ((1 - 2 * P.state.m p / P.state.r p) * P.state.r p))) =
      2 * P.state.m p * P.state.lam p * P.state.nu p /
        (P.state.r p * (P.state.r p - 2 * P.state.m p))
    exact grav_coefficient_identity hr hgap
  have hphi : P.state.phi p =
      C1Solution.statePhi (P.state.rectangleState p) := by
    change P.state.phi p =
      P.state.r p * P.state.phi p / P.state.r p
    field_simp [ne_of_gt hr]
  have hLam := hasDerivWithinAt_terminal_horizontal_slice hBarStar
    J.lam_full.2 hu
  have hAlpha := hasDerivWithinAt_terminal_horizontal_slice hBarStar
    J.alpha_full.2 hu
  have hpair := hLam.prodMk hAlpha
  dsimp [p] at hgrav hphi
  rw [hgrav, hphi] at hpair
  change HasDerivWithinAt
    (fun t => (P.state.lam (t, vStar), P.state.alpha (t, vStar)))
    (C1Solution.rectangleF (P.state.rectangleState (u, vStar)))
    (Icc 0 a) u
  simpa only [C1Solution.rectangleF] using hpair

end ChristodoulouBV.Uniqueness

end
