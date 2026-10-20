module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesTerminalIncoming
public import ChristodoulouBV.Uniqueness.RouteBLowerTilesBaseSlice
import Mathlib.Tactic

/-!
# Characteristic equations of the old terminal state

The full closed-base jets satisfy both semilinear characteristic equations
on every horizontal and vertical slice of the old off-axis rectangle.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The canonical old seven-state field solves the same characteristic
system as each new safe lower tile, including the terminal seam. -/
theorem RouteBTerminalBaseJets.characteristic_jets
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    {P : OffAxisTerminalC1Packet a vBar vStar S}
    (J : RouteBTerminalBaseJets P)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    {u v : ℝ} (hu : u ∈ Icc 0 a) (hv : v ∈ Icc vBar vStar) :
    HasDerivWithinAt
      (fun s => (P.state.rectangleState (s, v)).1)
      (C1Solution.rectangleF (P.state.rectangleState (u, v)))
      (Icc 0 a) u ∧
    HasDerivWithinAt
      (fun t => (P.state.rectangleState (u, t)).2)
      (C1Solution.rectangleG (P.state.rectangleState (u, v)))
      (Icc vBar vStar) v := by
  let p : ℝ × ℝ := (u, v)
  let z := P.state.rectangleState p
  have hfloor := P.state.floors u hu v hv
  have hr : 0 < P.state.r p := P.state.radius_pos.trans_le hfloor.1
  have hgap : 0 < P.state.massGap p :=
    P.state.gap_pos.trans_le hfloor.2.2
  have hmassgap : P.state.r p - 2 * P.state.m p ≠ 0 := by
    have hratio : (1 - 2 * P.state.m p / P.state.r p) *
        P.state.r p = P.state.r p - 2 * P.state.m p := by
      field_simp [ne_of_gt hr]
    intro heq
    have hzero := hratio.trans heq
    exact (mul_ne_zero (ne_of_gt hgap) (ne_of_gt hr)) hzero
  have hgrav : P.state.lam p * P.state.lambdaVCoefficient p =
      C1Solution.stateGrav z := by
    change P.state.lam p *
        (P.state.nu p *
          ((2 * P.state.m p / P.state.r p) /
            ((1 - 2 * P.state.m p / P.state.r p) * P.state.r p))) =
      2 * P.state.m p * P.state.lam p * P.state.nu p /
        (P.state.r p * (P.state.r p - 2 * P.state.m p))
    field_simp [ne_of_gt hr, ne_of_gt hgap, hmassgap]
  have hphi : P.state.phi p = C1Solution.statePhi z := by
    change P.state.phi p =
      P.state.r p * P.state.phi p / P.state.r p
    field_simp [ne_of_gt hr]
  have htheta : P.state.theta p = C1Solution.stateTheta z := by
    rw [P.theta_eq_alpha_sub_lam_phi ha haBar hBarStar ⟨hu, hv⟩]
    change P.state.alpha p - P.state.lam p * P.state.phi p =
      P.state.alpha p - P.state.lam p * C1Solution.statePhi z
    rw [hphi]
  have hmass : P.state.massGap p * P.state.theta p ^ 2 /
        (2 * P.state.lam p) =
      C1Solution.stateMassGap z / C1Solution.stateRadius z *
        C1Solution.stateTheta z ^ 2 /
          (2 * C1Solution.stateLam z) := by
    rw [htheta]
    change (1 - 2 * P.state.m p / P.state.r p) *
        C1Solution.stateTheta z ^ 2 / (2 * P.state.lam p) =
      ((P.state.r p - 2 * P.state.m p) / P.state.r p) *
        C1Solution.stateTheta z ^ 2 / (2 * P.state.lam p)
    exact mass_out_density_eq_rectangle_density (ne_of_gt hr)
  have hLamU := hasDerivWithinAt_base_horizontal_slice
    J.lam_full.2 hu hv
  have hAlphaU := hasDerivWithinAt_base_horizontal_slice
    J.alpha_full.2 hu hv
  have hNuV := hasDerivWithinAt_base_vertical_slice
    J.nu_full.2 hu hv
  have hBetaV := hasDerivWithinAt_base_vertical_slice
    J.beta_full.2 hu hv
  have hMassV := hasDerivWithinAt_base_vertical_slice
    J.mass_full.2 hu hv
  have hRadiusV := hasDerivWithinAt_base_vertical_slice
    J.radius_full.2 hu hv
  have hPsiV := hasDerivWithinAt_base_vertical_slice
    J.scalarRadius_full.2 hu hv
  dsimp [p, z] at hgrav hphi htheta hmass
  rw [hgrav] at hLamU hAlphaU hNuV hBetaV
  rw [hphi] at hAlphaU hBetaV
  rw [hmass] at hMassV
  constructor
  · change HasDerivWithinAt
      (fun s => (P.state.lam (s, v), P.state.alpha (s, v)))
      (C1Solution.rectangleF (P.state.rectangleState (u, v)))
      (Icc 0 a) u
    simpa only [C1Solution.rectangleF] using hLamU.prodMk hAlphaU
  · change HasDerivWithinAt
      (fun t => (P.state.nu (u, t),
        (P.state.zeta (u, t) + P.state.nu (u, t) * P.state.phi (u, t),
          (P.state.m (u, t),
            (P.state.r (u, t),
              P.state.r (u, t) * P.state.phi (u, t))))))
      (C1Solution.rectangleG (P.state.rectangleState (u, v)))
      (Icc vBar vStar) v
    simpa only [C1Solution.rectangleG, C1Solution.stateLam,
      C1Solution.stateAlpha, OffAxisTerminalTraces.rectangleState] using
      hNuV.prodMk (hBetaV.prodMk
        (hMassV.prodMk (hRadiusV.prodMk hPsiV)))

end ChristodoulouBV.Uniqueness

end
