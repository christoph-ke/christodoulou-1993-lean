module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseJetsPackage
public import ChristodoulouBV.Uniqueness.RouteBLowerTilesBaseSlice
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Tactic

/-!
# Outgoing data from the terminal base jets

The old family's full first jets give a continuous incoming derivative of
the five outgoing rectangle variables along the entire terminal base.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The relative incoming derivative of the outgoing terminal state. -/
@[expose] noncomputable def lowerTerminalOutgoingPrime
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S) (u : ℝ) :
    C1Solution.OutgoingState :=
  derivWithin (fun t => (P.state.rectangleState (t, vStar)).2)
    (Icc 0 a) u

/-- This derivative is continuous on the compact base and differentiates
the actual five-field outgoing trace at both endpoints as well. -/
theorem RouteBTerminalBaseJets.outgoingPrime_regular
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    {P : OffAxisTerminalC1Packet a vBar vStar S}
    (J : RouteBTerminalBaseJets P)
    (ha : 0 < a) (hBarStar : vBar ≤ vStar) :
    ContinuousOn (lowerTerminalOutgoingPrime P) (Icc 0 a) ∧
    (∀ u ∈ Icc 0 a,
      HasDerivWithinAt
        (fun t => (P.state.rectangleState (t, vStar)).2)
        (lowerTerminalOutgoingPrime P u) (Icc 0 a) u) := by
  let Q : C1Solution.RectangleState →L[ℝ]
      C1Solution.OutgoingState := ContinuousLinearMap.snd ℝ _ _
  have hOut : ContDiffOn ℝ 1
      (fun p => (P.state.rectangleState p).2)
      (Icc 0 a ×ˢ Icc vBar vStar) := by
    exact Q.contDiff.comp_contDiffOn J.state_c1
  have hSlice := contDiffOn_terminal_horizontal_slice hBarStar hOut
  constructor
  · exact hSlice.continuousOn_derivWithin
      (uniqueDiffOn_Icc ha) (by norm_num)
  · intro u hu
    exact (hSlice.differentiableOn (by norm_num) u hu).hasDerivWithinAt

/-- The five component derivatives are exactly the incoming entries of the
canonical closed-rectangle jet package. -/
theorem RouteBTerminalBaseJets.outgoingPrime_components
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    {P : OffAxisTerminalC1Packet a vBar vStar S}
    (J : RouteBTerminalBaseJets P)
    (ha : 0 < a) (hBarStar : vBar ≤ vStar)
    {u : ℝ} (hu : u ∈ Icc 0 a) :
    lowerTerminalOutgoingPrime P u =
      (J.nuU (u, vStar),
        (J.betaU (u, vStar),
          (P.state.massGap (u, vStar) * P.state.zeta (u, vStar) ^ 2 /
              (2 * P.state.nu (u, vStar)),
            (P.state.nu (u, vStar),
              P.state.zeta (u, vStar) +
                P.state.nu (u, vStar) * P.state.phi (u, vStar))))) := by
  let I := Icc 0 a
  let q := lowerTerminalOutgoingPrime P u
  have hq : HasDerivWithinAt
      (fun t => (P.state.rectangleState (t, vStar)).2) q I u :=
    (J.outgoingPrime_regular ha hBarStar).2 u hu
  have hunique := (uniqueDiffOn_Icc ha) u hu
  have hν := hasDerivWithinAt_terminal_horizontal_slice hBarStar
    J.nu_full.2 hu
  have hβ := hasDerivWithinAt_terminal_horizontal_slice hBarStar
    J.beta_full.2 hu
  have hm := hasDerivWithinAt_terminal_horizontal_slice hBarStar
    J.mass_full.2 hu
  have hr := hasDerivWithinAt_terminal_horizontal_slice hBarStar
    J.radius_full.2 hu
  have hψ := hasDerivWithinAt_terminal_horizontal_slice hBarStar
    J.scalarRadius_full.2 hu
  have htuple : HasDerivWithinAt
      (fun t => (P.state.rectangleState (t, vStar)).2)
      (J.nuU (u, vStar),
        (J.betaU (u, vStar),
          (P.state.massGap (u, vStar) * P.state.zeta (u, vStar) ^ 2 /
              (2 * P.state.nu (u, vStar)),
            (P.state.nu (u, vStar),
              P.state.zeta (u, vStar) +
                P.state.nu (u, vStar) * P.state.phi (u, vStar)))))
      I u := by
    change HasDerivWithinAt
      (fun t => (P.state.nu (t, vStar),
        (P.state.zeta (t, vStar) +
          P.state.nu (t, vStar) * P.state.phi (t, vStar),
          (P.state.m (t, vStar),
            (P.state.r (t, vStar),
              P.state.r (t, vStar) * P.state.phi (t, vStar)))))) _ I u
    exact hν.prodMk (hβ.prodMk (hm.prodMk (hr.prodMk hψ)))
  exact (hq.derivWithin hunique).symm.trans (htuple.derivWithin hunique)

/-- The radius and scalar-radius components of the outgoing derivative
satisfy the two tangential constraints required by the first tile. -/
theorem RouteBTerminalBaseJets.outgoingPrime_radius_psi
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    {P : OffAxisTerminalC1Packet a vBar vStar S}
    (J : RouteBTerminalBaseJets P)
    (ha : 0 < a) (hBarStar : vBar ≤ vStar)
    {u : ℝ} (hu : u ∈ Icc 0 a) :
    (lowerTerminalOutgoingPrime P u).2.2.2.1 =
      C1Solution.stateNu (P.state.rectangleState (u, vStar)) ∧
    (lowerTerminalOutgoingPrime P u).2.2.2.2 =
      C1Solution.stateBeta (P.state.rectangleState (u, vStar)) := by
  rw [J.outgoingPrime_components ha hBarStar hu]
  exact ⟨rfl, rfl⟩

/-- The mass component has the prescribed incoming constraint on the
terminal base. -/
theorem RouteBTerminalBaseJets.outgoingPrime_mass
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    {P : OffAxisTerminalC1Packet a vBar vStar S}
    (J : RouteBTerminalBaseJets P)
    (ha : 0 < a) (hBarStar : vBar ≤ vStar)
    {u : ℝ} (hu : u ∈ Icc 0 a) :
    (lowerTerminalOutgoingPrime P u).2.2.1 =
      (1 - 2 * C1Solution.stateMass
          (P.state.rectangleState (u, vStar)) /
        C1Solution.stateRadius
          (P.state.rectangleState (u, vStar))) *
        C1Solution.stateZeta
          (P.state.rectangleState (u, vStar)) ^ 2 /
        (2 * C1Solution.stateNu
          (P.state.rectangleState (u, vStar))) := by
  have hr : P.state.r (u, vStar) ≠ 0 :=
    ne_of_gt (P.state.radius_pos.trans_le
      (P.state.floors u hu vStar ⟨hBarStar, le_rfl⟩).1)
  rw [J.outgoingPrime_components ha hBarStar hu]
  simp only [C1Solution.stateMass, C1Solution.stateRadius,
    C1Solution.stateNu, C1Solution.stateZeta,
    C1Solution.statePhi, C1Solution.stateBeta,
    C1Solution.statePsi, OffAxisTerminalTraces.rectangleState,
    OffAxisTerminalTraces.massGap, OffAxisTerminalTraces.massRatio]
  field_simp [hr]
  ring

end ChristodoulouBV.Uniqueness

end
