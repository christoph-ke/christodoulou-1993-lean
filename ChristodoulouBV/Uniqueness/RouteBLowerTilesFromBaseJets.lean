module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesTerminalIncoming
public import ChristodoulouBV.Uniqueness.RouteBLowerTilesTerminalBase
public import ChristodoulouBV.Uniqueness.RouteBLowerTilesInitialGauge
import Mathlib.Tactic

/-!
# The old terminal jets as lower tile data

The complete canonical base-jet package and the prescribed initial gauge
instantiate the constrained characteristic interface used by the finite
lower tile march.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The closed terminal base jets provide all characteristic data and
tangential constraints required by the lower-cover tile construction. -/
theorem RouteBTerminalBaseJets.exists_lowerCoverBaseData
    {a vBar vStar L : ℝ} {S : ℝ → Fields}
    {P : OffAxisTerminalC1Packet a vBar vStar S}
    (J : RouteBTerminalBaseJets P)
    (alpha₀ : ℝ → ℝ)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hL : 0 < L)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ D : LowerCoverBaseData a vStar L,
      D.alpha₀ = alpha₀ ∧
      (∀ u ∈ Icc 0 a,
        D.base u = P.state.rectangleState (u, vStar)) := by
  have hStar0 : 0 ≤ vStar := by linarith only [ha, haBar, hBarStar]
  have hbase := lowerTerminalBase_regular P.state ha.le hBarStar.le
  have hout := J.outgoingPrime_regular ha hBarStar.le
  have hinit := lowerInitialIncoming_regular hStar0 hL hα
  have hzero : (0 : ℝ) ∈ Icc 0 a := ⟨le_rfl, ha.le⟩
  have htop : vStar ∈ Icc vBar vStar := ⟨hBarStar.le, le_rfl⟩
  let base := lowerTerminalBase P.state
  let incoming := lowerInitialIncoming vStar L alpha₀
  let incomingPrime := lowerInitialIncomingPrime vStar L alpha₀
  let outgoingPrime := lowerTerminalOutgoingPrime P
  have hbaseEdge : EqOn base
      (fun u => P.state.rectangleState (u, vStar)) (Icc 0 a) :=
    hbase.2
  have houtDeriv : ∀ u ∈ Icc 0 a,
      HasDerivWithinAt (fun t => (base t).2)
        (outgoingPrime u) (Icc 0 a) u := by
    intro u hu
    have hevent : (fun t => (base t).2) =ᶠ[𝓝[Icc 0 a] u]
        (fun t => (P.state.rectangleState (t, vStar)).2) :=
      Filter.eventually_of_mem self_mem_nhdsWithin
        (fun t ht => congrArg Prod.snd (hbaseEdge ht))
    exact (hout.2 u hu).congr_of_eventuallyEq hevent
      (congrArg Prod.snd (hbaseEdge hu))
  have hinDeriv : ∀ u ∈ Icc 0 a,
      HasDerivWithinAt (fun t => (base t).1)
        (C1Solution.rectangleF (base u)) (Icc 0 a) u := by
    intro u hu
    have hevent : (fun t => (base t).1) =ᶠ[𝓝[Icc 0 a] u]
        (fun t => (P.state.rectangleState (t, vStar)).1) :=
      Filter.eventually_of_mem self_mem_nhdsWithin
        (fun t ht => congrArg Prod.fst (hbaseEdge ht))
    rw [hbaseEdge hu]
    exact (J.incoming_deriv hBarStar.le hu).congr_of_eventuallyEq
      hevent (congrArg Prod.fst (hbaseEdge hu))
  have hcorner : incoming vStar = (base 0).1 := by
    rw [hbaseEdge hzero]
    change lowerInitialIncoming vStar L alpha₀ vStar =
      (P.state.rectangleState (0, vStar)).1
    rw [hinit.2.2.2 vStar ⟨le_rfl, by linarith only [hL]⟩]
    obtain ⟨hlam, halpha⟩ :=
      P.initial_terminal_gauge ha haBar hBarStar hα hfamily htop
    change ((1 / 2 : ℝ), alpha₀ vStar) =
      (P.state.lam (0, vStar), P.state.alpha (0, vStar))
    rw [hlam, halpha]
  refine ⟨{
    base := base
    baseOutgoingPrime := outgoingPrime
    initialIncoming := incoming
    initialIncomingPrime := incomingPrime
    base_cont := hbase.1
    initial_cont := hinit.1
    baseOutgoingPrime_cont := hout.1
    initialIncomingPrime_cont := hinit.2.1
    baseOutgoing_deriv := houtDeriv
    baseIncoming_deriv := hinDeriv
    initialIncoming_deriv := hinit.2.2.1
    corner := hcorner
    alpha₀ := alpha₀
    baseOutgoingPrime_radius := by
      intro u hu
      rw [hbaseEdge hu]
      exact (J.outgoingPrime_radius_psi ha hBarStar.le hu).1
    baseOutgoingPrime_psi := by
      intro u hu
      rw [hbaseEdge hu]
      exact (J.outgoingPrime_radius_psi ha hBarStar.le hu).2
    baseOutgoingPrime_mass := by
      intro u hu
      rw [hbaseEdge hu]
      exact J.outgoingPrime_mass ha hBarStar.le hu
    initial_incoming_gauge := hinit.2.2.2
    initial_radius_corner := by
      rw [hbaseEdge hzero]
      exact P.initial_radius_gauge ha haBar hBarStar hfamily htop
  }, rfl, hbase.2⟩

end ChristodoulouBV.Uniqueness

end
