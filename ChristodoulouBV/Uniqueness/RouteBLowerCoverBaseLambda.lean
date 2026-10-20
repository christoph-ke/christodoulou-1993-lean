module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseJets
public import ChristodoulouBV.Uniqueness.RouteBLowerCoverJetClosure
import ChristodoulouBV.Uniqueness.ExtensionLocalMixed
import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisCoefficients
import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisDerivativeCompatibility
import ChristodoulouBV.C1Solution.ExtractionCore
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Full first jet of the terminal expansion

The incoming mixed coefficient and the outgoing Volterra derivative form a
jointly continuous first jet on the closed terminal rectangle.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The canonical expansion has both first derivatives, including on the
terminal base and the initial incoming edge. -/
theorem OffAxisTerminalC1Packet.lam_full_jet
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ContDiffOn ℝ 1 P.state.lam (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt P.state.lam
          (rectangleScalarJet
            (P.state.lam p * P.state.lambdaVCoefficient p)
            (P.lambdaVTrace p))
          (Icc 0 a ×ˢ Icc vBar vStar) p := by
  have hdu : ContinuousOn
      (fun p => P.state.lam p * P.state.lambdaVCoefficient p)
      (Icc 0 a ×ˢ Icc vBar vStar) :=
    P.state.lam_cont.mul P.state.coefficients_continuousOn.2.2.1
  apply rectangle_scalar_full_jet_of_compatible_family
    (F := fun b p => (S b).lam p.1 p.2)
    (f := P.state.lam)
    (du := fun p => P.state.lam p * P.state.lambdaVCoefficient p)
    (dv := P.lambdaVTrace) ha haBar hBarStar
    P.state.lam_cont hdu P.lambdaV_cont
    (fun b hb u hu v hv => (P.state.match_old b hb u hu v hv).2.2.1)
  intro b hb u hu v hv
  let H := (hfamily b hb).1
  let B : ℝ := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith only [ha, haBar, hu.1, hv.1, hv.2]
  have hBb : B < b := by dsimp [B]; linarith only [hv.2]
  have hvB : v < B := by dsimp [B]; linarith only [hv.2]
  have huv : u < v := hu.2.trans (haBar.trans hv.1)
  have hpK : (u, v) ∈ interior (closedCoordTriangle 0 B) := by
    rw [interior_closedCoordTriangle]
    exact ⟨hu.1, huv, hvB⟩
  have hdiff : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => (S b).lam p.1 p.2) (u, v) :=
    (((C1Solution.five_fields_contDiffOn hB hBb H).1.differentiableOn
      (by norm_num)).mono interior_subset (u, v) hpK).differentiableAt
      (isOpen_interior.mem_nhds hpK)
  have hp : (u, v) ∈ interior (developmentWithInitialEdge b) := by
    have hopen : IsOpen (openCoordTriangle 0 b) := by
      rw [← interior_closedCoordTriangle]
      exact isOpen_interior
    have hsub : openCoordTriangle 0 b ⊆ developmentWithInitialEdge b := by
      intro q hq
      exact ⟨hq.1.le, hq.2.1, hq.2.2⟩
    exact (hopen.subset_interior_iff.mpr hsub) ⟨hu.1, huv, hv.2⟩
  have hm := P.state.match_old b hb u ⟨hu.1.le, hu.2.le⟩ v
    ⟨hv.1.le, hv.2⟩
  obtain ⟨hr, hmass, hlam, hnu, _, _, _, _, _⟩ := hm
  have hsource : localMixedCoefficient (S b) u v =
      P.state.lam (u, v) * P.state.lambdaVCoefficient (u, v) := by
    simp only [localMixedCoefficient,
      OffAxisTerminalTraces.lambdaVCoefficient,
      OffAxisTerminalTraces.mixedCoefficient,
      OffAxisTerminalTraces.massGap,
      OffAxisTerminalTraces.massRatio]
    rw [hr, hmass, hlam, hnu]
    ring
  have hderU := lam_hasDerivAt_u_of_c1_interior H hp
  have hderV : HasDerivAt (fun w => (S b).lam u w)
      (P.lambdaVTrace (u, v)) v := by
    have hslice : DifferentiableAt ℝ (fun w => (S b).lam u w) v :=
      hdiff.comp v
        (((hasDerivAt_const v u).prodMk (hasDerivAt_id' v)).differentiableAt)
    rw [lambdaV_terminal_trace_eq_old ha haBar P.state
      P.lambdaV_match hb ⟨hu.1.le, hu.2.le⟩ hv]
    exact hslice.hasDerivAt
  refine ⟨hdiff, ?_, ?_⟩
  · rw [← hsource]
    exact fderiv_apply_first_of_hasDerivAt hdiff hderU
  · exact fderiv_apply_second_of_hasDerivAt hdiff hderV

end ChristodoulouBV.Uniqueness

end
