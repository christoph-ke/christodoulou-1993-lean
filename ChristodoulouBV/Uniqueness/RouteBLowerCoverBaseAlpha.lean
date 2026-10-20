module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseLambda
import ChristodoulouBV.Uniqueness.ExtensionLocalMixed
import ChristodoulouBV.C1Solution.ExtractionCore
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Full first jet of the terminal scalar transport field

The incoming mixed equation and the outgoing Volterra jets close the full
first jet of `α` on the compact terminal rectangle.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The canonical `α` trace has the mixed incoming jet and the outgoing
product-rule jet on the whole terminal rectangle. -/
theorem OffAxisTerminalC1Packet.alpha_full_jet
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ContDiffOn ℝ 1 P.state.alpha (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ p ∈ Icc 0 a ×ˢ Icc vBar vStar,
        HasFDerivWithinAt P.state.alpha
          (rectangleScalarJet
            (P.state.lam p * P.state.lambdaVCoefficient p * P.state.phi p)
            (P.lambdaVTrace p * P.state.quotient p +
              P.state.lam p *
                (P.state.lam p * P.alphaPrimeTrace p)))
          (Icc 0 a ×ˢ Icc vBar vStar) p := by
  let du : ℝ × ℝ → ℝ := fun p =>
    P.state.lam p * P.state.lambdaVCoefficient p * P.state.phi p
  let dv : ℝ × ℝ → ℝ := fun p =>
    P.lambdaVTrace p * P.state.quotient p +
      P.state.lam p * (P.state.lam p * P.alphaPrimeTrace p)
  have hdu : ContinuousOn du (Icc 0 a ×ˢ Icc vBar vStar) :=
    (P.state.lam_cont.mul
      P.state.coefficients_continuousOn.2.2.1).mul P.state.phi_cont
  have hdv : ContinuousOn dv (Icc 0 a ×ˢ Icc vBar vStar) :=
    (P.lambdaV_cont.mul P.state.quotient_cont).add
      (P.state.lam_cont.mul
        (P.state.lam_cont.mul P.alphaPrime_cont))
  apply rectangle_scalar_full_jet_of_compatible_family
    (F := fun b p => (S b).alpha p.1 p.2)
    (f := P.state.alpha) (du := du) (dv := dv)
    ha haBar hBarStar P.state.alpha_cont hdu hdv
    (fun b hb u hu v hv =>
      (P.state.match_old b hb u hu v hv).2.2.2.2.2.2.1)
  intro b hb u hu v hv
  let H := (hfamily b hb).1
  let B : ℝ := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith only [ha, haBar, hv.1, hv.2]
  have hBb : B < b := by dsimp [B]; linarith only [hv.2]
  have hvB : v < B := by dsimp [B]; linarith only [hv.2]
  have huv : u < v := hu.2.trans (haBar.trans hv.1)
  have hpK : (u, v) ∈ interior (closedCoordTriangle 0 B) := by
    rw [interior_closedCoordTriangle]
    exact ⟨hu.1, huv, hvB⟩
  have hdiff : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => (S b).alpha p.1 p.2) (u, v) :=
    (((C1Solution.alpha_contDiffOn hB hBb H).differentiableOn
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
  obtain ⟨hr, hmass, hlam, hnu, hphi, _, _, _, _⟩ := hm
  have hsource : localMixedCoefficient (S b) u v * (S b).phi u v =
      du (u, v) := by
    dsimp [du, localMixedCoefficient,
      OffAxisTerminalTraces.lambdaVCoefficient,
      OffAxisTerminalTraces.mixedCoefficient,
      OffAxisTerminalTraces.massGap,
      OffAxisTerminalTraces.massRatio]
    rw [hr, hmass, hlam, hnu, hphi]
    ring
  have hderU := alpha_hasDerivAt_u_of_c1_interior H hp
  have hderV : HasDerivAt (fun w => (S b).alpha u w) (dv (u, v)) v := by
    have huClosed : u ∈ Icc 0 a := ⟨hu.1.le, hu.2.le⟩
    have hvStar : v ∈ Ioo vBar vStar := ⟨hv.1, hv.2.trans hb.2⟩
    have hterm := P.alpha_hasDerivAt_v ha haBar hBarStar hfamily
      huClosed hvStar
    have heq : (fun w => P.state.alpha (u, w)) =ᶠ[𝓝 v]
        (fun w => (S b).alpha u w) := by
      filter_upwards [Ioo_mem_nhds hv.1 hv.2] with w hw
      exact (P.state.match_old b hb u huClosed w ⟨hw.1.le, hw.2⟩).2.2.2.2.2.2.1
    exact hterm.congr_of_eventuallyEq heq.symm
  refine ⟨hdiff, ?_, ?_⟩
  · rw [← hsource]
    exact fderiv_apply_first_of_hasDerivAt hdiff hderU
  · exact fderiv_apply_second_of_hasDerivAt hdiff hderV

end ChristodoulouBV.Uniqueness

end
