module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseAlpha
import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisEdgeC1
import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarEdge
import ChristodoulouBV.C1Solution.ExtractionJets
import ChristodoulouBV.C1Solution.ExtractionCoefficient
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Outgoing jets of the terminal incoming fields

The mixed equations determine the outgoing derivatives of `ν` and `β`
through the terminal edge. The remaining transverse derivatives require
outgoing transport of the incoming jets.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The canonical terminal incoming expansion and incoming scalar amplitude
have their outgoing derivatives on every strict outgoing slice. The formula
also covers the initial incoming edge `u = 0`. -/
theorem OffAxisTerminalC1Packet.nu_beta_hasDerivAt_v
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {u v : ℝ} (hu : u ∈ Icc 0 a) (hv : v ∈ Ioo vBar vStar) :
    HasDerivAt (fun w => P.state.nu (u, w))
      (P.state.lam (u, v) * P.state.lambdaVCoefficient (u, v)) v ∧
    HasDerivAt (fun w => P.state.zeta (u, w) +
        P.state.nu (u, w) * P.state.phi (u, w))
      (P.state.lam (u, v) * P.state.lambdaVCoefficient (u, v) *
        P.state.phi (u, v)) v := by
  let b : ℝ := (v + vStar) / 2
  have hvb : v < b := by dsimp [b]; linarith only [hv.2]
  have hb : b ∈ Ioo (0 : ℝ) vStar := by
    dsimp [b]
    constructor <;> linarith only [ha, haBar, hv.1, hv.2]
  let B : ℝ := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith only [ha, haBar, hv.1, hvb]
  have hBb : B < b := by dsimp [B]; linarith only [hvb]
  have hvB : v < B := by dsimp [B]; linarith only [hvb]
  have huv : u < v := hu.2.trans_lt (haBar.trans hv.1)
  have hpK : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hu.1, huv.le, hvB.le⟩
  let H := (hfamily b hb).1
  have hfour := C1Solution.four_mixed_coordinate_jets hB hBb H hpK
  have hcoeff := C1Solution.canonicalMixedCoefficient_eq_frozen
    hB hBb H hu.1 huv hvB.le
  have hnuOld : HasDerivAt (fun w => (S b).nu u w)
      ((2 * (S b).m u v / (S b).r u v) * (S b).lam u v *
        (S b).nu u v /
        ((1 - 2 * (S b).m u v / (S b).r u v) * (S b).r u v)) v := by
    convert vertical_hasDerivAt_of_closed_jet
      (C1Solution.five_fields_contDiffOn hB hBb H).2.1
      hu.1 huv hvB (g := C1Solution.canonicalMixedCoefficient b (S b) (u, v))
      hfour.2.1 using 1
    exact hcoeff.symm
  have hbetaOld : HasDerivAt (fun w => (S b).beta u w)
      ((2 * (S b).m u v / (S b).r u v) * (S b).lam u v *
        (S b).nu u v /
        ((1 - 2 * (S b).m u v / (S b).r u v) * (S b).r u v) *
        (S b).phi u v) v := by
    convert vertical_hasDerivAt_of_closed_jet
      (C1Solution.beta_contDiffOn hB hBb H)
      hu.1 huv hvB
      (g := C1Solution.canonicalMixedCoefficient b (S b) (u, v) *
        (S b).phi u v) hfour.2.2.2 using 1
    rw [hcoeff]
  have hnuEq : (fun w => P.state.nu (u, w)) =ᶠ[𝓝 v]
      (fun w => (S b).nu u w) := by
    filter_upwards [Ioo_mem_nhds hv.1 hvb] with w hw
    exact (P.state.match_old b hb u hu w ⟨hw.1.le, hw.2⟩).2.2.2.1
  have hbetaEq : (fun w => P.state.zeta (u, w) +
        P.state.nu (u, w) * P.state.phi (u, w)) =ᶠ[𝓝 v]
      (fun w => (S b).beta u w) := by
    filter_upwards [Ioo_mem_nhds hv.1 hvb] with w hw
    obtain ⟨_, _, _, hn, hp, hz, _, _, _⟩ :=
      P.state.match_old b hb u hu w ⟨hw.1.le, hw.2⟩
    rw [hz, hn, hp]
    simp only [Fields.zeta]
    ring
  obtain ⟨hr, hm, hl, hn, hp, _, _, _, _⟩ :=
    P.state.match_old b hb u hu v ⟨hv.1.le, hvb⟩
  have hsource : P.state.lam (u, v) *
      P.state.lambdaVCoefficient (u, v) =
      (2 * (S b).m u v / (S b).r u v) * (S b).lam u v *
        (S b).nu u v /
        ((1 - 2 * (S b).m u v / (S b).r u v) * (S b).r u v) := by
    simp only [OffAxisTerminalTraces.lambdaVCoefficient,
      OffAxisTerminalTraces.mixedCoefficient,
      OffAxisTerminalTraces.massRatio,
      OffAxisTerminalTraces.massGap, hr, hm, hl, hn]
    ring
  constructor
  · rw [hsource]
    exact hnuOld.congr_of_eventuallyEq hnuEq
  · rw [hsource, hp]
    exact hbetaOld.congr_of_eventuallyEq hbetaEq

end ChristodoulouBV.Uniqueness

end
