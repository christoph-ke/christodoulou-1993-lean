module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseTransverseSlice
public import ChristodoulouBV.Uniqueness.RouteBLowerCoverVerticalODEInteriorParameter
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Outgoing ODEs for the canonical half-open incoming jets

Compatibility identifies the canonical incoming jets with one finite member
near each strict point below the terminal edge. The finite mixed-partial
equations therefore hold for the canonical half-open traces.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- At strict interior parameters, the canonical incoming `ν` jet obeys
`Pᵥ = A P + Aᵤν` on the half-open terminal base. -/
theorem OffAxisTerminalC1Packet.nu_incoming_jet_hasDerivAt_v
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {u v : ℝ} (hu : u ∈ Ioo 0 a) (hv : v ∈ Ioo vBar vStar) :
    HasDerivAt (fun w => P.nuIncomingJetBelow (u, w))
      (P.state.nuTransportCoefficient (u, v) *
        P.nuIncomingJetBelow (u, v) +
        P.state.nuTransportSource (u, v)) v := by
  let b : ℝ := (v + vStar) / 2
  have hvb : v < b := by dsimp [b]; linarith only [hv.2]
  have hb : b ∈ Ioo (0 : ℝ) vStar := by
    dsimp [b]
    constructor <;> linarith only [ha, haBar, hv.1, hv.2]
  let B : ℝ := (v + b) / 2
  have hvB : v < B := by dsimp [B]; linarith only [hvb]
  have hBb : B < b := by dsimp [B]; linarith only [hvb]
  have hB : 0 < B := by dsimp [B]; linarith only [ha, haBar, hv.1, hvb]
  let K := closedCoordTriangle 0 B
  have hp : (u, v) ∈ openCoordTriangle 0 B :=
    ⟨hu.1, hu.2.trans (haBar.trans hv.1), hvB⟩
  have hOld := finite_nu_incoming_jet_hasDerivAt_v hB hBb
    (hfamily b hb).1 hp
  have hmatch (t : ℝ) (ht : t ∈ Icc 0 a)
      (w : ℝ) (hw : w ∈ Ioo vBar B) :
      P.state.nu (t, w) = (S b).nu t w :=
    (P.state.match_old b hb t ht w ⟨hw.1.le, hw.2.trans hBb⟩).2.2.2.1
  have hjet (w : ℝ) (hw : w ∈ Ioo vBar B) :
      P.nuIncomingJetBelow (u, w) =
        (fderivWithin ℝ (fun q : ℝ × ℝ => (S b).nu q.1 q.2)
          K (u, w)) (1, 0) :=
    horizontal_derivWithin_eq_finite_triangle_jet ha haBar
      (C1Solution.five_fields_contDiffOn hB hBb (hfamily b hb).1).2.1
      hmatch hu hw
  have hEq : (fun w => P.nuIncomingJetBelow (u, w)) =ᶠ[𝓝 v]
      (fun w => (fderivWithin ℝ
        (fun q : ℝ × ℝ => (S b).nu q.1 q.2) K (u, w)) (1, 0)) := by
    filter_upwards [Ioo_mem_nhds hv.1 hvB] with w hw
    exact hjet w hw
  have hOld' := hOld.congr_of_eventuallyEq hEq
  obtain ⟨_, hA, hF⟩ := P.state.nu_transport_coefficients_match_old
    hb ⟨hu.1.le, hu.2.le⟩ ⟨hv.1.le, hvb⟩
  change HasDerivAt (fun w => P.nuIncomingJetBelow (u, w)) _ v at hOld'
  rw [hA, hF, hjet v ⟨hv.1, hvB⟩]
  exact hOld'

/-- At strict interior parameters, the canonical incoming `β` jet obeys
`Bᵥ = (A P + Aᵤν)φ + Aνζ/r`, where `P` is the canonical incoming `ν` jet. -/
theorem OffAxisTerminalC1Packet.beta_incoming_jet_hasDerivAt_v
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {u v : ℝ} (hu : u ∈ Ioo 0 a) (hv : v ∈ Ioo vBar vStar) :
    HasDerivAt (fun w => P.betaIncomingJetBelow (u, w))
      (P.state.betaTransportSource P.nuIncomingJetBelow (u, v)) v := by
  let b : ℝ := (v + vStar) / 2
  have hvb : v < b := by dsimp [b]; linarith only [hv.2]
  have hb : b ∈ Ioo (0 : ℝ) vStar := by
    dsimp [b]
    constructor <;> linarith only [ha, haBar, hv.1, hv.2]
  let B : ℝ := (v + b) / 2
  have hvB : v < B := by dsimp [B]; linarith only [hvb]
  have hBb : B < b := by dsimp [B]; linarith only [hvb]
  have hB : 0 < B := by dsimp [B]; linarith only [ha, haBar, hv.1, hvb]
  let K := closedCoordTriangle 0 B
  have hp : (u, v) ∈ openCoordTriangle 0 B :=
    ⟨hu.1, hu.2.trans (haBar.trans hv.1), hvB⟩
  have hOld := finite_beta_incoming_jet_hasDerivAt_v hB hBb
    (hfamily b hb).1 hp
  have hmatchNu (t : ℝ) (ht : t ∈ Icc 0 a)
      (w : ℝ) (hw : w ∈ Ioo vBar B) :
      P.state.nu (t, w) = (S b).nu t w :=
    (P.state.match_old b hb t ht w ⟨hw.1.le, hw.2.trans hBb⟩).2.2.2.1
  have hmatchBeta (t : ℝ) (ht : t ∈ Icc 0 a)
      (w : ℝ) (hw : w ∈ Ioo vBar B) :
      P.state.zeta (t, w) + P.state.nu (t, w) *
          P.state.phi (t, w) = (S b).beta t w := by
    obtain ⟨_, _, _, hn, hφ, hz, _, _, _⟩ :=
      P.state.match_old b hb t ht w ⟨hw.1.le, hw.2.trans hBb⟩
    rw [hz, hn, hφ]
    simp only [Fields.zeta]
    ring
  have hjetNu (w : ℝ) (hw : w ∈ Ioo vBar B) :
      P.nuIncomingJetBelow (u, w) =
        (fderivWithin ℝ (fun q : ℝ × ℝ => (S b).nu q.1 q.2)
          K (u, w)) (1, 0) :=
    horizontal_derivWithin_eq_finite_triangle_jet ha haBar
      (C1Solution.five_fields_contDiffOn hB hBb (hfamily b hb).1).2.1
      hmatchNu hu hw
  have hjetBeta (w : ℝ) (hw : w ∈ Ioo vBar B) :
      P.betaIncomingJetBelow (u, w) =
        (fderivWithin ℝ (fun q : ℝ × ℝ => (S b).beta q.1 q.2)
          K (u, w)) (1, 0) := by
    change derivWithin (fun t => P.state.zeta (t, w) +
      P.state.nu (t, w) * P.state.phi (t, w)) (Icc 0 a) u = _
    exact horizontal_derivWithin_eq_finite_triangle_jet ha haBar
      (f := fun q => P.state.zeta q + P.state.nu q * P.state.phi q)
      (C1Solution.beta_contDiffOn hB hBb (hfamily b hb).1)
      hmatchBeta hu hw
  have hEq : (fun w => P.betaIncomingJetBelow (u, w)) =ᶠ[𝓝 v]
      (fun w => (fderivWithin ℝ
        (fun q : ℝ × ℝ => (S b).beta q.1 q.2) K (u, w)) (1, 0)) := by
    filter_upwards [Ioo_mem_nhds hv.1 hvB] with w hw
    exact hjetBeta w hw
  have hOld' := hOld.congr_of_eventuallyEq hEq
  obtain ⟨_, hA, hF⟩ := P.state.nu_transport_coefficients_match_old
    hb ⟨hu.1.le, hu.2.le⟩ ⟨hv.1.le, hvb⟩
  obtain ⟨hr, _, _, hn, hφ, hz, _, _, _⟩ :=
    P.state.match_old b hb u ⟨hu.1.le, hu.2.le⟩ v
      ⟨hv.1.le, hvb⟩
  have hSource : P.state.betaTransportSource P.nuIncomingJetBelow (u, v) =
      (((2 * (S b).m u v *
          ((S b).lam u v /
            (1 - 2 * (S b).m u v / (S b).r u v)) /
          (S b).r u v ^ 2) *
          (fderivWithin ℝ (fun q : ℝ × ℝ => (S b).nu q.1 q.2)
            K (u, v)) (1, 0) +
        (((S b).lam u v / (1 - 2 * (S b).m u v / (S b).r u v)) *
          (S b).zeta u v ^ 2 / (S b).r u v ^ 2 -
          4 * (S b).m u v *
            ((S b).lam u v / (1 - 2 * (S b).m u v / (S b).r u v)) *
            (S b).nu u v ^ 2 / (S b).r u v ^ 3)) * (S b).phi u v +
        (2 * (S b).m u v *
          ((S b).lam u v /
            (1 - 2 * (S b).m u v / (S b).r u v)) /
          (S b).r u v ^ 2) * (S b).nu u v *
          ((S b).zeta u v / (S b).r u v)) := by
    simp only [OffAxisTerminalTraces.betaTransportSource,
      hA, hF, hjetNu v ⟨hv.1, hvB⟩, hr, hn, hφ, hz]
    ring
  rw [hSource]
  exact hOld'

/-- The compatible incoming `ν` jets have a jointly continuous terminal
trace on the complete closed off-axis rectangle. -/
theorem OffAxisTerminalC1Packet.exists_nu_incoming_jet_terminal_trace
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ N : ℝ × ℝ → ℝ,
      ContinuousOn N (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar vStar,
        N (u, v) = P.nuIncomingJetBelow (u, v) := by
  have hjet := P.nu_beta_incoming_jets_continuousOn_below
    ha haBar hBarStar hfamily |>.1
  have h0 : vBar ∈ Ico vBar vStar := ⟨le_rfl, hBarStar⟩
  have hy₀ : ContinuousOn
      (fun u => P.nuIncomingJetBelow (u, vBar)) (Icc 0 a) :=
    hjet.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => ⟨hu, h0⟩)
  have hy (u : ℝ) (hu : u ∈ Ioo 0 a) :
      ContinuousOn (fun v => P.nuIncomingJetBelow (u, v))
        (Ico vBar vStar) :=
    hjet.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨⟨hu.1.le, hu.2.le⟩, hv⟩)
  have hyparameter (v : ℝ) (hv : v ∈ Ico vBar vStar) :
      ContinuousOn (fun u => P.nuIncomingJetBelow (u, v))
        (Icc 0 a) :=
    hjet.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => ⟨hu, hv⟩)
  exact exists_continuousOn_terminal_of_interior_parameter_linear_ode
    ha hBarStar
    P.state.nu_transport_coefficients_continuousOn.1
    P.state.nu_transport_coefficients_continuousOn.2
    hy₀ hy hyparameter
    (fun _ _ => rfl)
    (fun u hu v hv =>
      P.nu_incoming_jet_hasDerivAt_v ha haBar hfamily hu hv)

/-- Both compatible incoming jets, `νᵤ` and `βᵤ`, extend jointly and
continuously to the terminal edge. -/
theorem OffAxisTerminalC1Packet.exists_nu_beta_incoming_jet_terminal_traces
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v)) :
    ∃ N B : ℝ × ℝ → ℝ,
      ContinuousOn N (Icc 0 a ×ˢ Icc vBar vStar) ∧
      ContinuousOn B (Icc 0 a ×ˢ Icc vBar vStar) ∧
      (∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar vStar,
        N (u, v) = P.nuIncomingJetBelow (u, v)) ∧
      (∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar vStar,
        B (u, v) = P.betaIncomingJetBelow (u, v)) := by
  obtain ⟨N, hNcont, hNmatch⟩ :=
    P.exists_nu_incoming_jet_terminal_trace ha haBar hBarStar hfamily
  have hjet := P.nu_beta_incoming_jets_continuousOn_below
    ha haBar hBarStar hfamily |>.2
  have h0 : vBar ∈ Ico vBar vStar := ⟨le_rfl, hBarStar⟩
  have hy₀ : ContinuousOn
      (fun u => P.betaIncomingJetBelow (u, vBar)) (Icc 0 a) :=
    hjet.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => ⟨hu, h0⟩)
  have hy (u : ℝ) (hu : u ∈ Ioo 0 a) :
      ContinuousOn (fun v => P.betaIncomingJetBelow (u, v))
        (Ico vBar vStar) :=
    hjet.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨⟨hu.1.le, hu.2.le⟩, hv⟩)
  have hyparameter (v : ℝ) (hv : v ∈ Ico vBar vStar) :
      ContinuousOn (fun u => P.betaIncomingJetBelow (u, v))
        (Icc 0 a) :=
    hjet.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => ⟨hu, hv⟩)
  have hsource := P.state.beta_transport_source_continuousOn hNcont
  obtain ⟨B, hBcont, hBmatch⟩ :=
    exists_continuousOn_terminal_of_interior_parameter_linear_ode
      ha hBarStar (a := fun _ => 0)
      (b := P.state.betaTransportSource N)
      continuousOn_const hsource hy₀ hy hyparameter
      (fun _ _ => rfl) (by
        intro u hu v hv
        have hD := P.beta_incoming_jet_hasDerivAt_v ha haBar hfamily hu hv
        have hN : N (u, v) = P.nuIncomingJetBelow (u, v) :=
          hNmatch u ⟨hu.1.le, hu.2.le⟩ v ⟨hv.1.le, hv.2⟩
        have hsourceEq :
            P.state.betaTransportSource N (u, v) =
              P.state.betaTransportSource P.nuIncomingJetBelow (u, v) := by
          simp only [OffAxisTerminalTraces.betaTransportSource, hN]
        change HasDerivAt (fun w => P.betaIncomingJetBelow (u, w))
          (0 * P.betaIncomingJetBelow (u, v) +
            P.state.betaTransportSource N (u, v)) v
        simpa only [zero_mul, zero_add, hsourceEq] using hD)
  exact ⟨N, B, hNcont, hBcont, hNmatch, hBmatch⟩

end ChristodoulouBV.Uniqueness

end
