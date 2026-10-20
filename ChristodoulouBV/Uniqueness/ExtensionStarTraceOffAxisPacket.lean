module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceCompactEdgeBounds
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceCompactRadius

/-!
# The compact off-axis terminal trace data

This packages the unconditional lower-order value trace, both incoming
Volterra derivative traces, and the compact C¹ characteristic edge used by
Route B. It gives the off-axis terminal trace used in Theorem 5.1.
-/

public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- All terminal data on a fixed off-axis rectangle and its compact
outgoing edge. The old family remains canonical through the matching fields. -/
structure OffAxisTerminalC1Packet (a vBar vStar : ℝ) (S : ℝ → Fields) where
  state : OffAxisTerminalTraces a vBar vStar S
  alphaPrimeTrace : ℝ × ℝ → ℝ
  lambdaVTrace : ℝ × ℝ → ℝ
  alphaPrime_cont : ContinuousOn alphaPrimeTrace
    (Icc 0 a ×ˢ Icc vBar vStar)
  lambdaV_cont : ContinuousOn lambdaVTrace
    (Icc 0 a ×ˢ Icc vBar vStar)
  alphaPrime_match : ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar vStar,
    alphaPrimeTrace (u, v) =
      deriv (fun t =>
        (S ((v + vStar) / 2)).alpha u t /
          (S ((v + vStar) / 2)).lam u t) v /
        (S ((v + vStar) / 2)).lam u v
  lambdaV_match : ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar vStar,
    lambdaVTrace (u, v) = deriv ((S ((v + vStar) / 2)).lam u) v
  c : ℝ
  Cderiv : ℝ
  H : ℝ
  c_pos : 0 < c
  Cderiv_nonneg : 0 ≤ Cderiv
  H_nonneg : 0 ≤ H
  g : ℝ → ℝ
  hEdge : ℝ → ℝ
  rEdge : ℝ → ℝ
  g_c1 : ContDiffOn ℝ 1 g (Icc a vStar)
  h_c1 : ContDiffOn ℝ 1 hEdge (Icc a vStar)
  r_c1 : ContDiffOn ℝ 1 rEdge (Icc a vStar)
  g_axis_pos : 0 < g a
  edge_bounds : ∀ v ∈ Icc a vStar,
    c ≤ g v ∧ |deriv g v| ≤ Cderiv ∧
      |hEdge v| ≤ H ∧ |deriv hEdge v| ≤ H
  top_match : ∀ v ∈ Icc vBar vStar,
    g v = state.lam (a, v) ∧
      hEdge v = state.quotient (a, v) ∧
      rEdge v = state.r (a, v)
  b₀ : ℝ
  t : ℝ
  b₀_mem : b₀ ∈ Ioo (0 : ℝ) vStar
  vBar_lt_t : vBar < t
  t_lt_b₀ : t < b₀
  old_match : ∀ v ∈ Icc a t,
    g v = (S b₀).lam a v ∧
      hEdge v = (S b₀).alpha a v / (S b₀).lam a v ∧
      rEdge v = C1Solution.canonicalRadius (S b₀) (a, v)
  radius_axis : rEdge a = 0
  radius_deriv : ∀ v ∈ Ioo a vStar, HasDerivAt rEdge (g v) v
  radius_primitive : ∀ v ∈ Icc a vStar,
    rEdge v = ∫ s in a..v, g s

/-- Every fixed `0<a<vBar<vStar` has the complete off-axis terminal
construction, with no incoming boundedness hypothesis. The incoming bound follows from the off-axis strip estimates. -/
theorem exists_offAxisTerminalC1Packet
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
    Nonempty (OffAxisTerminalC1Packet a vBar vStar S) := by
  obtain ⟨T⟩ := exists_offAxisTerminalTraces
    hu₀ ha haBar hBarStar hα hfamily hε1 htail
  obtain ⟨P, hPcont, hPmatch⟩ :=
    exists_alphaPrime_terminal_trace_on_rectangle
      ha haBar hBarStar hα hfamily T
  obtain ⟨L, hLcont, hLmatch⟩ :=
    exists_lambdaV_terminal_trace_on_rectangle
      ha haBar hBarStar hfamily T
  obtain ⟨c, Cderiv, H, hc, hCderiv, hH,
    g, hEdge, hg, hh, hga, hbounds, htop,
    b₀, t, hb₀, hBart, htb₀, hold⟩ :=
    T.exists_compact_edge_data_with_bounds ha haBar hBarStar hfamily
      hPcont hLcont hPmatch hLmatch
  obtain ⟨rEdge, hr, hrAxis, hrTop, hrOld, hrDeriv, hrPrim⟩ :=
    T.exists_compact_radius_edge ha haBar hBarStar hfamily
      hg (fun v hv => (htop v hv).1)
      hb₀ hBart htb₀ (fun v hv => (hold v hv).1)
  refine ⟨{
    state := T, alphaPrimeTrace := P, lambdaVTrace := L,
    alphaPrime_cont := hPcont, lambdaV_cont := hLcont,
    alphaPrime_match := hPmatch, lambdaV_match := hLmatch,
    c := c, Cderiv := Cderiv, H := H,
    c_pos := hc, Cderiv_nonneg := hCderiv, H_nonneg := hH,
    g := g, hEdge := hEdge, rEdge := rEdge,
    g_c1 := hg.contDiffOn, h_c1 := hh.contDiffOn,
    r_c1 := hr.contDiffOn, g_axis_pos := hga,
    edge_bounds := hbounds,
    top_match := by
      intro v hv
      exact ⟨(htop v hv).1, (htop v hv).2, hrTop v hv⟩,
    b₀ := b₀, t := t, b₀_mem := hb₀,
    vBar_lt_t := hBart, t_lt_b₀ := htb₀,
    old_match := by
      intro v hv
      exact ⟨(hold v hv).1, (hold v hv).2, hrOld v hv⟩,
    radius_axis := hrAxis, radius_deriv := hrDeriv,
    radius_primitive := hrPrim
  }⟩

end ChristodoulouBV.Uniqueness

end
