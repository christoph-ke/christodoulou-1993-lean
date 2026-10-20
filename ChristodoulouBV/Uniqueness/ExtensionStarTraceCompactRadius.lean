module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceCompactEdge
import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarTransport
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# Compact terminal radius edge and its outgoing primitive

The canonical radius on a finite old member and the terminal radius trace
agree on an overlap. Their glued derivative is the compact expansion edge.
-/

public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- A globally C¹ radius edge matches the old and terminal radii and is the
primitive of the glued expansion edge. -/
theorem OffAxisTerminalTraces.exists_compact_radius_edge
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (T : OffAxisTerminalTraces a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgTop : ∀ v ∈ Icc vBar vStar, g v = T.lam (a, v))
    {b₀ t : ℝ} (hb₀ : b₀ ∈ Ioo (0 : ℝ) vStar)
    (hBart : vBar < t) (htb₀ : t < b₀)
    (hgOld : ∀ v ∈ Icc a t, g v = (S b₀).lam a v) :
    ∃ rEdge : ℝ → ℝ,
      ContDiff ℝ 1 rEdge ∧ rEdge a = 0 ∧
      (∀ v ∈ Icc vBar vStar, rEdge v = T.r (a, v)) ∧
      (∀ v ∈ Icc a t,
        rEdge v = C1Solution.canonicalRadius (S b₀) (a, v)) ∧
      (∀ v ∈ Ioo a vStar, HasDerivAt rEdge (g v) v) ∧
      ∀ v ∈ Icc a vStar, rEdge v = ∫ s in a..v, g s := by
  let B : ℝ := (t + b₀) / 2
  have hat : a < t := haBar.trans hBart
  have htStar : t < vStar := htb₀.trans hb₀.2
  have hB : 0 < B := by dsimp [B]; linarith only [ha, hat, htb₀]
  have hBb₀ : B < b₀ := by dsimp [B]; linarith only [htb₀]
  have htB : t < B := by dsimp [B]; linarith only [htb₀]
  let H := (hfamily b₀ hb₀).1
  have hmap : MapsTo (fun v : ℝ => (a, v)) (Icc a t)
      (closedCoordTriangle 0 B) := by
    intro v hv
    exact ⟨ha.le, hv.1, hv.2.trans htB.le⟩
  have hOld : ContDiffOn ℝ 1
      (fun v => C1Solution.canonicalRadius (S b₀) (a, v)) (Icc a t) :=
    (C1Solution.canonicalRadius_contDiffOn hB hBb₀ H).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn hmap
  have haI : a ∈ Icc 0 a := ⟨ha.le, le_rfl⟩
  have hTopVal : ContinuousOn (fun v => T.r (a, v)) (Icc vBar vStar) :=
    T.r_cont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨haI, hv⟩)
  have hTopDeriv : ContinuousOn (fun v => T.lam (a, v))
      (Icc vBar vStar) :=
    T.lam_cont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨haI, hv⟩)
  have hTop : ContDiffOn ℝ 1 (fun v => T.r (a, v))
      (Icc vBar vStar) :=
    contDiffOn_one_Icc_of_continuousOn_hasDerivAt_Ioo
      hBarStar hTopVal hTopDeriv
      (fun v hv => T.radius_terminal_edge_hasDerivAt ha haBar hfamily hv)
  have hOverlap : ∀ v ∈ Icc vBar t,
      C1Solution.canonicalRadius (S b₀) (a, v) = T.r (a, v) := by
    intro v hv
    have hcanon : C1Solution.canonicalRadius (S b₀) (a, v) =
        (S b₀).r a v :=
      C1Solution.canonicalRadius_eq_radius hB hBb₀ H ha.le
        (haBar.trans_le hv.1) (hv.2.trans htB.le)
    exact hcanon.trans
      ((T.match_old b₀ hb₀ a haI v ⟨hv.1, hv.2.trans_lt htb₀⟩).1).symm
  obtain ⟨rEdge, hrC1, hrOld, hrTop⟩ :=
    exists_contDiff_one_of_overlapping_compact_intervals
      haBar hBart htStar hOld hTop hOverlap
  have hrAxis : rEdge a = 0 := by
    rw [hrOld a ⟨le_rfl, hat.le⟩]
    exact (C1Solution.canonical_outgoing_axis (S b₀) a).1
  have hderiv : ∀ v ∈ Ioo a vStar, HasDerivAt rEdge (g v) v := by
    intro v hv
    by_cases hvt : v < t
    · have hp : (a, v) ∈ openDevelopment 0 b₀ :=
        ⟨⟨ha, hv.1.trans (hvt.trans htb₀)⟩,
          ⟨hv.1, hvt.trans htb₀⟩⟩
      have heq : rEdge =ᶠ[𝓝 v] (S b₀).r a := by
        filter_upwards [Ioo_mem_nhds hv.1 hvt] with w hw
        have hwOld : w ∈ Icc a t := ⟨hw.1.le, hw.2.le⟩
        rw [hrOld w hwOld]
        exact C1Solution.canonicalRadius_eq_radius hB hBb₀ H ha.le
          hw.1 (hw.2.trans htB).le
      have h := (radius_hasDerivAt_v_of_c1 H hp).congr_of_eventuallyEq heq
      rw [hgOld v ⟨hv.1.le, hvt.le⟩]
      exact h
    · have htV : t ≤ v := le_of_not_gt hvt
      have hvTop : v ∈ Ioo vBar vStar := ⟨hBart.trans_le htV, hv.2⟩
      have heq : rEdge =ᶠ[𝓝 v] (fun w => T.r (a, w)) := by
        filter_upwards [Ioo_mem_nhds hvTop.1 hvTop.2] with w hw
        exact hrTop w ⟨hw.1.le, hw.2.le⟩
      have h := (T.radius_terminal_edge_hasDerivAt ha haBar hfamily hvTop)
        |>.congr_of_eventuallyEq heq
      rw [hgTop v ⟨hvTop.1.le, hvTop.2.le⟩]
      exact h
  refine ⟨rEdge, hrC1, hrAxis, hrTop, hrOld, hderiv, ?_⟩
  intro v hv
  have hrcont : ContinuousOn rEdge (Icc a v) :=
    hrC1.continuous.continuousOn
  have hgcont : ContinuousOn g (Icc a v) :=
    hg.continuous.continuousOn
  have hint : IntervalIntegrable g volume a v :=
    hgcont.intervalIntegrable_of_Icc hv.1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hv.1 hrcont (by
      intro s hs
      exact hderiv s ⟨hs.1, hs.2.trans_le hv.2⟩) hint
  rw [hrAxis] at hFTC
  simpa only [sub_zero] using hFTC.symm

end ChristodoulouBV.Uniqueness

end
