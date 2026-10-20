module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisEdgeC1
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.OverlappingCompactC1
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# A compact C¹ characteristic edge from the old family

One finite old member supplies the interval adjacent to the axis. The
Volterra traces supply the terminal part. They agree on an open overlap.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The old family and the off-axis terminal derivative traces give global
`C¹` edge functions on `[a,vStar]`, with positive outgoing expansion. -/
theorem OffAxisTerminalTraces.exists_compact_edge_data
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (T : OffAxisTerminalTraces a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    {P L : ℝ × ℝ → ℝ}
    (hPcont : ContinuousOn P (Icc 0 a ×ˢ Icc vBar vStar))
    (hLcont : ContinuousOn L (Icc 0 a ×ˢ Icc vBar vStar))
    (hPmatch : ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar vStar,
      P (u, v) =
        deriv (fun t =>
          (S ((v + vStar) / 2)).alpha u t /
            (S ((v + vStar) / 2)).lam u t) v /
          (S ((v + vStar) / 2)).lam u v)
    (hLmatch : ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar vStar,
      L (u, v) = deriv ((S ((v + vStar) / 2)).lam u) v) :
    ∃ c : ℝ, 0 < c ∧ ∃ g hEdge : ℝ → ℝ,
      ContDiff ℝ 1 g ∧ ContDiff ℝ 1 hEdge ∧
      (∀ v ∈ Icc a vStar, c ≤ g v) ∧
      (∀ v ∈ Icc vBar vStar,
        g v = T.lam (a, v) ∧ hEdge v = T.quotient (a, v)) ∧
      ∃ b₀ t : ℝ, b₀ ∈ Ioo (0 : ℝ) vStar ∧ vBar < t ∧ t < b₀ ∧
        (∀ v ∈ Icc a t,
          g v = (S b₀).lam a v ∧
          hEdge v = (S b₀).alpha a v / (S b₀).lam a v) := by
  let b₀ : ℝ := (vBar + vStar) / 2
  let t : ℝ := (vBar + b₀) / 2
  let B : ℝ := (t + b₀) / 2
  have hBarb₀ : vBar < b₀ := by dsimp [b₀]; linarith only [hBarStar]
  have hb₀Star : b₀ < vStar := by dsimp [b₀]; linarith only [hBarStar]
  have hb₀ : b₀ ∈ Ioo (0 : ℝ) vStar :=
    ⟨(ha.trans haBar).trans hBarb₀, hb₀Star⟩
  have hBart : vBar < t := by dsimp [t]; linarith only [hBarb₀]
  have htb₀ : t < b₀ := by dsimp [t]; linarith only [hBarb₀]
  have htStar : t < vStar := htb₀.trans hb₀Star
  have hat : a < t := haBar.trans hBart
  have hB : 0 < B := by dsimp [B]; linarith only [ha, hat, htb₀]
  have hBb₀ : B < b₀ := by dsimp [B]; linarith only [htb₀]
  have htB : t < B := by dsimp [B]; linarith only [htb₀]
  let H := (hfamily b₀ hb₀).1
  have hmap : MapsTo (fun v : ℝ => (a, v)) (Icc a t)
      (closedCoordTriangle 0 B) := by
    intro v hv
    exact ⟨ha.le, hv.1, hv.2.trans htB.le⟩
  have hLamOld : ContDiffOn ℝ 1 ((S b₀).lam a) (Icc a t) :=
    (C1Solution.five_fields_contDiffOn hB hBb₀ H).1.comp
      (contDiff_const.prodMk contDiff_id).contDiffOn hmap
  have hQuotOld : ContDiffOn ℝ 1
      (fun v => (S b₀).alpha a v / (S b₀).lam a v) (Icc a t) :=
    (C1Solution.alpha_div_lam_contDiffOn hB hBb₀ H).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn hmap
  obtain ⟨hLamTop, hQuotTop, _⟩ :=
    T.compact_edge_c1 ha haBar hBarStar hfamily
      hPcont hLcont hPmatch hLmatch
  have haI : a ∈ Icc 0 a := ⟨ha.le, le_rfl⟩
  have hLamOverlap : ∀ v ∈ Icc vBar t,
      (S b₀).lam a v = T.lam (a, v) := by
    intro v hv
    exact ((T.match_old b₀ hb₀ a haI v ⟨hv.1, hv.2.trans_lt htb₀⟩).2.2.1).symm
  have hQuotOverlap : ∀ v ∈ Icc vBar t,
      (S b₀).alpha a v / (S b₀).lam a v = T.quotient (a, v) := by
    intro v hv
    exact ((T.match_old b₀ hb₀ a haI v ⟨hv.1, hv.2.trans_lt htb₀⟩).2.2.2.2.2.2.2.2).symm
  obtain ⟨g, hg, hgOld, hgTop⟩ :=
    exists_contDiff_one_of_overlapping_compact_intervals
      haBar hBart htStar hLamOld hLamTop hLamOverlap
  obtain ⟨hEdge, hh, hhOld, hhTop⟩ :=
    exists_contDiff_one_of_overlapping_compact_intervals
      haBar hBart htStar hQuotOld hQuotTop hQuotOverlap
  obtain ⟨c₀, hc₀, hfloorOld⟩ :=
    C1Solution.exists_lam_lower_bound hB hBb₀ H
  let c : ℝ := min c₀ T.c
  have hc : 0 < c := lt_min hc₀ T.expansion_pos
  refine ⟨c, hc, g, hEdge, hg, hh, ?_, ?_, b₀, t,
    hb₀, hBart, htb₀, ?_⟩
  · intro v hv
    by_cases hvt : v ≤ t
    · have hvOld : v ∈ Icc a t := ⟨hv.1, hvt⟩
      rw [hgOld v hvOld]
      exact (min_le_left _ _).trans
        (hfloorOld (a, v) (hmap hvOld))
    · have hvTop : v ∈ Icc vBar vStar :=
        ⟨(hBart.trans (lt_of_not_ge hvt)).le, hv.2⟩
      rw [hgTop v hvTop]
      exact (min_le_right _ _).trans (T.floors a haI v hvTop).2.1
  · intro v hv
    exact ⟨hgTop v hv, hhTop v hv⟩
  · intro v hv
    exact ⟨hgOld v hv, hhOld v hv⟩

end ChristodoulouBV.Uniqueness

end
