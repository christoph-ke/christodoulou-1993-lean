module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceCompactEdge
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Bounds for compact terminal characteristic data

The glued edge functions are globally C¹, so their values and derivatives
have finite bounds on `[a,vStar]`.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The characteristic data consumed by compact-edge axis local existence:
positive `g`, C¹ regularity, and finite value/derivative bounds. -/
theorem OffAxisTerminalTraces.exists_compact_edge_data_with_bounds
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
    ∃ c Cderiv H : ℝ, 0 < c ∧ 0 ≤ Cderiv ∧ 0 ≤ H ∧
      ∃ g hEdge : ℝ → ℝ,
        ContDiff ℝ 1 g ∧
        ContDiff ℝ 1 hEdge ∧
        0 < g a ∧
        (∀ v ∈ Icc a vStar,
          c ≤ g v ∧ |deriv g v| ≤ Cderiv ∧
            |hEdge v| ≤ H ∧ |deriv hEdge v| ≤ H) ∧
        (∀ v ∈ Icc vBar vStar,
          g v = T.lam (a, v) ∧ hEdge v = T.quotient (a, v)) ∧
        ∃ b₀ t : ℝ, b₀ ∈ Ioo (0 : ℝ) vStar ∧ vBar < t ∧ t < b₀ ∧
          ∀ v ∈ Icc a t,
            g v = (S b₀).lam a v ∧
            hEdge v = (S b₀).alpha a v / (S b₀).lam a v := by
  obtain ⟨c, hc, g, hEdge, hg, hh, hfloor, htop,
    b₀, t, hb₀, hBart, htb₀, hOld⟩ :=
    T.exists_compact_edge_data ha haBar hBarStar hfamily
      hPcont hLcont hPmatch hLmatch
  have hab : a ≤ vStar := (haBar.trans hBarStar).le
  have haI : a ∈ Icc a vStar := ⟨le_rfl, hab⟩
  have hhc : ContinuousOn hEdge (Icc a vStar) := hh.continuous.continuousOn
  have hgd : ContinuousOn (deriv g) (Icc a vStar) :=
    (contDiff_one_iff_deriv.mp hg).2.continuousOn
  have hhd : ContinuousOn (deriv hEdge) (Icc a vStar) :=
    (contDiff_one_iff_deriv.mp hh).2.continuousOn
  obtain ⟨Cderiv, hCderiv⟩ := isCompact_Icc.exists_bound_of_continuousOn hgd
  obtain ⟨H₀, hH₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hhc
  obtain ⟨H₁, hH₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hhd
  have hCderiv0 : 0 ≤ Cderiv := (norm_nonneg _).trans (hCderiv a haI)
  have hH₀0 : 0 ≤ H₀ := (norm_nonneg _).trans (hH₀ a haI)
  let H : ℝ := max H₀ H₁
  have hH0 : 0 ≤ H := hH₀0.trans (le_max_left _ _)
  refine ⟨c, Cderiv, H, hc, hCderiv0, hH0,
    g, hEdge, hg, hh,
    hc.trans_le (hfloor a haI), ?_, htop,
    b₀, t, hb₀, hBart, htb₀, hOld⟩
  intro v hv
  refine ⟨hfloor v hv, ?_, ?_, ?_⟩
  · simpa only [Real.norm_eq_abs] using hCderiv v hv
  · have h : |hEdge v| ≤ H₀ := by
      simpa only [Real.norm_eq_abs] using hH₀ v hv
    exact h.trans (le_max_left _ _)
  · have h : |deriv hEdge v| ≤ H₁ := by
      simpa only [Real.norm_eq_abs] using hH₁ v hv
    exact h.trans (le_max_right _ _)

end ChristodoulouBV.Uniqueness

end
