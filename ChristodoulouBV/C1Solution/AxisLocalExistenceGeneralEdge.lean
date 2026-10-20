module

public import ChristodoulouBV.C1Solution.AxisLocalExistence
public import ChristodoulouBV.C1Solution.AxisLocalExistenceEdge
import ChristodoulouBV.C1Solution.AxisMassDefect
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Normalized Picard reconstruction for a positive incoming edge

Physical radial scaling puts an arbitrary positive outgoing expansion into
the numerical Picard box on a short edge. Compactness supplies the remaining
edge value and derivative bounds.
-/

public section

noncomputable section

open Set
open scoped Topology

namespace ChristodoulouBV.AxisPicard

/-- A relative `C¹` jet on a translated axis triangle gives the ordinary
vertical derivative at each interior point of its incoming edge. -/
theorem vertical_hasDerivAt_axis_edge {a b : ℝ}
    {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b))
    {v : ℝ} (hv : v ∈ Ioo a b) :
    HasDerivAt (fun t => f (a, t))
      ((fderivWithin ℝ f (closedCoordTriangle a b) (a, v)) (0, 1)) v := by
  have hp : (a, v) ∈ closedCoordTriangle a b := by
    change a ≤ a ∧ a ≤ v ∧ v ≤ b
    exact ⟨le_rfl, hv.1.le, hv.2.le⟩
  have hmap : MapsTo (fun t : ℝ => (a, t)) (Icc a b)
      (closedCoordTriangle a b) := by
    intro t ht
    change a ≤ a ∧ a ≤ t ∧ t ≤ b
    exact ⟨le_rfl, ht.1, ht.2⟩
  have hpath : HasDerivWithinAt (fun t : ℝ => (a, t)) (0, 1)
      (Icc a b) v :=
    ((hasDerivAt_const v a).prodMk (hasDerivAt_id' v)).hasDerivWithinAt
  have hfield := (hf.differentiableOn (by norm_num) (a, v) hp).hasFDerivWithinAt
  have h := hfield.comp_hasDerivWithinAt v hpath hmap
  exact h.hasDerivAt (Icc_mem_nhds hv.1 hv.2)

/-- A relative vertical jet is an ordinary vertical derivative at every
point of a translated open axis development, including its incoming edge. -/
theorem vertical_hasDerivAt_axis_development {a b u v : ℝ}
    {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b))
    (hp : a ≤ u ∧ u < v ∧ v < b) :
    HasDerivAt (fun t => f (u, t))
      ((fderivWithin ℝ f (closedCoordTriangle a b) (u, v)) (0, 1)) v := by
  rcases lt_or_eq_of_le hp.1 with hu | hu
  · apply vertical_hasDerivAt_of_triangle_c1 hf
    exact ⟨hu, hp.2.1, hp.2.2⟩
  · subst u
    exact vertical_hasDerivAt_axis_edge hf ⟨hp.2.1, hp.2.2⟩

/-- Positive C¹ outgoing expansion and C¹ scalar edge data give a bounded
normalized Picard reconstruction on a positive subinterval of any prescribed
edge. The expansion is multiplied by `k`; the normalized scalar datum is
unchanged. -/
theorem exists_normalized_reconstructed_edge {a L : ℝ} {g hEdge : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 hEdge)
    (hga : 0 < g a) (hL : 0 < L) :
    ∃ k b M : ℝ, 0 < k ∧ a < b ∧ b ≤ a + L ∧ 1 ≤ M ∧
      k * g a = 1 / 2 ∧ b - a ≤ (numericalLedger M).lifetime M ∧
      ∃ x : Box a b M (fun v => k * g v) hEdge,
        x.IsTriangleFixedPoint := by
  obtain ⟨k, L₀, hk, hL₀, hka, hnorm⟩ :=
    exists_normalized_positive_edge hg hga
  let L₁ := min L L₀
  have hL₁ : 0 < L₁ := lt_min hL hL₀
  have hL₁L : L₁ ≤ L := min_le_left _ _
  have hL₁L₀ : L₁ ≤ L₀ := min_le_right _ _
  let gNorm : ℝ → ℝ := fun v => k * g v
  have hgNorm : ContDiff ℝ 1 gNorm := contDiff_const.mul hg
  have hKcompact : IsCompact (Icc a (a + L₁)) := isCompact_Icc
  obtain ⟨Cg, hCg⟩ := hKcompact.exists_bound_of_continuousOn
    hgNorm.continuous_deriv_one.continuousOn
  obtain ⟨Ch, hCh⟩ := hKcompact.exists_bound_of_continuousOn
    hh.continuous.continuousOn
  obtain ⟨Ch', hCh'⟩ := hKcompact.exists_bound_of_continuousOn
    hh.continuous_deriv_one.continuousOn
  let M := max 1 (max Cg (max Ch Ch'))
  have hM : 1 ≤ M := le_max_left _ _
  have hCgM : Cg ≤ M :=
    (le_max_left Cg (max Ch Ch')).trans (le_max_right 1 _)
  have hChM : Ch ≤ M :=
    ((le_max_left Ch Ch').trans (le_max_right Cg _)).trans
      (le_max_right 1 _)
  have hCh'M : Ch' ≤ M :=
    ((le_max_right Ch Ch').trans (le_max_right Cg _)).trans
      (le_max_right 1 _)
  have D : EdgeData a (a + L₁) M gNorm hEdge := {
    g_c1 := hgNorm
    h_c1 := hh
    g_lower := by
      intro v hv
      have hv₀ : v ∈ Icc a (a + L₀) :=
        ⟨hv.1, hv.2.trans (by linarith only [hL₁L₀])⟩
      exact (hnorm v hv₀).1
    g_upper := by
      intro v hv
      have hv₀ : v ∈ Icc a (a + L₀) :=
        ⟨hv.1, hv.2.trans (by linarith only [hL₁L₀])⟩
      exact (hnorm v hv₀).2
    g_deriv_bound := by
      intro v hv
      have h : |deriv gNorm v| ≤ Cg := by
        simpa only [Real.norm_eq_abs] using hCg v hv
      exact h.trans hCgM
    h_bound := by
      intro v hv
      have h : |hEdge v| ≤ Ch := by
        simpa only [Real.norm_eq_abs] using hCh v hv
      exact h.trans hChM
    h_deriv_bound := by
      intro v hv
      have h : |deriv hEdge v| ≤ Ch' := by
        simpa only [Real.norm_eq_abs] using hCh' v hv
      exact h.trans hCh'M }
  let w := min L₁ ((numericalLedger M).lifetime M)
  let b := a + w
  have hw : 0 < w := lt_min hL₁ (numerical_lifetime_pos hM)
  have hab : a < b := by dsimp [b]; linarith only [hw]
  have hbL : b ≤ a + L := by
    have hbL₁ : b ≤ a + L₁ := by
      dsimp [b, w]
      linarith only [min_le_left L₁ ((numericalLedger M).lifetime M)]
    linarith only [hbL₁, hL₁L]
  have hsmall : b - a ≤ (numericalLedger M).lifetime M := by
    dsimp [b, w]
    linarith only [min_le_right L₁ ((numericalLedger M).lifetime M)]
  have hbL₁ : b ≤ a + L₁ := by
    dsimp [b, w]
    linarith only [min_le_left L₁ ((numericalLedger M).lifetime M)]
  have D' : EdgeData a b M gNorm hEdge := {
    g_c1 := D.g_c1
    h_c1 := D.h_c1
    g_lower := fun v hv => D.g_lower v ⟨hv.1, hv.2.trans hbL₁⟩
    g_upper := fun v hv => D.g_upper v ⟨hv.1, hv.2.trans hbL₁⟩
    g_deriv_bound := fun v hv => D.g_deriv_bound v ⟨hv.1, hv.2.trans hbL₁⟩
    h_bound := fun v hv => D.h_bound v ⟨hv.1, hv.2.trans hbL₁⟩
    h_deriv_bound := fun v hv => D.h_deriv_bound v ⟨hv.1, hv.2.trans hbL₁⟩ }
  obtain ⟨x, hfixed, _⟩ := exists_reconstructed_fields D' hab hM hsmall
  exact ⟨k, b, M, hk, hab, hbL, hM, hka, hsmall, x, hfixed⟩

end ChristodoulouBV.AxisPicard

end
