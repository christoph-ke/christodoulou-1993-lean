module

public import ChristodoulouBV.C1Solution.AxisLocalExistencePhysical
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Local classical existence from a positive incoming edge

The edge radius is the integral of its prescribed outgoing expansion, so its
axis value is zero. The edge scalar amplitude is the ratio alpha / lambda.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.C1Solution

open ChristodoulouBV.AxisPicard

/-- On the incoming edge, the scalar radius is the primitive of alpha,
with zero value at the axis. -/
theorem AxisClassicalSolution.psi_edge_integral {a b : ℝ} {T : Fields}
    (H : AxisClassicalSolution a b T) {G : ℝ → ℝ}
    (hα : ∀ v ∈ Icc a b, T.alpha a v = G v)
    {v : ℝ} (hv : v ∈ Icc a b) :
    T.r a v * T.phi a v = ∫ s in a..v, G s := by
  have hmap : MapsTo (fun t : ℝ => (a, t)) (Icc a v)
      (closedCoordTriangle a b) := by
    intro t ht
    change a ≤ a ∧ a ≤ t ∧ t ≤ b
    exact ⟨le_rfl, ht.1, ht.2.trans hv.2⟩
  have hψ : ContinuousOn (fun t : ℝ => T.r a t * T.phi a t) (Icc a v) :=
    (H.r_c1.mul H.phi_c1).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap
  have hαcont : ContinuousOn (T.alpha a) (Icc a v) :=
    H.alpha_c1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap
  have hint : IntervalIntegrable (T.alpha a) MeasureTheory.volume a v :=
    hαcont.intervalIntegrable_of_Icc hv.1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hv.1 hψ (by
      intro t ht
      apply H.psi_v a t
      change a ≤ a ∧ a < t ∧ t < b
      exact ⟨le_rfl, ht.1, ht.2.trans_le hv.2⟩) hint
  have haxis : T.r a a = 0 := H.r_axis a ⟨le_rfl, hv.1.trans hv.2⟩
  have hInt : (∫ s in a..v, T.alpha a s) = ∫ s in a..v, G s := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc a v := by simpa only [uIcc_of_le hv.1] using hs
    exact hα s ⟨hs'.1, hs'.2.trans hv.2⟩
  calc
    T.r a v * T.phi a v = T.r a v * T.phi a v - T.r a a * T.phi a a := by
      rw [haxis]
      ring
    _ = ∫ s in a..v, T.alpha a s := hFTC.symm
    _ = ∫ s in a..v, G s := hInt

/-- Given positive C¹ outgoing expansion g and C¹ scalar amplitude hEdge,
there is a short adjacent-axis triangle with all classical equations, the
physical sign bounds, and the exact incoming trace. The radius trace is the
axis-compatible primitive of g and alpha equals g times hEdge. -/
theorem exists_axis_triangle_solution_of_edge {a L : ℝ}
    {g hEdge : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 hEdge)
    (hga : 0 < g a) (hL : 0 < L) :
    ∃ b : ℝ, a < b ∧ b ≤ a + L ∧ ∃ T : Fields,
      AxisClassicalSolution a b T ∧
      (∀ p ∈ closedCoordTriangle a b,
        g a / 2 ≤ T.lam p.1 p.2 ∧
        -(3 * g a / 2) ≤ T.nu p.1 p.2 ∧
        T.nu p.1 p.2 ≤ -(g a / 2) ∧
        0 ≤ 2 * T.m p.1 p.2 / T.r p.1 p.2 ∧
        2 * T.m p.1 p.2 / T.r p.1 p.2 ≤ 1 / 4) ∧
      (∀ v ∈ Icc a b,
        T.r a v = ∫ s in a..v, g s ∧
        T.lam a v = g v ∧ T.alpha a v = g v * hEdge v) ∧
      (∀ v ∈ Icc a b, T.alpha a v / T.lam a v = hEdge v) ∧
      (∀ v ∈ Icc a b,
        T.r a v * T.phi a v = ∫ s in a..v, g s * hEdge s) := by
  obtain ⟨k, b, hk, hab, hbL, hka, T,
    _, _, _, _, _, _, _, hsign, _, hedge, hclass⟩ :=
    exists_physical_reconstructed_edge hg hh hga hL
  have hkne : k ≠ 0 := ne_of_gt hk
  have hkinv : 1 / k = 2 * g a := by
    apply (div_eq_iff hkne).2
    nlinarith only [hka]
  have hquarter : (1 / (4 * k) : ℝ) = g a / 2 := by
    calc
      1 / (4 * k) = (1 / k) / 4 := by field_simp [hkne]
      _ = g a / 2 := by rw [hkinv]; ring
  have hthree : (3 / (4 * k) : ℝ) = 3 * g a / 2 := by
    calc
      3 / (4 * k) = 3 * (1 / k) / 4 := by field_simp [hkne]
      _ = 3 * g a / 2 := by rw [hkinv]; ring
  refine ⟨b, hab, hbL, T, hclass, ?_, hedge, ?_, ?_⟩
  · intro p hp
    obtain ⟨hl, hnlo, hnhi, hmlo, hmhi⟩ := hsign p hp
    rw [hquarter] at hl hnhi
    rw [hthree] at hnlo
    exact ⟨hl, hnlo, hnhi, hmlo, hmhi⟩
  · intro v hv
    have hp : (a, v) ∈ closedCoordTriangle a b := by
      change a ≤ a ∧ a ≤ v ∧ v ≤ b
      exact ⟨le_rfl, hv.1, hv.2⟩
    have hlam := (hsign (a, v) hp).1
    have hgv : g v ≠ 0 := by
      have hvlam := (hedge v hv).2.1
      rw [hquarter, hvlam] at hlam
      exact ne_of_gt (lt_of_lt_of_le (by positivity) hlam)
    rw [(hedge v hv).2.1, (hedge v hv).2.2]
    field_simp [hgv]
  · intro v hv
    exact hclass.psi_edge_integral (fun s hs => (hedge s hs).2.2) hv

/-- A C¹ edge radius with zero axis value and outgoing derivative g is
the canonical primitive of g. -/
theorem edge_radius_eq_integral {a L : ℝ} {rEdge g : ℝ → ℝ}
    (hr : ContDiff ℝ 1 rEdge) (hg : ContDiff ℝ 1 g)
    (hrAxis : rEdge a = 0)
    (hrv : ∀ v ∈ Ioo a (a + L), HasDerivAt rEdge (g v) v)
    {v : ℝ} (hv : v ∈ Icc a (a + L)) :
    rEdge v = ∫ s in a..v, g s := by
  have hint : IntervalIntegrable g MeasureTheory.volume a v :=
    hg.continuous.continuousOn.intervalIntegrable_of_Icc hv.1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hv.1 hr.continuous.continuousOn (by
      intro s hs
      exact hrv s ⟨hs.1, hs.2.trans_le hv.2⟩) hint
  rw [hrAxis] at hFTC
  simpa only [sub_zero] using hFTC.symm

/-- An explicitly prescribed C¹ radius trace can be used when its axis
value is zero and its outgoing derivative is the prescribed expansion. -/
theorem exists_axis_triangle_solution_of_edge_with_radius {a L : ℝ}
    {rEdge g hEdge : ℝ → ℝ}
    (hr : ContDiff ℝ 1 rEdge)
    (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 hEdge)
    (hrAxis : rEdge a = 0)
    (hrv : ∀ v ∈ Ioo a (a + L), HasDerivAt rEdge (g v) v)
    (hga : 0 < g a) (hL : 0 < L) :
    ∃ b : ℝ, a < b ∧ b ≤ a + L ∧ ∃ T : Fields,
      AxisClassicalSolution a b T ∧
      (∀ p ∈ closedCoordTriangle a b,
        g a / 2 ≤ T.lam p.1 p.2 ∧
        -(3 * g a / 2) ≤ T.nu p.1 p.2 ∧
        T.nu p.1 p.2 ≤ -(g a / 2) ∧
        0 ≤ 2 * T.m p.1 p.2 / T.r p.1 p.2 ∧
        2 * T.m p.1 p.2 / T.r p.1 p.2 ≤ 1 / 4) ∧
      (∀ v ∈ Icc a b,
        T.r a v = rEdge v ∧
        T.lam a v = g v ∧ T.alpha a v = g v * hEdge v) ∧
      (∀ v ∈ Icc a b, T.alpha a v / T.lam a v = hEdge v) ∧
      (∀ v ∈ Icc a b,
        T.r a v * T.phi a v = ∫ s in a..v, g s * hEdge s) := by
  obtain ⟨b, hab, hbL, T, hclass, hsign, hedge, hhtrace, hpsitrace⟩ :=
    exists_axis_triangle_solution_of_edge hg hh hga hL
  refine ⟨b, hab, hbL, T, hclass, hsign, ?_, hhtrace, hpsitrace⟩
  intro v hv
  obtain ⟨hrT, hlT, haT⟩ := hedge v hv
  have hvL : v ∈ Icc a (a + L) := ⟨hv.1, hv.2.trans hbL⟩
  rw [← edge_radius_eq_integral hr hg hrAxis hrv hvL] at hrT
  exact ⟨hrT, hlT, haT⟩

end ChristodoulouBV.C1Solution

end
