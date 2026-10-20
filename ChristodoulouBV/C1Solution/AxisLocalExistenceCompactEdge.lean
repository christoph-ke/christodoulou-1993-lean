module

public import ChristodoulouBV.C1Solution.AxisLocalExistenceEdgeTheorem
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.IntervalC1Extension
import Mathlib.Tactic

/-!
# Axis local existence from compact-interval edge data

The incoming edge data need only be `C¹` on the finite interval supplied by
the old solution. First-order endpoint continuation supplies the global
representatives used by the Picard construction.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.C1Solution

/-- Positive outgoing expansion and scalar amplitude that are `C¹` only on
the prescribed compact edge give a short classical axis triangle. -/
theorem exists_axis_triangle_solution_of_compact_edge {a L : ℝ}
    {g hEdge : ℝ → ℝ}
    (hg : ContDiffOn ℝ 1 g (Icc a (a + L)))
    (hh : ContDiffOn ℝ 1 hEdge (Icc a (a + L)))
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
  let G := intervalC1Extension g a (a + L)
  let H := intervalC1Extension hEdge a (a + L)
  have haL : a < a + L := by linarith only [hL]
  have hG : ContDiff ℝ 1 G := intervalC1Extension_c1 haL hg
  have hH : ContDiff ℝ 1 H := intervalC1Extension_c1 haL hh
  have hGa : G a = g a := intervalC1Extension_eq ⟨le_rfl, haL.le⟩
  obtain ⟨b, hab, hbL, T, hclass, hsign, hedge, hratio, hpsi⟩ :=
    exists_axis_triangle_solution_of_edge hG hH (hGa.symm ▸ hga) hL
  refine ⟨b, hab, hbL, T, hclass, ?_, ?_, ?_, ?_⟩
  · simpa only [hGa] using hsign
  · intro v hv
    have hvL : v ∈ Icc a (a + L) := ⟨hv.1, hv.2.trans hbL⟩
    have hGv : G v = g v := intervalC1Extension_eq hvL
    have hHv : H v = hEdge v := intervalC1Extension_eq hvL
    obtain ⟨hr, hl, hα⟩ := hedge v hv
    refine ⟨?_, hl.trans hGv, ?_⟩
    · calc
        T.r a v = ∫ s in a..v, G s := hr
        _ = ∫ s in a..v, g s := by
          apply intervalIntegral.integral_congr
          intro s hs
          have hs' : s ∈ Icc a v := by
            simpa only [uIcc_of_le hv.1] using hs
          exact intervalC1Extension_eq ⟨hs'.1, hs'.2.trans hvL.2⟩
    · simpa only [hGv, hHv] using hα
  · intro v hv
    have hvL : v ∈ Icc a (a + L) := ⟨hv.1, hv.2.trans hbL⟩
    simpa only [show H v = hEdge v from intervalC1Extension_eq hvL] using hratio v hv
  · intro v hv
    calc
      T.r a v * T.phi a v = ∫ s in a..v, G s * H s := hpsi v hv
      _ = ∫ s in a..v, g s * hEdge s := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hs' : s ∈ Icc a v := by
          simpa only [uIcc_of_le hv.1] using hs
        have hsL : s ∈ Icc a (a + L) := ⟨hs'.1, (hs'.2.trans hv.2).trans hbL⟩
        change G s * H s = g s * hEdge s
        rw [show G s = g s from intervalC1Extension_eq hsL,
          show H s = hEdge s from intervalC1Extension_eq hsL]

/-- A compact-edge `C¹` radius whose axis value is zero and whose outgoing
derivative is `g` is the canonical primitive of `g`. -/
theorem edge_radius_eq_integral_of_contDiffOn {a L : ℝ}
    {rEdge g : ℝ → ℝ}
    (hr : ContDiffOn ℝ 1 rEdge (Icc a (a + L)))
    (hg : ContDiffOn ℝ 1 g (Icc a (a + L)))
    (hrAxis : rEdge a = 0)
    (hrv : ∀ v ∈ Ioo a (a + L), HasDerivAt rEdge (g v) v)
    {v : ℝ} (hv : v ∈ Icc a (a + L)) :
    rEdge v = ∫ s in a..v, g s := by
  have hsub : Icc a v ⊆ Icc a (a + L) :=
    fun _ ht => ⟨ht.1, ht.2.trans hv.2⟩
  have hrcont : ContinuousOn rEdge (Icc a v) := hr.continuousOn.mono hsub
  have hgcont : ContinuousOn g (Icc a v) := hg.continuousOn.mono hsub
  have hint : IntervalIntegrable g MeasureTheory.volume a v :=
    hgcont.intervalIntegrable_of_Icc hv.1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hv.1 hrcont (by
      intro s hs
      exact hrv s ⟨hs.1, hs.2.trans_le hv.2⟩) hint
  rw [hrAxis] at hFTC
  simpa only [sub_zero] using hFTC.symm

/-- The compact-edge theorem accepts an independently supplied radius
trace when it has the axis value and outgoing derivative required by the
field equations. -/
theorem exists_axis_triangle_solution_of_compact_edge_with_radius
    {a L : ℝ} {rEdge g hEdge : ℝ → ℝ}
    (hr : ContDiffOn ℝ 1 rEdge (Icc a (a + L)))
    (hg : ContDiffOn ℝ 1 g (Icc a (a + L)))
    (hh : ContDiffOn ℝ 1 hEdge (Icc a (a + L)))
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
  obtain ⟨b, hab, hbL, T, hclass, hsign, hedge, hratio, hpsi⟩ :=
    exists_axis_triangle_solution_of_compact_edge hg hh hga hL
  refine ⟨b, hab, hbL, T, hclass, hsign, ?_, hratio, hpsi⟩
  intro v hv
  obtain ⟨hrT, hlT, hαT⟩ := hedge v hv
  have hvL : v ∈ Icc a (a + L) := ⟨hv.1, hv.2.trans hbL⟩
  rw [← edge_radius_eq_integral_of_contDiffOn hr hg hrAxis hrv hvL] at hrT
  exact ⟨hrT, hlT, hαT⟩

end ChristodoulouBV.C1Solution

end
