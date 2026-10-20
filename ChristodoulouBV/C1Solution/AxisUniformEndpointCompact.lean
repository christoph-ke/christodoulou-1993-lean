module

public import ChristodoulouBV.C1Solution.AxisUniformEndpoint
public import ChristodoulouBV.C1Solution.AxisLocalExistenceCompactEdge
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.IntervalC1ExtensionBounds
import Mathlib.Tactic

/-!
# Prescribed axis endpoints from compact C¹ edge data

First-order continuation supplies the global representatives required by the
Picard box while preserving the original values and relative derivatives.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.C1Solution

open ChristodoulouBV.AxisPicard

/-- Uniform bounds on one compact physical incoming edge give a classical
solution at every prescribed endpoint inside the explicit common lifetime.
The incoming radius and scalar radius are their canonical primitives. -/
theorem exists_axis_triangle_solution_prescribed_compact
    {a L b c Clam H : ℝ} {g hEdge : ℝ → ℝ}
    (hg : ContDiffOn ℝ 1 g (Icc a (a + L)))
    (hh : ContDiffOn ℝ 1 hEdge (Icc a (a + L)))
    (hc : 0 < c) (hL : 0 < L)
    (hglo : ∀ v ∈ Icc a (a + L), c ≤ g v)
    (hgderiv : ∀ v ∈ Icc a (a + L),
      |derivWithin g (Icc a (a + L)) v| ≤ Clam)
    (hhval : ∀ v ∈ Icc a (a + L), |hEdge v| ≤ H)
    (hhderiv : ∀ v ∈ Icc a (a + L),
      |derivWithin hEdge (Icc a (a + L)) v| ≤ H)
    (hab : a < b) (hbL : b ≤ a + L)
    (hsmall : b - a ≤ uniformAxisLifetime c Clam H) :
    ∃ T : Fields,
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
  let J := intervalC1Extension hEdge a (a + L)
  have haL : a < a + L := by linarith only [hL]
  have hG : ContDiff ℝ 1 G := intervalC1Extension_c1 haL hg
  have hJ : ContDiff ℝ 1 J := intervalC1Extension_c1 haL hh
  have hGderiv (v : ℝ) (hv : v ∈ Icc a (a + L)) :
      |deriv G v| ≤ Clam := by
    rw [deriv_intervalC1Extension_eq haL hg hv]
    exact hgderiv v hv
  have hJderiv (v : ℝ) (hv : v ∈ Icc a (a + L)) :
      |deriv J v| ≤ H := by
    rw [deriv_intervalC1Extension_eq haL hh hv]
    exact hhderiv v hv
  have hGlo (v : ℝ) (hv : v ∈ Icc a (a + L)) : c ≤ G v := by
    rw [show G v = g v from intervalC1Extension_eq hv]
    exact hglo v hv
  have hJval (v : ℝ) (hv : v ∈ Icc a (a + L)) : |J v| ≤ H := by
    rw [show J v = hEdge v from intervalC1Extension_eq hv]
    exact hhval v hv
  obtain ⟨T, hclass, hsign, hedge, hratio, hpsi⟩ :=
    exists_axis_triangle_solution_prescribed_global hG hJ hc hL
      hGlo hGderiv hJval hJderiv hab hbL hsmall
  have hGa : G a = g a := intervalC1Extension_eq ⟨le_rfl, haL.le⟩
  refine ⟨T, hclass, ?_, ?_, ?_, ?_⟩
  · simpa only [hGa] using hsign
  · intro v hv
    have hvL : v ∈ Icc a (a + L) := ⟨hv.1, hv.2.trans hbL⟩
    have hGv : G v = g v := intervalC1Extension_eq hvL
    have hJv : J v = hEdge v := intervalC1Extension_eq hvL
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
    · simpa only [hGv, hJv] using hα
  · intro v hv
    have hvL : v ∈ Icc a (a + L) := ⟨hv.1, hv.2.trans hbL⟩
    simpa only [show J v = hEdge v from intervalC1Extension_eq hvL] using hratio v hv
  · intro v hv
    calc
      T.r a v * T.phi a v = ∫ s in a..v, G s * J s := hpsi v hv
      _ = ∫ s in a..v, g s * hEdge s := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hs' : s ∈ Icc a v := by
          simpa only [uIcc_of_le hv.1] using hs
        have hsL : s ∈ Icc a (a + L) :=
          ⟨hs'.1, (hs'.2.trans hv.2).trans hbL⟩
        change G s * J s = g s * hEdge s
        rw [show G s = g s from intervalC1Extension_eq hsL,
          show J s = hEdge s from intervalC1Extension_eq hsL]

/-- A supplied canonical radius trace is reproduced exactly by the
prescribed-endpoint solution. -/
theorem exists_axis_triangle_solution_prescribed_compact_with_radius
    {a L b c Clam H : ℝ} {rEdge g hEdge : ℝ → ℝ}
    (hr : ContDiffOn ℝ 1 rEdge (Icc a (a + L)))
    (hg : ContDiffOn ℝ 1 g (Icc a (a + L)))
    (hh : ContDiffOn ℝ 1 hEdge (Icc a (a + L)))
    (hrAxis : rEdge a = 0)
    (hrv : ∀ v ∈ Ioo a (a + L), HasDerivAt rEdge (g v) v)
    (hc : 0 < c) (hL : 0 < L)
    (hglo : ∀ v ∈ Icc a (a + L), c ≤ g v)
    (hgderiv : ∀ v ∈ Icc a (a + L),
      |derivWithin g (Icc a (a + L)) v| ≤ Clam)
    (hhval : ∀ v ∈ Icc a (a + L), |hEdge v| ≤ H)
    (hhderiv : ∀ v ∈ Icc a (a + L),
      |derivWithin hEdge (Icc a (a + L)) v| ≤ H)
    (hab : a < b) (hbL : b ≤ a + L)
    (hsmall : b - a ≤ uniformAxisLifetime c Clam H) :
    ∃ T : Fields,
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
  obtain ⟨T, hclass, hsign, hedge, hratio, hpsi⟩ :=
    exists_axis_triangle_solution_prescribed_compact hg hh hc hL
      hglo hgderiv hhval hhderiv hab hbL hsmall
  refine ⟨T, hclass, hsign, ?_, hratio, hpsi⟩
  intro v hv
  obtain ⟨hrT, hlT, hαT⟩ := hedge v hv
  have hvL : v ∈ Icc a (a + L) := ⟨hv.1, hv.2.trans hbL⟩
  rw [← edge_radius_eq_integral_of_contDiffOn hr hg hrAxis hrv hvL] at hrT
  exact ⟨hrT, hlT, hαT⟩

end ChristodoulouBV.C1Solution

end
