module

public import ChristodoulouBV.Uniqueness.RouteBAssemblyShrink
public import ChristodoulouBV.C1Solution.AxisUniformEndpoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The prescribed Route B axis triangle from joined edge data

The uniform lifetime is fixed before the incoming cutoff. Once the lower
edge is joined, its C¹ bounds persist on a short segment beyond the old
terminal line. The prescribed endpoint theorem then gives the axis triangle.
-/

public section

open Set ChristodoulouBV.AxisPicard
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- Joined old and lower physical edge data produce a prescribed axis
triangle beyond `vStar`. Its old incoming trace retains the construction's radius
and scalar-radius primitives, while its new expansion and quotient match the
lower edge. -/
theorem OffAxisTerminalC1Packet.exists_routeB_axis_from_joined_edge
    {a vBar vStar η c Clam H : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (_ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hη : 0 < η) (hc : 0 < c)
    (hgap : vStar - a <
      uniformAxisLifetime (c / 2) (Clam + 1) (H + 1) / 2)
    (hηhalf : η <
      uniformAxisLifetime (c / 2) (Clam + 1) (H + 1) / 2)
    (hOldBounds : ∀ v ∈ Icc a vStar,
      c ≤ intervalC1Extension P.g a vStar v ∧
      |deriv (intervalC1Extension P.g a vStar) v| ≤ Clam ∧
      |intervalC1Extension P.hEdge a vStar v| ≤ H ∧
      |deriv (intervalC1Extension P.hEdge a vStar) v| ≤ H)
    {g h : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h)
    (hOld : ∀ v ∈ Icc a vStar,
      g v = P.g v ∧ h v = P.hEdge v)
    {SLow : Fields}
    (hLow : ∀ v ∈ Icc vStar (vStar + η),
      g v = SLow.lam a v ∧
      h v = SLow.alpha a v / SLow.lam a v) :
    ∃ η' b' : ℝ, 0 < η' ∧ η' < η ∧
      b' = vStar + η' ∧ vStar < b' ∧
      b' - a ≤ uniformAxisLifetime (c / 2) (Clam + 1) (H + 1) ∧
      ∃ SAx : Fields,
        C1Solution.AxisClassicalSolution a b' SAx ∧
        (∀ p ∈ closedCoordTriangle a b',
          g a / 2 ≤ SAx.lam p.1 p.2 ∧
          SAx.nu p.1 p.2 ≤ -(g a / 2) ∧
          2 * SAx.m p.1 p.2 / SAx.r p.1 p.2 ≤ 1 / 4) ∧
        (∀ v ∈ Icc a vStar,
          SAx.r a v = P.rEdge v ∧
          SAx.r a v * SAx.phi a v =
            ∫ s in a..v, P.g s * P.hEdge s) ∧
        (∀ v ∈ Icc vStar b',
          SAx.lam a v = SLow.lam a v ∧
          SAx.alpha a v / SAx.lam a v =
            SLow.alpha a v / SLow.lam a v) := by
  have haStar : a < vStar := haBar.trans hBarStar
  have hOldEqG : EqOn (intervalC1Extension P.g a vStar) g
      (Icc a vStar) := by
    intro v hv
    rw [intervalC1Extension_eq hv]
    exact (hOld v hv).1.symm
  have hOldEqH : EqOn (intervalC1Extension P.hEdge a vStar) h
      (Icc a vStar) := by
    intro v hv
    rw [intervalC1Extension_eq hv]
    exact (hOld v hv).2.symm
  obtain ⟨η', hη', hη'η, hbds⟩ :=
    exists_short_joined_edge_bounds haStar hη hc hg hh
      hOldEqG hOldEqH hOldBounds
  let b' := vStar + η'
  have hStarb' : vStar < b' := by dsimp [b']; linarith only [hη']
  have hab' : a < b' := haStar.trans hStarb'
  have hwidth : b' - a ≤
      uniformAxisLifetime (c / 2) (Clam + 1) (H + 1) := by
    dsimp [b']
    linarith only [hgap, hη'η, hηhalf]
  have hL : 0 < b' - a := sub_pos.mpr hab'
  have htop : b' ≤ a + (b' - a) := by
    linarith
  have hfloor : ∀ v ∈ Icc a (a + (b' - a)), c / 2 ≤ g v := by
    intro v hv
    convert (hbds v (by simpa only [show a + (b' - a) = b' by ring] using hv)).1
  have hGderiv : ∀ v ∈ Icc a (a + (b' - a)),
      |deriv g v| ≤ Clam + 1 := by
    intro v hv
    exact (hbds v (by simpa only [show a + (b' - a) = b' by ring] using hv)).2.1
  have hHval : ∀ v ∈ Icc a (a + (b' - a)), |h v| ≤ H + 1 := by
    intro v hv
    exact (hbds v (by simpa only [show a + (b' - a) = b' by ring] using hv)).2.2.1
  have hHderiv : ∀ v ∈ Icc a (a + (b' - a)),
      |deriv h v| ≤ H + 1 := by
    intro v hv
    exact (hbds v (by simpa only [show a + (b' - a) = b' by ring] using hv)).2.2.2
  obtain ⟨SAx, hAxis, hBox, hedge, hquot, hpsi⟩ :=
    C1Solution.exists_axis_triangle_solution_prescribed_global
      hg hh (half_pos hc) hL hfloor hGderiv hHval hHderiv
      hab' htop hwidth
  refine ⟨η', b', hη', hη'η, rfl, hStarb', hwidth,
    SAx, hAxis, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hl, _, hn, _, hm⟩ := hBox p hp
    exact ⟨hl, hn, hm⟩
  · intro v hv
    have hvb' : v ∈ Icc a b' := ⟨hv.1, hv.2.trans hStarb'.le⟩
    have hGint : (∫ s in a..v, g s) = ∫ s in a..v, P.g s := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hsI : s ∈ Icc a v := by
        simpa only [uIcc_of_le hv.1] using hs
      exact (hOld s ⟨hsI.1, hsI.2.trans hv.2⟩).1
    have hGHInt : (∫ s in a..v, g s * h s) =
        ∫ s in a..v, P.g s * P.hEdge s := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hsI : s ∈ Icc a v := by
        simpa only [uIcc_of_le hv.1] using hs
      obtain ⟨hgs, hhs⟩ := hOld s ⟨hsI.1, hsI.2.trans hv.2⟩
      change g s * h s = P.g s * P.hEdge s
      rw [hgs, hhs]
    exact ⟨(hedge v hvb').1.trans
        (hGint.trans (P.radius_primitive v hv).symm),
      (hpsi v hvb').trans hGHInt⟩
  · intro v hv
    have hvb' : v ∈ Icc a b' :=
      ⟨haStar.le.trans hv.1, hv.2⟩
    have hvLow : v ∈ Icc vStar (vStar + η) :=
      ⟨hv.1, hv.2.trans (by dsimp [b']; linarith only [hη'η])⟩
    obtain ⟨hgv, hhv⟩ := hLow v hvLow
    exact ⟨(hedge v hvb').2.1.trans hgv,
      (hquot v hvb').trans hhv⟩

end ChristodoulouBV.Uniqueness

end
