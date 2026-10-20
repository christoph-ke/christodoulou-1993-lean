module

public import ChristodoulouBV.Uniqueness.RouteBAssemblyRestrict
public import ChristodoulouBV.C1Solution.RectangleJetSeams
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# Radius equality on the new incoming edge

The lower rectangle and axis triangle solve the same outgoing radius
equation. Equal corner radius and expansion therefore fix the entire
shared radius trace.
-/

public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- The lower radius on `u = a` is its corner value plus the integral of
the lower expansion. -/
theorem routeB_lower_radius_edge_integral
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (hStarb : vStar < b) (SLow : Fields)
    (hLowC1 : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hLowJet : RouteBClassicalJetOn b
      (routeBLowerRegion a vStar b) SLow) :
    ∀ v ∈ Icc vStar b,
      SLow.r a v = SLow.r a vStar + ∫ s in vStar..v, SLow.lam a s := by
  intro v hv
  have hsliceR : ContinuousOn (SLow.r a) (Icc vStar v) :=
    (hLowC1 .radius).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨⟨ha.le, le_rfl⟩, ⟨hs.1, hs.2.trans hv.2⟩⟩)
  have hsliceLam : ContinuousOn (SLow.lam a) (Icc vStar v) :=
    (hLowC1 .expansion).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨⟨ha.le, le_rfl⟩, ⟨hs.1, hs.2.trans hv.2⟩⟩)
  have hderiv : ∀ s ∈ Ioo vStar v,
      HasDerivAt (SLow.r a) (SLow.lam a s) s := by
    intro s hs
    have hsBig : s ∈ Ioo vStar b := ⟨hs.1, hs.2.trans_le hv.2⟩
    have hsLow : (a, s) ∈ routeBLowerRegion a vStar b :=
      ⟨⟨ha.le, le_rfl⟩, ⟨hsBig.1.le, hsBig.2.le⟩⟩
    have hsDev : (a, s) ∈ developmentWithInitialEdge b :=
      ⟨ha.le, haStar.trans hsBig.1, hsBig.2⟩
    have hRadiusC1 : ContDiffOn ℝ 1
        (fun p : ℝ × ℝ => SLow.r p.1 p.2)
        (Goursat.rectangle 0 a vStar b) := by
      simpa only [routeBLowerRegion, Goursat.rectangle, routeBField]
        using hLowC1 .radius
    have hcoordinate :=
      (C1Solution.coordinate_derivatives_of_contDiffOn_rectangle
        ha hStarb hRadiusC1
        ⟨ha.le, le_rfl⟩ ⟨hsBig.1.le, hsBig.2.le⟩).2
    have hval := hLowJet.radius_out (a, s) hsLow hsDev
    change (fderivWithin ℝ (fun p : ℝ × ℝ => SLow.r p.1 p.2)
      (routeBLowerRegion a vStar b) (a, s)) (0, 1) =
        SLow.lam a s at hval
    have hcoordinate' : HasDerivWithinAt (SLow.r a)
        ((fderivWithin ℝ (fun p : ℝ × ℝ => SLow.r p.1 p.2)
          (routeBLowerRegion a vStar b) (a, s)) (0, 1))
        (Icc vStar b) s := by
      simpa only [Goursat.rectangle, routeBLowerRegion] using hcoordinate
    rw [hval] at hcoordinate'
    exact hcoordinate'.hasDerivAt (Icc_mem_nhds hsBig.1 hsBig.2)
  have hint : IntervalIntegrable (SLow.lam a) volume vStar v :=
    hsliceLam.intervalIntegrable_of_Icc hv.1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hv.1 hsliceR hderiv hint
  linarith only [hFTC]

/-- The axis radius on the same edge has the analogous primitive. -/
theorem routeB_axis_radius_edge_integral
    {a vStar b : ℝ} (haStar : a < vStar)
    (_hStarb : vStar < b) (SAx : Fields)
    (HT : C1Solution.AxisClassicalSolution a b SAx) :
    ∀ v ∈ Icc vStar b,
      SAx.r a v = SAx.r a vStar + ∫ s in vStar..v, SAx.lam a s := by
  intro v hv
  have hsliceR : ContinuousOn (SAx.r a) (Icc vStar v) :=
    HT.r_c1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => by
        change (a, s) ∈ closedCoordTriangle a b
        exact ⟨le_rfl, haStar.le.trans hs.1, hs.2.trans hv.2⟩)
  have hsliceLam : ContinuousOn (SAx.lam a) (Icc vStar v) :=
    HT.lam_c1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => by
        change (a, s) ∈ closedCoordTriangle a b
        exact ⟨le_rfl, haStar.le.trans hs.1, hs.2.trans hv.2⟩)
  have hderiv : ∀ s ∈ Ioo vStar v,
      HasDerivAt (SAx.r a) (SAx.lam a s) s := by
    intro s hs
    exact HT.r_v a s ⟨le_rfl, haStar.trans hs.1,
      hs.2.trans_le hv.2⟩
  have hint : IntervalIntegrable (SAx.lam a) volume vStar v :=
    hsliceLam.intervalIntegrable_of_Icc hv.1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hv.1 hsliceR hderiv hint
  linarith only [hFTC]

/-- Positivity of the expansion and the regular axis imply positive radius
also on the closed top edge of an axis triangle. -/
theorem routeB_axis_radius_pos_closed_off_axis
    {a b : ℝ} {SAx : Fields}
    (HT : C1Solution.AxisClassicalSolution a b SAx)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hOff : p.1 < p.2) : 0 < SAx.r p.1 p.2 := by
  have hu : p.1 ∈ Icc a b := ⟨hp.1, hp.2.1.trans hp.2.2⟩
  have hRcont : ContinuousOn (SAx.r p.1) (Icc p.1 p.2) :=
    HT.r_c1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => by
        change (p.1, s) ∈ closedCoordTriangle a b
        exact ⟨hp.1, hs.1, hs.2.trans hp.2.2⟩)
  have hLamCont : ContinuousOn (SAx.lam p.1) (Icc p.1 p.2) :=
    HT.lam_c1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => by
        change (p.1, s) ∈ closedCoordTriangle a b
        exact ⟨hp.1, hs.1, hs.2.trans hp.2.2⟩)
  have hderiv : ∀ s ∈ Ioo p.1 p.2,
      HasDerivAt (SAx.r p.1) (SAx.lam p.1 s) s := by
    intro s hs
    exact HT.r_v p.1 s ⟨hp.1, hs.1,
      hs.2.trans_le hp.2.2⟩
  have hint : IntervalIntegrable (SAx.lam p.1) volume p.1 p.2 :=
    hLamCont.intervalIntegrable_of_Icc hOff.le
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hOff.le hRcont hderiv hint
  have hLamPos (s : ℝ) (hs : s ∈ Icc p.1 p.2) :
      0 < SAx.lam p.1 s :=
    HT.lam_pos (p.1, s) ⟨hp.1, hs.1, hs.2.trans hp.2.2⟩
  have hIntPos : 0 < ∫ s in p.1..p.2, SAx.lam p.1 s :=
    intervalIntegral.integral_pos hOff hLamCont
      (fun s hs => (hLamPos s ⟨hs.1.le, hs.2⟩).le)
      ⟨p.2, ⟨hOff.le, le_rfl⟩,
        hLamPos p.2 ⟨hOff.le, le_rfl⟩⟩
  rw [HT.r_axis p.1 hu] at hFTC
  linarith only [hFTC, hIntPos]

/-- Matching corner radius and expansion determine the radius on the
entire closed lower/axis vertical seam. -/
theorem routeB_lower_axis_radius_edge_eq
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (hStarb : vStar < b) (SLow SAx : Fields)
    (hLowC1 : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hLowJet : RouteBClassicalJetOn b
      (routeBLowerRegion a vStar b) SLow)
    (HT : C1Solution.AxisClassicalSolution a b SAx)
    (hCorner : SLow.r a vStar = SAx.r a vStar)
    (hLam : ∀ v ∈ Icc vStar b, SLow.lam a v = SAx.lam a v) :
    ∀ v ∈ Icc vStar b, SLow.r a v = SAx.r a v := by
  intro v hv
  have hInt : (∫ s in vStar..v, SLow.lam a s) =
      ∫ s in vStar..v, SAx.lam a s := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s ∈ Icc vStar v := by
      simpa only [uIcc_of_le hv.1] using hs
    exact hLam s ⟨hsI.1, hsI.2.trans hv.2⟩
  rw [routeB_lower_radius_edge_integral ha haStar hStarb SLow
      hLowC1 hLowJet v hv,
    routeB_axis_radius_edge_integral haStar hStarb SAx HT v hv,
    hCorner, hInt]

end ChristodoulouBV.Uniqueness

end
