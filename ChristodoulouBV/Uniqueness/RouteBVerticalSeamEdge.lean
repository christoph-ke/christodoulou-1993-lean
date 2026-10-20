module

public import ChristodoulouBV.Uniqueness.RouteBGluingClassicalJet
public import ChristodoulouBV.Uniqueness.RouteBGluingGeometry
import ChristodoulouBV.C1Solution.RectangleSeams
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Prescribed data on the Route B vertical seam

The prescribed expansion, scalar quotient, and radius on the outgoing edge
determine three primary field values. Equality of any C¹ field values on the
edge also determines its tangential relative jet, including both endpoints.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The two relative vertical jets of C¹ fields agree when their traces on
the common lower/axis edge agree. This holds at the terminal and top corners. -/
theorem routeB_vertical_jet_eq_of_trace_eq
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (hStarb : vStar < b)
    {fLow fAx : ℝ × ℝ → ℝ}
    (hLow : ContDiffOn ℝ 1 fLow (routeBLowerRegion a vStar b))
    (hAx : ContDiffOn ℝ 1 fAx (closedCoordTriangle a b))
    (hTrace : ∀ v ∈ Icc vStar b, fLow (a, v) = fAx (a, v))
    {v : ℝ} (hv : v ∈ Icc vStar b) :
    (fderivWithin ℝ fLow (routeBLowerRegion a vStar b) (a, v)) (0, 1) =
      (fderivWithin ℝ fAx (closedCoordTriangle a b) (a, v)) (0, 1) := by
  have hpLow : (a, v) ∈ routeBLowerRegion a vStar b :=
    ⟨⟨ha.le, le_rfl⟩, hv⟩
  have hpAx : (a, v) ∈ closedCoordTriangle a b :=
    ⟨le_rfl, haStar.le.trans hv.1, hv.2⟩
  have hmapLow : MapsTo (fun t : ℝ => (a, t)) (Icc vStar b)
      (routeBLowerRegion a vStar b) :=
    fun _ ht => ⟨⟨ha.le, le_rfl⟩, ht⟩
  have hmapAx : MapsTo (fun t : ℝ => (a, t)) (Icc vStar b)
      (closedCoordTriangle a b) :=
    fun _ ht => ⟨le_rfl, haStar.le.trans ht.1, ht.2⟩
  have hpair : HasDerivAt (fun t : ℝ => (a, t)) (0, 1) v :=
    (hasDerivAt_const v a).prodMk (hasDerivAt_id' v)
  have hLowSlice : HasDerivWithinAt (fun t => fLow (a, t))
      ((fderivWithin ℝ fLow (routeBLowerRegion a vStar b) (a, v)) (0, 1))
      (Icc vStar b) v := by
    have hFd := (hLow.differentiableOn (by norm_num) (a, v) hpLow).hasFDerivWithinAt
    simpa only [Function.comp_def] using
      hFd.comp_hasDerivWithinAt v hpair.hasDerivWithinAt hmapLow
  have hAxSlice : HasDerivWithinAt (fun t => fAx (a, t))
      ((fderivWithin ℝ fAx (closedCoordTriangle a b) (a, v)) (0, 1))
      (Icc vStar b) v := by
    have hFd := (hAx.differentiableOn (by norm_num) (a, v) hpAx).hasFDerivWithinAt
    simpa only [Function.comp_def] using
      hFd.comp_hasDerivWithinAt v hpair.hasDerivWithinAt hmapAx
  have hLowSlice' : HasDerivWithinAt (fun t => fAx (a, t))
      ((fderivWithin ℝ fLow (routeBLowerRegion a vStar b) (a, v)) (0, 1))
      (Icc vStar b) v :=
    hLowSlice.congr_of_mem (fun t ht => (hTrace t ht).symm) hv
  have huniq : UniqueDiffWithinAt ℝ (Icc vStar b) v :=
    (uniqueDiffOn_Icc hStarb) v hv
  exact (hLowSlice'.derivWithin huniq).symm.trans
    (hAxSlice.derivWithin huniq)

/-- Matching `λ`, `α/λ`, and `r` with positive expansion gives equality of
the three primary prescribed field values on the outgoing edge. -/
theorem routeB_vertical_prescribed_values_eq
    {a vStar b : ℝ} (SLow SAx : Fields)
    (hLamLow : ∀ v ∈ Icc vStar b, 0 < SLow.lam a v)
    (hLamAx : ∀ v ∈ Icc vStar b, 0 < SAx.lam a v)
    (hLam : ∀ v ∈ Icc vStar b, SLow.lam a v = SAx.lam a v)
    (hQuot : ∀ v ∈ Icc vStar b,
      SLow.alpha a v / SLow.lam a v = SAx.alpha a v / SAx.lam a v)
    (hRadius : ∀ v ∈ Icc vStar b, SLow.r a v = SAx.r a v) :
    ∀ v ∈ Icc vStar b,
      SLow.lam a v = SAx.lam a v ∧
      SLow.alpha a v = SAx.alpha a v ∧
      SLow.r a v = SAx.r a v := by
  intro v hv
  have hL := hLam v hv
  have hQ := hQuot v hv
  have hLA : SLow.lam a v ≠ 0 := ne_of_gt (hLamLow v hv)
  have hLB : SAx.lam a v ≠ 0 := ne_of_gt (hLamAx v hv)
  have hA : SLow.alpha a v = SAx.alpha a v := by
    calc
      SLow.alpha a v =
          (SLow.alpha a v / SLow.lam a v) * SLow.lam a v :=
        (div_mul_cancel₀ _ hLA).symm
      _ = (SAx.alpha a v / SAx.lam a v) * SAx.lam a v := by
        rw [hQ, hL]
      _ = SAx.alpha a v := div_mul_cancel₀ _ hLB
  exact ⟨hL, hA, hRadius v hv⟩

/-- The three prescribed fields have matching tangential relative jets on
the full closed seam. -/
theorem routeB_vertical_prescribed_vertical_jets_eq
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (hStarb : vStar < b) (SLow SAx : Fields)
    (hLowC1 : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hAxC1 : RouteBFieldsC1On SAx (closedCoordTriangle a b))
    (hLamLow : ∀ v ∈ Icc vStar b, 0 < SLow.lam a v)
    (hLamAx : ∀ v ∈ Icc vStar b, 0 < SAx.lam a v)
    (hLam : ∀ v ∈ Icc vStar b, SLow.lam a v = SAx.lam a v)
    (hQuot : ∀ v ∈ Icc vStar b,
      SLow.alpha a v / SLow.lam a v = SAx.alpha a v / SAx.lam a v)
    (hRadius : ∀ v ∈ Icc vStar b, SLow.r a v = SAx.r a v) :
    ∀ v ∈ Icc vStar b, ∀ c ∈
      ({RouteBField.expansion, RouteBField.outgoing, RouteBField.radius} :
        Set RouteBField),
      (fderivWithin ℝ (routeBField SLow c)
        (routeBLowerRegion a vStar b) (a, v)) (0, 1) =
      (fderivWithin ℝ (routeBField SAx c)
        (closedCoordTriangle a b) (a, v)) (0, 1) := by
  have hValues := routeB_vertical_prescribed_values_eq
    SLow SAx hLamLow hLamAx hLam hQuot hRadius
  intro v hv c hc
  have hTrace : ∀ t ∈ Icc vStar b,
      routeBField SLow c (a, t) = routeBField SAx c (a, t) := by
    intro t ht
    obtain ⟨hl, hα, hr⟩ := hValues t ht
    rcases Set.mem_insert_iff.mp hc with hc | hc
    · subst c; exact hl
    rcases Set.mem_insert_iff.mp hc with hc | hc
    · subst c; exact hα
    have hc : c = RouteBField.radius := by simpa using hc
    subst c
    exact hr
  exact routeB_vertical_jet_eq_of_trace_eq ha haStar hStarb
    (hLowC1 c) (hAxC1 c) hTrace hv

/-- Once all seven edge traces and transverse coordinate jets agree, the
full relative first jets agree. This isolates the ODE step needed by the
axis/rectangle seam theorem. -/
theorem routeB_vertical_full_jets_eq_of_horizontal_jets_eq
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (hStarb : vStar < b) (SLow SAx : Fields)
    (hLowC1 : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hAxC1 : RouteBFieldsC1On SAx (closedCoordTriangle a b))
    (hTrace : ∀ c : RouteBField, ∀ v ∈ Icc vStar b,
      routeBField SLow c (a, v) = routeBField SAx c (a, v))
    (hHorizontal : ∀ c : RouteBField, ∀ v ∈ Icc vStar b,
      (fderivWithin ℝ (routeBField SLow c)
        (routeBLowerRegion a vStar b) (a, v)) (1, 0) =
      (fderivWithin ℝ (routeBField SAx c)
        (closedCoordTriangle a b) (a, v)) (1, 0)) :
    ∀ c : RouteBField, ∀ v ∈ Icc vStar b,
      fderivWithin ℝ (routeBField SLow c)
        (routeBLowerRegion a vStar b) (a, v) =
      fderivWithin ℝ (routeBField SAx c)
        (closedCoordTriangle a b) (a, v) := by
  intro c v hv
  apply C1Solution.continuousLinearMap_ext_coordinate
  · exact hHorizontal c v hv
  · exact routeB_vertical_jet_eq_of_trace_eq ha haStar hStarb
      (hLowC1 c) (hAxC1 c) (hTrace c) hv

end ChristodoulouBV.Uniqueness

end
