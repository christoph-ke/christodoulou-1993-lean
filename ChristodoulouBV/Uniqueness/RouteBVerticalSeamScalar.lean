module

public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamEdge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Scalar trace on the Route B vertical seam

The outgoing equation for `r φ` propagates the scalar trace from the
terminal corner. Positivity of `r` then recovers the scalar field itself.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A common outgoing source and a common terminal value determine the
trace of two C¹ fields on the lower/axis seam. The derivative equations are
needed only below the upper endpoint, where the open development lives. -/
theorem routeB_vertical_trace_eq_of_common_source
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    {fLow fAx : ℝ × ℝ → ℝ} {G : ℝ → ℝ}
    (hLow : ContDiffOn ℝ 1 fLow (routeBLowerRegion a vStar b))
    (hAx : ContDiffOn ℝ 1 fAx (closedCoordTriangle a b))
    (hLowV : ∀ v ∈ Ico vStar b,
      (fderivWithin ℝ fLow (routeBLowerRegion a vStar b) (a, v)) (0, 1) = G v)
    (hAxV : ∀ v ∈ Ico vStar b,
      (fderivWithin ℝ fAx (closedCoordTriangle a b) (a, v)) (0, 1) = G v)
    (hCorner : fLow (a, vStar) = fAx (a, vStar)) :
    ∀ v ∈ Icc vStar b, fLow (a, v) = fAx (a, v) := by
  have hmapLow : MapsTo (fun t : ℝ => (a, t)) (Icc vStar b)
      (routeBLowerRegion a vStar b) :=
    fun _ ht => ⟨⟨ha.le, le_rfl⟩, ht⟩
  have hmapAx : MapsTo (fun t : ℝ => (a, t)) (Icc vStar b)
      (closedCoordTriangle a b) :=
    fun _ ht => ⟨le_rfl, haStar.le.trans ht.1, ht.2⟩
  have hLowCont : ContinuousOn (fun v => fLow (a, v)) (Icc vStar b) :=
    hLow.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      hmapLow
  have hAxCont : ContinuousOn (fun v => fAx (a, v)) (Icc vStar b) :=
    hAx.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      hmapAx
  have hLowDeriv : ∀ v ∈ Ico vStar b,
      HasDerivWithinAt (fun t => fLow (a, t)) (G v) (Ici v) v := by
    intro v hv
    have hp : (a, v) ∈ routeBLowerRegion a vStar b :=
      ⟨⟨ha.le, le_rfl⟩, ⟨hv.1, hv.2.le⟩⟩
    have hFd := (hLow.differentiableOn (by norm_num) (a, v) hp).hasFDerivWithinAt
    have hpair : HasDerivAt (fun t : ℝ => (a, t)) (0, 1) v :=
      (hasDerivAt_const v a).prodMk (hasDerivAt_id' v)
    have hSlice : HasDerivWithinAt (fun t => fLow (a, t)) (G v)
        (Icc vStar b) v := by
      simpa only [Function.comp_def, hLowV v hv] using
        hFd.comp_hasDerivWithinAt v hpair.hasDerivWithinAt hmapLow
    exact hSlice.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hv)
  have hAxDeriv : ∀ v ∈ Ico vStar b,
      HasDerivWithinAt (fun t => fAx (a, t)) (G v) (Ici v) v := by
    intro v hv
    have hp : (a, v) ∈ closedCoordTriangle a b :=
      ⟨le_rfl, haStar.le.trans hv.1, hv.2.le⟩
    have hFd := (hAx.differentiableOn (by norm_num) (a, v) hp).hasFDerivWithinAt
    have hpair : HasDerivAt (fun t : ℝ => (a, t)) (0, 1) v :=
      (hasDerivAt_const v a).prodMk (hasDerivAt_id' v)
    have hSlice : HasDerivWithinAt (fun t => fAx (a, t)) (G v)
        (Icc vStar b) v := by
      simpa only [Function.comp_def, hAxV v hv] using
        hFd.comp_hasDerivWithinAt v hpair.hasDerivWithinAt hmapAx
    exact hSlice.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hv)
  intro v hv
  exact eq_of_has_deriv_right_eq hLowDeriv hAxDeriv
    hLowCont hAxCont hCorner v hv

/-- Matching radius and outgoing amplitude, together with the corner
scalar, force the scalar values to agree along the full closed seam. -/
theorem routeB_vertical_scalar_values_eq
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (hStarb : vStar < b) (SLow SAx : Fields)
    (hLowC1 : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hAxC1 : RouteBFieldsC1On SAx (closedCoordTriangle a b))
    (hLowJet : RouteBClassicalJetOn b (routeBLowerRegion a vStar b) SLow)
    (hAxJet : RouteBClassicalJetOn b (closedCoordTriangle a b) SAx)
    (hRadius : ∀ v ∈ Icc vStar b, SLow.r a v = SAx.r a v)
    (hRadiusPos : ∀ v ∈ Icc vStar b, 0 < SLow.r a v)
    (hAlpha : ∀ v ∈ Icc vStar b, SLow.alpha a v = SAx.alpha a v)
    (hCorner : SLow.phi a vStar = SAx.phi a vStar) :
    ∀ v ∈ Icc vStar b, SLow.phi a v = SAx.phi a v := by
  let ψLow := routeBScalarExpression routeBScalarRadiusExpr SLow
  let ψAx := routeBScalarExpression routeBScalarRadiusExpr SAx
  have hψLow : ContDiffOn ℝ 1 ψLow (routeBLowerRegion a vStar b) := by
    change ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => SLow.r p.1 p.2 * SLow.phi p.1 p.2)
      (routeBLowerRegion a vStar b)
    exact (hLowC1 .radius).mul (hLowC1 .scalar)
  have hψAx : ContDiffOn ℝ 1 ψAx (closedCoordTriangle a b) := by
    change ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => SAx.r p.1 p.2 * SAx.phi p.1 p.2)
      (closedCoordTriangle a b)
    exact (hAxC1 .radius).mul (hAxC1 .scalar)
  have hψVLow : ∀ v ∈ Ico vStar b,
      (fderivWithin ℝ ψLow (routeBLowerRegion a vStar b) (a, v)) (0, 1) =
        SLow.alpha a v := by
    intro v hv
    exact hLowJet.scalar_radius_out (a, v)
      ⟨⟨ha.le, le_rfl⟩, ⟨hv.1, hv.2.le⟩⟩
      ⟨ha.le, haStar.trans_le hv.1, hv.2⟩
  have hψVAx : ∀ v ∈ Ico vStar b,
      (fderivWithin ℝ ψAx (closedCoordTriangle a b) (a, v)) (0, 1) =
        SLow.alpha a v := by
    intro v hv
    have h := hAxJet.scalar_radius_out (a, v)
      ⟨le_rfl, haStar.le.trans hv.1, hv.2.le⟩
      ⟨ha.le, haStar.trans_le hv.1, hv.2⟩
    exact h.trans (hAlpha v ⟨hv.1, hv.2.le⟩).symm
  have hψCorner : ψLow (a, vStar) = ψAx (a, vStar) := by
    change SLow.r a vStar * SLow.phi a vStar =
      SAx.r a vStar * SAx.phi a vStar
    rw [hRadius vStar ⟨le_rfl, hStarb.le⟩, hCorner]
  have hψEq := routeB_vertical_trace_eq_of_common_source ha haStar
    hψLow hψAx hψVLow hψVAx hψCorner
  intro v hv
  have h := hψEq v hv
  change SLow.r a v * SLow.phi a v =
    SAx.r a v * SAx.phi a v at h
  rw [← hRadius v hv] at h
  exact (mul_left_cancel₀ (ne_of_gt (hRadiusPos v hv))) h

end ChristodoulouBV.Uniqueness

end
