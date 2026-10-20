module

public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamLinear
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Outgoing mass trace on the Route B seam

Once the prescribed fields and scalar agree, the outgoing mass equation is
affine linear in mass. Its corner value therefore fixes the full edge trace.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The outgoing mass source, viewed as an affine linear function of mass. -/
theorem routeB_mass_out_linear
    (r lam m theta : ℝ) (hr : r ≠ 0) (hlam : lam ≠ 0) :
    (1 - 2 * m / r) * theta ^ 2 / (2 * lam) =
      (-theta ^ 2 / (lam * r)) * m + theta ^ 2 / (2 * lam) := by
  field_simp [hr, hlam]
  ring

/-- Matching prescribed data, scalar, and corner mass force equality of
the mass values along the whole axis/rectangle seam. -/
theorem routeB_vertical_mass_values_eq
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (SLow SAx : Fields)
    (hLowC1 : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hAxC1 : RouteBFieldsC1On SAx (closedCoordTriangle a b))
    (hLowJet : RouteBClassicalJetOn b (routeBLowerRegion a vStar b) SLow)
    (hAxJet : RouteBClassicalJetOn b (closedCoordTriangle a b) SAx)
    (hRadius : ∀ v ∈ Icc vStar b, SLow.r a v = SAx.r a v)
    (hRadiusPos : ∀ v ∈ Icc vStar b, 0 < SLow.r a v)
    (hLam : ∀ v ∈ Icc vStar b, SLow.lam a v = SAx.lam a v)
    (hLamPos : ∀ v ∈ Icc vStar b, 0 < SLow.lam a v)
    (hAlpha : ∀ v ∈ Icc vStar b, SLow.alpha a v = SAx.alpha a v)
    (hPhi : ∀ v ∈ Icc vStar b, SLow.phi a v = SAx.phi a v)
    (hCorner : SLow.m a vStar = SAx.m a vStar) :
    ∀ v ∈ Icc vStar b, SLow.m a v = SAx.m a v := by
  let θ : ℝ → ℝ := fun v =>
    SLow.alpha a v - SLow.lam a v * SLow.phi a v
  let A : ℝ → ℝ := fun v => -θ v ^ 2 / (SLow.lam a v * SLow.r a v)
  let B : ℝ → ℝ := fun v => θ v ^ 2 / (2 * SLow.lam a v)
  have hmapLow : MapsTo (fun t : ℝ => (a, t)) (Icc vStar b)
      (routeBLowerRegion a vStar b) :=
    fun _ ht => ⟨⟨ha.le, le_rfl⟩, ht⟩
  have hαCont : ContinuousOn (fun v => SLow.alpha a v) (Icc vStar b) :=
    (hLowC1 .outgoing).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmapLow
  have hLamCont : ContinuousOn (fun v => SLow.lam a v) (Icc vStar b) :=
    (hLowC1 .expansion).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmapLow
  have hφCont : ContinuousOn (fun v => SLow.phi a v) (Icc vStar b) :=
    (hLowC1 .scalar).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmapLow
  have hrCont : ContinuousOn (fun v => SLow.r a v) (Icc vStar b) :=
    (hLowC1 .radius).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmapLow
  have hθCont : ContinuousOn θ (Icc vStar b) :=
    hαCont.sub (hLamCont.mul hφCont)
  have hACont : ContinuousOn A (Icc vStar b) := by
    apply (hθCont.pow 2).neg.div (hLamCont.mul hrCont)
    intro v hv
    exact mul_ne_zero (ne_of_gt (hLamPos v hv))
      (ne_of_gt (hRadiusPos v hv))
  have hLowV : ∀ v ∈ Ico vStar b,
      (fderivWithin ℝ (routeBField SLow .mass)
        (routeBLowerRegion a vStar b) (a, v)) (0, 1) =
        A v * SLow.m a v + B v := by
    intro v hv
    have h := hLowJet.mass_out (a, v)
      ⟨⟨ha.le, le_rfl⟩, ⟨hv.1, hv.2.le⟩⟩
      ⟨ha.le, haStar.trans_le hv.1, hv.2⟩
    change _ =
      (1 - 2 * SLow.m a v / SLow.r a v) * θ v ^ 2 /
        (2 * SLow.lam a v) at h
    rw [routeB_mass_out_linear _ _ _ _
      (ne_of_gt (hRadiusPos v ⟨hv.1, hv.2.le⟩))
      (ne_of_gt (hLamPos v ⟨hv.1, hv.2.le⟩))] at h
    exact h
  have hAxV : ∀ v ∈ Ico vStar b,
      (fderivWithin ℝ (routeBField SAx .mass)
        (closedCoordTriangle a b) (a, v)) (0, 1) =
        A v * SAx.m a v + B v := by
    intro v hv
    have hv' : v ∈ Icc vStar b := ⟨hv.1, hv.2.le⟩
    have h := hAxJet.mass_out (a, v)
      ⟨le_rfl, haStar.le.trans hv.1, hv.2.le⟩
      ⟨ha.le, haStar.trans_le hv.1, hv.2⟩
    change _ =
      (1 - 2 * SAx.m a v / SAx.r a v) *
        (SAx.alpha a v - SAx.lam a v * SAx.phi a v) ^ 2 /
          (2 * SAx.lam a v) at h
    rw [← hRadius v hv', ← hLam v hv', ← hAlpha v hv',
      ← hPhi v hv'] at h
    rw [routeB_mass_out_linear _ _ _ _
      (ne_of_gt (hRadiusPos v hv'))
      (ne_of_gt (hLamPos v hv'))] at h
    exact h
  exact routeB_vertical_trace_eq_of_linear_source ha haStar
    (hLowC1 .mass) (hAxC1 .mass) hACont hLowV hAxV hCorner

end ChristodoulouBV.Uniqueness

end
