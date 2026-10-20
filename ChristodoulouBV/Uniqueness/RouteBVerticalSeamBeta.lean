module

public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamNu
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Incoming scalar transport on the Route B vertical seam

After the six other field values agree, the outgoing equation for `β` has
one common source. Its corner value fixes the final primary field trace.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Equality of the other six fields and the corner incoming transport
value forces the incoming transport field to agree on the full seam. -/
theorem routeB_vertical_beta_values_eq
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (SLow SAx : Fields)
    (hLowC1 : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hAxC1 : RouteBFieldsC1On SAx (closedCoordTriangle a b))
    (hLowJet : RouteBClassicalJetOn b (routeBLowerRegion a vStar b) SLow)
    (hAxJet : RouteBClassicalJetOn b (closedCoordTriangle a b) SAx)
    (hRadius : ∀ v ∈ Icc vStar b, SLow.r a v = SAx.r a v)
    (hPhi : ∀ v ∈ Icc vStar b, SLow.phi a v = SAx.phi a v)
    (hMass : ∀ v ∈ Icc vStar b, SLow.m a v = SAx.m a v)
    (hLam : ∀ v ∈ Icc vStar b, SLow.lam a v = SAx.lam a v)
    (hNu : ∀ v ∈ Icc vStar b, SLow.nu a v = SAx.nu a v)
    (hCorner : SLow.beta a vStar = SAx.beta a vStar) :
    ∀ v ∈ Icc vStar b, SLow.beta a v = SAx.beta a v := by
  let G : ℝ → ℝ := fun v =>
    ((2 * SLow.m a v / SLow.r a v) *
      SLow.lam a v * SLow.nu a v) /
        ((1 - 2 * SLow.m a v / SLow.r a v) * SLow.r a v) *
      SLow.phi a v
  have hLowV : ∀ v ∈ Ico vStar b,
      (fderivWithin ℝ (routeBField SLow .incoming)
        (routeBLowerRegion a vStar b) (a, v)) (0, 1) = G v := by
    intro v hv
    have h := hLowJet.incoming_out (a, v)
      ⟨⟨ha.le, le_rfl⟩, ⟨hv.1, hv.2.le⟩⟩
      ⟨ha.le, haStar.trans_le hv.1, hv.2⟩
    change _ = G v at h
    have hfun :
        routeBScalarExpression (routeBSelector .incoming) SLow =
          routeBField SLow .incoming := by
      funext p
      rfl
    rw [hfun] at h
    exact h
  have hAxV : ∀ v ∈ Ico vStar b,
      (fderivWithin ℝ (routeBField SAx .incoming)
        (closedCoordTriangle a b) (a, v)) (0, 1) = G v := by
    intro v hv
    have hv' : v ∈ Icc vStar b := ⟨hv.1, hv.2.le⟩
    have h := hAxJet.incoming_out (a, v)
      ⟨le_rfl, haStar.le.trans hv.1, hv.2.le⟩
      ⟨ha.le, haStar.trans_le hv.1, hv.2⟩
    change _ =
      ((2 * SAx.m a v / SAx.r a v) *
        SAx.lam a v * SAx.nu a v) /
          ((1 - 2 * SAx.m a v / SAx.r a v) * SAx.r a v) *
        SAx.phi a v at h
    rw [← hRadius v hv', ← hPhi v hv', ← hMass v hv',
      ← hLam v hv', ← hNu v hv'] at h
    have hfun :
        routeBScalarExpression (routeBSelector .incoming) SAx =
          routeBField SAx .incoming := by
      funext p
      rfl
    rw [hfun] at h
    exact h
  exact routeB_vertical_trace_eq_of_common_source ha haStar
    (hLowC1 .incoming) (hAxC1 .incoming)
    hLowV hAxV hCorner

end ChristodoulouBV.Uniqueness

end
