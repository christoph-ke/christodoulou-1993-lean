module

public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamMass
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Incoming expansion on the Route B vertical seam

With radius, expansion, and mass already matched, the outgoing mixed
equation is a homogeneous linear ODE for `ν` along the shared edge.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Common radius, expansion, and mass and a common corner contraction
determine the contraction throughout the full closed vertical seam. -/
theorem routeB_vertical_nu_values_eq
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (SLow SAx : Fields)
    (hLowC1 : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hAxC1 : RouteBFieldsC1On SAx (closedCoordTriangle a b))
    (hLowJet : RouteBClassicalJetOn b (routeBLowerRegion a vStar b) SLow)
    (hAxJet : RouteBClassicalJetOn b (closedCoordTriangle a b) SAx)
    (hRadius : ∀ v ∈ Icc vStar b, SLow.r a v = SAx.r a v)
    (hRadiusPos : ∀ v ∈ Icc vStar b, 0 < SLow.r a v)
    (hLam : ∀ v ∈ Icc vStar b, SLow.lam a v = SAx.lam a v)
    (hMass : ∀ v ∈ Icc vStar b, SLow.m a v = SAx.m a v)
    (hGap : ∀ v ∈ Icc vStar b,
      0 < 1 - 2 * SLow.m a v / SLow.r a v)
    (hCorner : SLow.nu a vStar = SAx.nu a vStar) :
    ∀ v ∈ Icc vStar b, SLow.nu a v = SAx.nu a v := by
  let C : ℝ → ℝ := fun v =>
    ((2 * SLow.m a v / SLow.r a v) * SLow.lam a v) /
      ((1 - 2 * SLow.m a v / SLow.r a v) * SLow.r a v)
  have hmapLow : MapsTo (fun t : ℝ => (a, t)) (Icc vStar b)
      (routeBLowerRegion a vStar b) :=
    fun _ ht => ⟨⟨ha.le, le_rfl⟩, ht⟩
  have hmCont : ContinuousOn (fun v => SLow.m a v) (Icc vStar b) :=
    (hLowC1 .mass).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmapLow
  have hrCont : ContinuousOn (fun v => SLow.r a v) (Icc vStar b) :=
    (hLowC1 .radius).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmapLow
  have hLamCont : ContinuousOn (fun v => SLow.lam a v) (Icc vStar b) :=
    (hLowC1 .expansion).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmapLow
  have hrNe : ∀ v ∈ Icc vStar b, SLow.r a v ≠ 0 :=
    fun v hv => ne_of_gt (hRadiusPos v hv)
  have hRatioCont : ContinuousOn
      (fun v => 2 * SLow.m a v / SLow.r a v) (Icc vStar b) :=
    (continuousOn_const.mul hmCont).div hrCont hrNe
  have hDenCont : ContinuousOn
      (fun v => (1 - 2 * SLow.m a v / SLow.r a v) * SLow.r a v)
      (Icc vStar b) :=
    (continuousOn_const.sub hRatioCont).mul hrCont
  have hDenNe : ∀ v ∈ Icc vStar b,
      (1 - 2 * SLow.m a v / SLow.r a v) * SLow.r a v ≠ 0 :=
    fun v hv => ne_of_gt (mul_pos (hGap v hv) (hRadiusPos v hv))
  have hCCont : ContinuousOn C (Icc vStar b) :=
    (hRatioCont.mul hLamCont).div hDenCont hDenNe
  have hLowV : ∀ v ∈ Ico vStar b,
      (fderivWithin ℝ (routeBField SLow .contraction)
        (routeBLowerRegion a vStar b) (a, v)) (0, 1) =
        C v * SLow.nu a v + 0 := by
    intro v hv
    have h := hLowJet.contraction_out (a, v)
      ⟨⟨ha.le, le_rfl⟩, ⟨hv.1, hv.2.le⟩⟩
      ⟨ha.le, haStar.trans_le hv.1, hv.2⟩
    change _ =
      ((2 * SLow.m a v / SLow.r a v) * SLow.lam a v * SLow.nu a v) /
        ((1 - 2 * SLow.m a v / SLow.r a v) * SLow.r a v) at h
    have h' :
        (fderivWithin ℝ (routeBField SLow .contraction)
          (routeBLowerRegion a vStar b) (a, v)) (0, 1) =
        ((2 * SLow.m a v / SLow.r a v) * SLow.lam a v * SLow.nu a v) /
          ((1 - 2 * SLow.m a v / SLow.r a v) * SLow.r a v) := by
      have hfun :
          routeBScalarExpression (routeBSelector .contraction) SLow =
            routeBField SLow .contraction := by
        funext p
        rfl
      rw [hfun] at h
      exact h
    rw [h']
    dsimp [C]
    simp only [add_zero, div_eq_mul_inv]
    ring
  have hAxV : ∀ v ∈ Ico vStar b,
      (fderivWithin ℝ (routeBField SAx .contraction)
        (closedCoordTriangle a b) (a, v)) (0, 1) =
        C v * SAx.nu a v + 0 := by
    intro v hv
    have hv' : v ∈ Icc vStar b := ⟨hv.1, hv.2.le⟩
    have h := hAxJet.contraction_out (a, v)
      ⟨le_rfl, haStar.le.trans hv.1, hv.2.le⟩
      ⟨ha.le, haStar.trans_le hv.1, hv.2⟩
    change _ =
      ((2 * SAx.m a v / SAx.r a v) * SAx.lam a v * SAx.nu a v) /
        ((1 - 2 * SAx.m a v / SAx.r a v) * SAx.r a v) at h
    rw [← hMass v hv', ← hRadius v hv', ← hLam v hv'] at h
    have h' :
        (fderivWithin ℝ (routeBField SAx .contraction)
          (closedCoordTriangle a b) (a, v)) (0, 1) =
        ((2 * SLow.m a v / SLow.r a v) * SLow.lam a v * SAx.nu a v) /
          ((1 - 2 * SLow.m a v / SLow.r a v) * SLow.r a v) := by
      have hfun :
          routeBScalarExpression (routeBSelector .contraction) SAx =
            routeBField SAx .contraction := by
        funext p
        rfl
      rw [hfun] at h
      exact h
    rw [h']
    dsimp [C]
    simp only [add_zero, div_eq_mul_inv]
    ring
  exact routeB_vertical_trace_eq_of_linear_source ha haStar
    (hLowC1 .contraction) (hAxC1 .contraction) hCCont
    hLowV hAxV hCorner

end ChristodoulouBV.Uniqueness

end
