module

public import ChristodoulouBV.Uniqueness.RouteBGluingClassicalTransfer
public import ChristodoulouBV.C1Solution.FrozenBridge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# From the glued classical jets to the frozen C¹ solution

Relative first jets yield ordinary characteristic derivatives throughout
the enlarged development, including its initial edge. The existing
classical-to-frozen bridge then supplies the interval primitives, axis
limits, and frozen C¹ bounds.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A vertical relative-jet equation on the closed triangle is an ordinary
outgoing characteristic derivative throughout the development. -/
theorem routeB_vertical_hasDerivAt_of_jetEquation
    {b : ℝ} {S : Fields} {E rhs : (RouteBField → ℝ) → ℝ}
    (hC1 : ContDiffOn ℝ 1 (routeBScalarExpression E S)
      (closedCoordTriangle 0 b))
    (hEq : RouteBLocalJetEquation b (closedCoordTriangle 0 b)
      S E rhs (0, 1))
    {u v : ℝ} (hp : (u, v) ∈ developmentWithInitialEdge b) :
    HasDerivAt (fun w => routeBScalarExpression E S (u, w))
      (rhs (fun c => routeBField S c (u, v))) v := by
  have hpK : (u, v) ∈ closedCoordTriangle 0 b :=
    ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
  have h := vertical_hasDerivAt_of_routeB_c1 hC1 hp
  rw [hEq (u, v) hpK hp] at h
  exact h

/-- A horizontal relative-jet equation is an ordinary incoming derivative
at every point with positive incoming coordinate. -/
theorem routeB_horizontal_hasDerivAt_of_jetEquation
    {b : ℝ} {S : Fields} {E rhs : (RouteBField → ℝ) → ℝ}
    (hC1 : ContDiffOn ℝ 1 (routeBScalarExpression E S)
      (closedCoordTriangle 0 b))
    (hEq : RouteBLocalJetEquation b (closedCoordTriangle 0 b)
      S E rhs (1, 0))
    {u v : ℝ} (hu : 0 < u)
    (hp : (u, v) ∈ developmentWithInitialEdge b) :
    HasDerivAt (fun w => routeBScalarExpression E S (w, v))
      (rhs (fun c => routeBField S c (u, v))) u := by
  have hpK : (u, v) ∈ closedCoordTriangle 0 b :=
    ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
  have h := horizontal_hasDerivAt_of_routeB_c1 hC1 hu hp
  rw [hEq (u, v) hpK hp] at h
  exact h

/-- The exact classical system, regular axis, and physical signs on the
glued closed triangle imply the frozen `IsC1Solution` predicate. -/
theorem routeB_isC1Solution_of_classicalJet
    {b : ℝ} (hb : 0 < b) (T : Fields)
    (hC1 : RouteBFieldsC1On T (closedCoordTriangle 0 b))
    (hJet : RouteBClassicalJetOn b (closedCoordTriangle 0 b) T)
    (haxisr : ∀ u ∈ Icc (0 : ℝ) b, T.r u u = 0)
    (haxism : ∀ u ∈ Icc (0 : ℝ) b, T.m u u = 0)
    (hrpos : ∀ p ∈ developmentWithInitialEdge b, 0 < T.r p.1 p.2)
    (hlampos : ∀ p ∈ closedCoordTriangle 0 b, 0 < T.lam p.1 p.2)
    (hnuneg : ∀ p ∈ developmentWithInitialEdge b, T.nu p.1 p.2 < 0)
    (hgap : ∀ p ∈ developmentWithInitialEdge b,
      0 < 1 - 2 * T.m p.1 p.2 / T.r p.1 p.2) :
    IsC1Solution (developmentWithInitialEdge b) T := by
  have hselect (c : RouteBField) :
      ContDiffOn ℝ 1
        (routeBScalarExpression (routeBSelector c) T)
        (closedCoordTriangle 0 b) := hC1 c
  have hpsi : ContDiffOn ℝ 1
      (routeBScalarExpression routeBScalarRadiusExpr T)
      (closedCoordTriangle 0 b) := routeB_scalarRadius_c1 hC1
  have htheta : ContDiffOn ℝ 1
      (routeBScalarExpression routeBThetaExpr T)
      (closedCoordTriangle 0 b) := (hC1.theta_zeta).1
  have hzeta : ContDiffOn ℝ 1
      (routeBScalarExpression routeBZetaExpr T)
      (closedCoordTriangle 0 b) := (hC1.theta_zeta).2
  have hrv : ∀ u v, (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (T.r u) (T.lam u v) v := by
    intro u v hp
    have h := routeB_vertical_hasDerivAt_of_jetEquation
      (hselect .radius) hJet.radius_out hp
    exact h
  have hru : ∀ u v, 0 < u → (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => T.r w v) (T.nu u v) u := by
    intro u v hu hp
    have h := routeB_horizontal_hasDerivAt_of_jetEquation
      (hselect .radius) hJet.radius_in hu hp
    exact h
  have hpsiv : ∀ u v, (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => T.r u w * T.phi u w) (T.alpha u v) v := by
    intro u v hp
    have h := routeB_vertical_hasDerivAt_of_jetEquation
      hpsi hJet.scalar_radius_out hp
    exact h
  have hpsiu : ∀ u v, 0 < u → (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => T.r w v * T.phi w v) (T.beta u v) u := by
    intro u v hu hp
    have h := routeB_horizontal_hasDerivAt_of_jetEquation
      hpsi hJet.scalar_radius_in hu hp
    exact h
  have hmv : ∀ u v, (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (T.m u)
        ((1 - 2 * T.m u v / T.r u v) * (T.theta u v)^2 /
          (2 * T.lam u v)) v := by
    intro u v hp
    have h := routeB_vertical_hasDerivAt_of_jetEquation
      (hselect .mass) hJet.mass_out hp
    exact h
  have hmu : ∀ u v, 0 < u → (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => T.m w v)
        ((1 - 2 * T.m u v / T.r u v) * (T.zeta u v)^2 /
          (2 * T.nu u v)) u := by
    intro u v hu hp
    have h := routeB_horizontal_hasDerivAt_of_jetEquation
      (hselect .mass) hJet.mass_in hu hp
    exact h
  have hlamu : ∀ u v, 0 < u → (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => T.lam w v)
        ((2 * T.m u v / T.r u v) * T.lam u v * T.nu u v /
          ((1 - 2 * T.m u v / T.r u v) * T.r u v)) u := by
    intro u v hu hp
    have h := routeB_horizontal_hasDerivAt_of_jetEquation
      (hselect .expansion) hJet.expansion_in hu hp
    exact h
  have hnuv : ∀ u v, (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (T.nu u)
        ((2 * T.m u v / T.r u v) * T.lam u v * T.nu u v /
          ((1 - 2 * T.m u v / T.r u v) * T.r u v)) v := by
    intro u v hp
    have h := routeB_vertical_hasDerivAt_of_jetEquation
      (hselect .contraction) hJet.contraction_out hp
    exact h
  have hthetau : ∀ u v, 0 < u → (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => T.theta w v)
        (-(T.lam u v / T.r u v * T.zeta u v)) u := by
    intro u v hu hp
    have h := routeB_horizontal_hasDerivAt_of_jetEquation
      htheta hJet.theta_in hu hp
    exact h
  have hzetav : ∀ u v, (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (T.zeta u)
        (-(T.nu u v / T.r u v * T.theta u v)) v := by
    intro u v hp
    have h := routeB_vertical_hasDerivAt_of_jetEquation
      hzeta hJet.zeta_out hp
    exact h
  have halphau : ∀ u v, 0 < u → (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (fun w => T.alpha w v)
        (((2 * T.m u v / T.r u v) * T.lam u v * T.nu u v /
          ((1 - 2 * T.m u v / T.r u v) * T.r u v)) * T.phi u v) u := by
    intro u v hu hp
    have h := routeB_horizontal_hasDerivAt_of_jetEquation
      (hselect .outgoing) hJet.outgoing_in hu hp
    exact h
  have hbetav : ∀ u v, (u, v) ∈ developmentWithInitialEdge b →
      HasDerivAt (T.beta u)
        (((2 * T.m u v / T.r u v) * T.lam u v * T.nu u v /
          ((1 - 2 * T.m u v / T.r u v) * T.r u v)) * T.phi u v) v := by
    intro u v hp
    have h := routeB_vertical_hasDerivAt_of_jetEquation
      (hselect .incoming) hJet.incoming_out hp
    exact h
  exact (C1Solution.isSolution_and_isC1Solution_of_classical hb T
    (hC1 .radius) (hC1 .scalar) (hC1 .mass)
    (hC1 .expansion) (hC1 .contraction)
    (hC1 .outgoing) (hC1 .incoming)
    hrv hru hpsiv hpsiu hmv hmu hlamu hnuv hthetau hzetav
    halphau hbetav
    (fun u hu hub => haxisr u ⟨hu, hub⟩)
    (fun u hu hub => haxism u ⟨hu, hub⟩)
    hrpos hlampos hnuneg hgap).2

end ChristodoulouBV.Uniqueness

end
