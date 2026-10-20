module

public import ChristodoulouBV.Frozen.FieldsTheta
public import ChristodoulouBV.Frozen.FieldsZeta
public import ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Classical equations on a translated axis triangle

This predicate records the seven relative C¹ fields and the ordinary
characteristic derivatives of the reduced Einstein-scalar system.
-/

@[expose] public section

open Set

namespace ChristodoulouBV.C1Solution

/-- The axis development with incoming edge at coordinate a. -/
def axisTriangleDevelopment (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | a ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < b}

/-- The classical reduced equations on a translated axis triangle. All
derivatives on the incoming edge are ordinary derivatives, while incoming
derivatives are required only away from that edge. -/
structure AxisClassicalSolution (a b : ℝ) (S : Fields) : Prop where
  r_c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.r p.1 p.2)
    (closedCoordTriangle a b)
  phi_c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2)
    (closedCoordTriangle a b)
  m_c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.m p.1 p.2)
    (closedCoordTriangle a b)
  lam_c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.lam p.1 p.2)
    (closedCoordTriangle a b)
  nu_c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.nu p.1 p.2)
    (closedCoordTriangle a b)
  alpha_c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.alpha p.1 p.2)
    (closedCoordTriangle a b)
  beta_c1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.beta p.1 p.2)
    (closedCoordTriangle a b)
  r_v : ∀ u v, (u, v) ∈ axisTriangleDevelopment a b →
    HasDerivAt (S.r u) (S.lam u v) v
  r_u : ∀ u v, a < u → (u, v) ∈ axisTriangleDevelopment a b →
    HasDerivAt (fun w => S.r w v) (S.nu u v) u
  psi_v : ∀ u v, (u, v) ∈ axisTriangleDevelopment a b →
    HasDerivAt (fun w => S.r u w * S.phi u w) (S.alpha u v) v
  psi_u : ∀ u v, a < u → (u, v) ∈ axisTriangleDevelopment a b →
    HasDerivAt (fun w => S.r w v * S.phi w v) (S.beta u v) u
  m_v : ∀ u v, (u, v) ∈ axisTriangleDevelopment a b →
    HasDerivAt (S.m u)
      ((1 - 2 * S.m u v / S.r u v) * (S.theta u v)^2 /
        (2 * S.lam u v)) v
  m_u : ∀ u v, a < u → (u, v) ∈ axisTriangleDevelopment a b →
    HasDerivAt (fun w => S.m w v)
      ((1 - 2 * S.m u v / S.r u v) * (S.zeta u v)^2 /
        (2 * S.nu u v)) u
  lam_u : ∀ u v, a < u → (u, v) ∈ axisTriangleDevelopment a b →
    HasDerivAt (fun w => S.lam w v)
      ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v)) u
  nu_v : ∀ u v, (u, v) ∈ axisTriangleDevelopment a b →
    HasDerivAt (S.nu u)
      ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v)) v
  theta_u : ∀ u v, a < u → (u, v) ∈ axisTriangleDevelopment a b →
    HasDerivAt (fun w => S.theta w v)
      (-(S.lam u v / S.r u v * S.zeta u v)) u
  zeta_v : ∀ u v, (u, v) ∈ axisTriangleDevelopment a b →
    HasDerivAt (S.zeta u)
      (-(S.nu u v / S.r u v * S.theta u v)) v
  alpha_u : ∀ u v, a < u → (u, v) ∈ axisTriangleDevelopment a b →
    HasDerivAt (fun w => S.alpha w v)
      (((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v)) * S.phi u v) u
  beta_v : ∀ u v, (u, v) ∈ axisTriangleDevelopment a b →
    HasDerivAt (S.beta u)
      (((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v)) * S.phi u v) v
  r_axis : ∀ u ∈ Icc a b, S.r u u = 0
  m_axis : ∀ u ∈ Icc a b, S.m u u = 0
  r_pos : ∀ p ∈ axisTriangleDevelopment a b, 0 < S.r p.1 p.2
  lam_pos : ∀ p ∈ closedCoordTriangle a b, 0 < S.lam p.1 p.2
  nu_neg : ∀ p ∈ axisTriangleDevelopment a b, S.nu p.1 p.2 < 0
  gap_pos : ∀ p ∈ axisTriangleDevelopment a b,
    0 < 1 - 2 * S.m p.1 p.2 / S.r p.1 p.2

end ChristodoulouBV.C1Solution

end
