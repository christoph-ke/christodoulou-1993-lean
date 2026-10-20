module

public import ChristodoulouBV.C1Solution.AxisReconstructionFixedPoint
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Reconstructed scalar-radius and transport equations

The scalar Picard equations imply both scalar-radius derivatives and the
two null transport equations above the regular axis.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- The incoming null scalar derivative equals `r φ_u` on the full closed
triangle. This includes its zero trace on the regular axis. -/
theorem Box.zeta_eq_radius_mul_phi_u {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    x.1.toTriple.zeta p = x.1.toTriple.radius p *
      (fderivWithin ℝ x.1.toTriple.phi
        (closedCoordTriangle a b) p) (1, 0) := by
  let K := closedCoordTriangle a b
  have hunique : UniqueDiffWithinAt ℝ K p :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab) p hp
  have hrDiff := (x.radius_c1 hab).differentiableOn (by norm_num) p hp
  have hphiDiff := (x.phi_c1 hab).differentiableOn (by norm_num) p hp
  have hEq : EqOn x.1.toTriple.scalarRadius
      (x.1.toTriple.radius * x.1.toTriple.phi) K :=
    fun q hq => x.scalarRadius_eq_radius_mul_phi_on hq
  have hderiv : fderivWithin ℝ x.1.toTriple.scalarRadius K p =
      fderivWithin ℝ (x.1.toTriple.radius * x.1.toTriple.phi) K p :=
    fderivWithin_congr' hEq hp
  rw [fderivWithin_mul hunique hrDiff hphiDiff] at hderiv
  have hu := congrArg (fun F : (ℝ × ℝ) →L[ℝ] ℝ => F (1, 0)) hderiv
  simp only [add_apply, smul_apply, smul_eq_mul] at hu
  rw [x.scalarRadius_u hab hM hsmall hfixed hp,
    x.radius_u hab hM hsmall hfixed hp] at hu
  unfold Triple.zeta
  linarith only [hu]

/-- The horizontal derivative of `θ` is `-λφ_u` on the entire closed
triangle. No second derivative of `φ` is used. -/
theorem Box.theta_u_eq_neg_lam_phi_u {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ x.1.toTriple.theta
      (closedCoordTriangle a b) p) (1, 0) =
      -x.1.toTriple.lam p *
        (fderivWithin ℝ x.1.toTriple.phi
          (closedCoordTriangle a b) p) (1, 0) := by
  let K := closedCoordTriangle a b
  have hunique : UniqueDiffWithinAt ℝ K p :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab) p hp
  have halpha := (x.alpha_c1).differentiableOn (by norm_num) p hp
  have hlam := (x.lam_c1).differentiableOn (by norm_num) p hp
  have hphi := (x.phi_c1 hab).differentiableOn (by norm_num) p hp
  have hprod := (x.lam_c1.mul (x.phi_c1 hab)).differentiableOn (by norm_num) p hp
  change (fderivWithin ℝ
    (x.1.toTriple.alpha - x.1.1.extendValue * x.1.toTriple.phi) K p) (1, 0) = _
  have hfun : x.1.1.extendValue * x.1.toTriple.phi =
      fun q => x.1.1.extendValue q * x.1.toTriple.phi q := by
    funext q
    simp only [Pi.mul_apply]
  rw [hfun]
  rw [fderivWithin_sub hunique halpha hprod]
  rw [← hfun, fderivWithin_mul hunique hlam hphi]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
  have hlamJet := x.lam_u hab hM hsmall hfixed hp
  change (fderivWithin ℝ x.1.1.extendValue K p) (1, 0) =
    x.1.toTriple.gravitational p at hlamJet
  rw [x.alpha_u hab hM hsmall hfixed hp, hlamJet]
  simp only [TripleJet.toTriple, K]
  ring_nf

/-- The vertical derivative of `ζ` is `-νφ_v` on the entire closed
triangle. -/
theorem Box.zeta_v_eq_neg_nu_phi_v {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ x.1.toTriple.zeta
      (closedCoordTriangle a b) p) (0, 1) =
      -x.1.toTriple.nu p *
        (fderivWithin ℝ x.1.toTriple.phi
          (closedCoordTriangle a b) p) (0, 1) := by
  let K := closedCoordTriangle a b
  have hunique : UniqueDiffWithinAt ℝ K p :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab) p hp
  have hbeta := (x.beta_c1 hab hM hsmall).differentiableOn (by norm_num) p hp
  have hnu := (x.nu_c1).differentiableOn (by norm_num) p hp
  have hphi := (x.phi_c1 hab).differentiableOn (by norm_num) p hp
  have hprod := (x.nu_c1.mul (x.phi_c1 hab)).differentiableOn (by norm_num) p hp
  change (fderivWithin ℝ
    (x.1.toTriple.beta - x.1.2.1.extendValue * x.1.toTriple.phi) K p) (0, 1) = _
  have hfun : x.1.2.1.extendValue * x.1.toTriple.phi =
      fun q => x.1.2.1.extendValue q * x.1.toTriple.phi q := by
    funext q
    simp only [Pi.mul_apply]
  rw [hfun]
  rw [fderivWithin_sub hunique hbeta hprod]
  rw [← hfun, fderivWithin_mul hunique hnu hphi]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
  have hnuJet := x.nu_v hab hM hsmall hfixed hp
  change (fderivWithin ℝ x.1.2.1.extendValue K p) (0, 1) =
    x.1.toTriple.gravitational p at hnuJet
  rw [x.beta_v hab hM hsmall hp, hnuJet]
  simp only [TripleJet.toTriple, K]
  ring_nf

/-- Christodoulou's outgoing scalar transport equation (1.16a) holds
strictly above the regular axis. -/
theorem Box.theta_transport {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hstrict : p.1 < p.2) :
    (fderivWithin ℝ x.1.toTriple.theta
      (closedCoordTriangle a b) p) (1, 0) =
      -(x.1.toTriple.lam p / x.1.toTriple.radius p) *
        x.1.toTriple.zeta p := by
  rw [x.theta_u_eq_neg_lam_phi_u hab hM hsmall hfixed hp,
    x.zeta_eq_radius_mul_phi_u hab hM hsmall hfixed hp]
  have hr : x.1.toTriple.radius p ≠ 0 := (x.radius_pos hp hstrict).ne'
  field_simp [hr]

/-- Christodoulou's incoming scalar transport equation (1.16b) holds
strictly above the regular axis. -/
theorem Box.zeta_transport {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hstrict : p.1 < p.2) :
    (fderivWithin ℝ x.1.toTriple.zeta
      (closedCoordTriangle a b) p) (0, 1) =
      -(x.1.toTriple.nu p / x.1.toTriple.radius p) *
        x.1.toTriple.theta p := by
  rw [x.zeta_v_eq_neg_nu_phi_v hab hM hsmall hfixed hp,
    x.theta_eq_radius_mul_phi_v hab hp]
  have hr : x.1.toTriple.radius p ≠ 0 := (x.radius_pos hp hstrict).ne'
  field_simp [hr]

end ChristodoulouBV.AxisPicard

end
