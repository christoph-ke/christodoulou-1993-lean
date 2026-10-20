module

public import ChristodoulouBV.C1Solution.AxisReconstruction
public import ChristodoulouBV.C1Solution.AxisReconstructionAxis
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Outgoing mass equation and mixed regularity

The attenuated Volterra formula supplies the outgoing mass equation on the
closed triangle. Its right-hand side is `C¹`; this supplies the mixed
regularity needed for the subsequent incoming mass defect argument.
-/

public section

noncomputable section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.AxisPicard

/-- Twice the mass is exactly the attenuated mass numerator. -/
theorem Triple.massNumerator_eq_two_mass (x : Triple) (p : ℝ × ℝ) :
    x.massNumerator p = 2 * x.mass p := by
  simp [Triple.mass]
  ring

/-- The outgoing first jet of twice the mass satisfies the linear
Volterra equation on the whole closed triangle. -/
theorem Box.massNumerator_v {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ x.1.toTriple.massNumerator
      (closedCoordTriangle a b) p) (0, 1) =
      x.1.toTriple.massSource p -
        x.1.toTriple.attenuation p * x.1.toTriple.massNumerator p := by
  obtain ⟨hj, hk⟩ := x.massSource_attenuation_c1 hab
  exact intervalIntegral.fderivWithin_attenuatedVolterraIntegral_vertical
    hab hj hk hp

/-- The outgoing first jet of the mass, expressed without quotient
division by the vanishing radius. -/
theorem Box.two_mass_v {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    2 * (fderivWithin ℝ x.1.toTriple.mass
      (closedCoordTriangle a b) p) (0, 1) =
      x.1.toTriple.massSource p -
        x.1.toTriple.attenuation p * x.1.toTriple.massNumerator p := by
  let K := closedCoordTriangle a b
  have hunique : UniqueDiffWithinAt ℝ K p :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab) p hp
  have hEq : x.1.toTriple.massNumerator =
      fun q => 2 * x.1.toTriple.mass q := by
    funext q
    exact x.1.toTriple.massNumerator_eq_two_mass q
  have hjet : fderivWithin ℝ x.1.toTriple.massNumerator K p =
      (2 : ℝ) • fderivWithin ℝ x.1.toTriple.mass K p := by
    rw [hEq]
    exact fderivWithin_const_mul hunique
      ((x.mass_c1 hab).differentiableOn (by norm_num) p hp) 2
  have hv := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1)) hjet
  rw [x.massNumerator_v hab hp] at hv
  simpa only [smul_apply, smul_eq_mul] using hv.symm

/-- The outgoing mass derivative itself is `C¹` on the entire closed
triangle. In particular its horizontal derivative exists off the axis,
providing the mixed derivative `∂u∂v m` required by the mass-defect computation. -/
theorem Box.mass_v_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) :
    ContDiffOn ℝ 1
      (fun p => (fderivWithin ℝ x.1.toTriple.mass
        (closedCoordTriangle a b) p) (0, 1))
      (closedCoordTriangle a b) := by
  obtain ⟨hj, hk⟩ := x.massSource_attenuation_c1 hab
  have hJ := intervalIntegral.contDiffOn_attenuatedVolterraIntegral hab hj hk
  have hRhs : ContDiffOn ℝ 1
      (fun p => (x.1.toTriple.massSource p -
        x.1.toTriple.attenuation p * x.1.toTriple.massNumerator p) / 2)
      (closedCoordTriangle a b) :=
    (hj.sub (hk.mul hJ)).div_const 2
  apply hRhs.congr
  intro p hp
  have h := x.two_mass_v hab hp
  linarith only [h]

/-- Both mass coordinate jets vanish at the regular axis, including the
vertices. These are the zero initial trace needed for the later defect ODE. -/
theorem Box.mass_axis_jets {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b)
    {u : ℝ} (hu : u ∈ Icc a b) :
    (fderivWithin ℝ x.1.toTriple.mass (closedCoordTriangle a b) (u, u)) (1, 0) = 0 ∧
    (fderivWithin ℝ x.1.toTriple.mass (closedCoordTriangle a b) (u, u)) (0, 1) = 0 := by
  have hp : (u, u) ∈ closedCoordTriangle a b := ⟨hu.1, le_rfl, hu.2⟩
  have hv : (fderivWithin ℝ x.1.toTriple.mass
      (closedCoordTriangle a b) (u, u)) (0, 1) = 0 := by
    have h := x.two_mass_v hab hp
    have hj : x.1.toTriple.massSource (u, u) = 0 := by
      change x.1.toTriple.lam (u, u) *
        (x.1.toTriple.h (u, u) - x.1.toTriple.phi (u, u)) ^ 2 = 0
      rw [Triple.phi_diag x hu]
      ring
    have hJ : x.1.toTriple.massNumerator (u, u) = 0 := by
      rw [x.1.toTriple.massNumerator_eq_two_mass]
      rw [(Triple.mass_diag x.1.toTriple u).1]
      ring
    rw [hj, hJ] at h
    ring_nf at h
    linarith only [h]
  have hdiag : ∀ t ∈ Icc a b, x.1.toTriple.mass (t, t) = 0 :=
    fun t _ => (Triple.mass_diag x.1.toTriple t).1
  have hsum := zero_diagonal_coordinate_jets hab (x.mass_c1 hab) hdiag hu
  exact ⟨by linarith only [hsum, hv], hv⟩

/-- Above the axis, the attenuation kernel is the quadratic source
divided by the positive radius. -/
theorem Box.attenuation_off_axis {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge)
    {p : ℝ × ℝ} (hstrict : p.1 < p.2) :
    x.1.toTriple.attenuation p =
      x.1.toTriple.massSource p / x.1.toTriple.radius p := by
  simp [Triple.attenuation, Triple.massSource, Triple.radius,
    intervalIntegral.weightedDiagonalQuotientKernel, hstrict]

/-- Above the axis, the mass ratio is twice the mass divided by the
positive radius. -/
theorem Box.massRatio_off_axis {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge)
    {p : ℝ × ℝ} (hstrict : p.1 < p.2) :
    x.1.toTriple.massRatio p =
      2 * x.1.toTriple.mass p / x.1.toTriple.radius p := by
  simp [Triple.massRatio, intervalIntegral.cubicLinearQuotient, hstrict,
    Triple.mass]
  ring

/-- The ordinary off-axis mass quotient is differentiable on the open
triangle, so the reconstruction may differentiate `μ = 2m/r` there. -/
theorem Box.mass_radius_quotient_differentiable {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge) (hab : a < b)
    {p : ℝ × ℝ} (hp : p ∈ openCoordTriangle a b) :
    DifferentiableAt ℝ
      (fun q => 2 * x.1.toTriple.mass q / x.1.toTriple.radius q) p := by
  have hpi : p ∈ interior (closedCoordTriangle a b) := by
    rw [interior_closedCoordTriangle]
    exact hp
  have hKn : closedCoordTriangle a b ∈ 𝓝 p :=
    mem_of_superset (isOpen_interior.mem_nhds hpi) interior_subset
  have hmass : DifferentiableAt ℝ x.1.toTriple.mass p :=
    ((x.mass_c1 hab).differentiableOn (by norm_num) p (interior_subset hpi))
      |>.differentiableAt hKn
  have hradius : DifferentiableAt ℝ x.1.toTriple.radius p :=
    ((x.radius_c1 hab).differentiableOn (by norm_num) p (interior_subset hpi))
      |>.differentiableAt hKn
  have hcoord : a < p.1 ∧ p.1 < p.2 ∧ p.2 < b := hp
  have hr : x.1.toTriple.radius p ≠ 0 :=
    (x.radius_pos (interior_subset hpi) hcoord.2.1).ne'
  have hquot := (hmass.const_mul 2).mul (hradius.inv hr)
  have heq : ((fun q => 2 * x.1.toTriple.mass q) * x.1.toTriple.radius⁻¹) =
      (fun q => 2 * x.1.toTriple.mass q / x.1.toTriple.radius q) := by
    funext q
    simp only [Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]
  rw [← heq]
  exact hquot

/-- The outgoing null scalar derivative is the weighted-mean error times
the outgoing expansion. -/
theorem Triple.theta_eq_lam_mul_error (x : Triple) (p : ℝ × ℝ) :
    x.theta p = x.lam p * (x.h p - x.phi p) := by
  simp only [Triple.theta, Triple.alpha]
  ring

/-- The quadratic mass source is `λ(h-φ)²`. -/
theorem Triple.massSource_eq (x : Triple) (p : ℝ × ℝ) :
    x.massSource p = x.lam p * (x.h p - x.phi p) ^ 2 := by
  rfl

/-- The reconstructed mass satisfies Christodoulou's outgoing mass
constraint (1.15b) at every point strictly above the regular axis. -/
theorem Box.outgoing_mass_equation {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hstrict : p.1 < p.2) :
    2 * x.1.toTriple.lam p *
      (fderivWithin ℝ x.1.toTriple.mass
        (closedCoordTriangle a b) p) (0, 1) =
      (1 - x.1.toTriple.massRatio p) * x.1.toTriple.theta p ^ 2 := by
  have hr : x.1.toTriple.radius p ≠ 0 := (x.radius_pos hp hstrict).ne'
  have hk := x.attenuation_off_axis hstrict
  have hmu : x.1.toTriple.massRatio p =
      x.1.toTriple.massNumerator p / x.1.toTriple.radius p := by
    simp [Triple.massRatio, intervalIntegral.cubicLinearQuotient, hstrict]
  have hj := x.1.toTriple.massSource_eq p
  have ht := x.1.toTriple.theta_eq_lam_mul_error p
  have hm := x.two_mass_v hab hp
  calc
    2 * x.1.toTriple.lam p *
        (fderivWithin ℝ x.1.toTriple.mass
          (closedCoordTriangle a b) p) (0, 1) =
      x.1.toTriple.lam p *
        (x.1.toTriple.massSource p -
          x.1.toTriple.attenuation p * x.1.toTriple.massNumerator p) := by
            rw [← hm]
            ring
    _ = (1 - x.1.toTriple.massRatio p) * x.1.toTriple.theta p ^ 2 := by
      rw [hk, hmu, hj, ht]
      field_simp [hr]

end ChristodoulouBV.AxisPicard

end
