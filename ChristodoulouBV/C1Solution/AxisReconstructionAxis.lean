module

public import ChristodoulouBV.C1Solution.AxisReconstructionScalar
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Scalar jets at the regular axis

The weighted mean has two explicit coordinate jets at each diagonal point.
The Picard equation kills the horizontal jet of `h` there, leaving the two
equal scalar jets and the forced null-field jets.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- The diagonal jets of the normalized scalar field are each half the
vertical jet of the Picard scalar. The fixed-point equation supplies the
vanishing horizontal jet of `h`. -/
theorem Box.phi_axis_jets {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {u : ℝ} (hu : u ∈ Icc a b) :
    (fderivWithin ℝ x.1.toTriple.phi (closedCoordTriangle a b) (u, u)) (1, 0) =
      (fderivWithin ℝ x.1.toTriple.h (closedCoordTriangle a b) (u, u)) (0, 1) / 2 ∧
    (fderivWithin ℝ x.1.toTriple.phi (closedCoordTriangle a b) (u, u)) (0, 1) =
      (fderivWithin ℝ x.1.toTriple.h (closedCoordTriangle a b) (u, u)) (0, 1) / 2 := by
  let K := closedCoordTriangle a b
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hwl := x.lam_c1.continuousOn_fderivWithin hunique (by norm_num)
  have hhl := x.h_c1.continuousOn_fderivWithin hunique (by norm_num)
  have hdw : DifferentiableOn ℝ x.1.toTriple.lam (interior K) :=
    (x.lam_c1.differentiableOn (by norm_num)).mono interior_subset
  have hdf : DifferentiableOn ℝ x.1.toTriple.h (interior K) :=
    (x.h_c1.differentiableOn (by norm_num)).mono interior_subset
  have hderivw : ∀ p ∈ interior K,
      fderiv ℝ x.1.toTriple.lam p =
        fderivWithin ℝ x.1.toTriple.lam K p := by
    intro p hp
    exact (fderivWithin_eq_fderiv (hunique p (interior_subset hp))
      ((hdw p hp).differentiableAt (isOpen_interior.mem_nhds hp))).symm
  have hderivf : ∀ p ∈ interior K,
      fderiv ℝ x.1.toTriple.h p =
        fderivWithin ℝ x.1.toTriple.h K p := by
    intro p hp
    exact (fderivWithin_eq_fderiv (hunique p (interior_subset hp))
      ((hdf p hp).differentiableAt (isOpen_interior.mem_nhds hp))).symm
  have hcoords := intervalIntegral.weightedDiagonalMean_diag_coordinate_derivatives
    hab x.lam_c1.continuousOn x.h_c1.continuousOn hwl hhl
    hdw hdf hderivw hderivf (fun p hp => x.lam_ge_quarter hp)
    (by norm_num : (0 : ℝ) < 1 / 4) hu.1 hu.2
  have hhu := (x.picard_axis_evolution_jets hab hM hsmall hfixed hu).2.2
  change (fderivWithin ℝ x.1.2.2.extendValue K (u, u)) (1, 0) = 0 at hhu
  simp only [K] at hhu
  constructor
  · change (fderivWithin ℝ
      (intervalIntegral.weightedDiagonalMean x.1.1.extendValue x.1.2.2.extendValue)
      (closedCoordTriangle a b) (u, u)) (1, 0) =
      (fderivWithin ℝ x.1.2.2.extendValue (closedCoordTriangle a b) (u, u)) (0, 1) / 2
    rw [hcoords.2.1, hhu]
    simp
  · exact hcoords.1

/-- The horizontal derivative of the outgoing null scalar field at the
regular axis is minus half the axis expansion times `h_v`. -/
theorem Box.theta_u_axis {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {u : ℝ} (hu : u ∈ Icc a b) :
    (fderivWithin ℝ x.1.toTriple.theta (closedCoordTriangle a b) (u, u)) (1, 0) =
      -x.1.toTriple.lam (u, u) *
        (fderivWithin ℝ x.1.toTriple.h (closedCoordTriangle a b) (u, u)) (0, 1) / 2 := by
  have hp : (u, u) ∈ closedCoordTriangle a b := ⟨hu.1, le_rfl, hu.2⟩
  rw [x.theta_u_eq_neg_lam_phi_u hab hM hsmall hfixed hp,
    (x.phi_axis_jets hab hM hsmall hfixed hu).1]
  ring

/-- The vertical derivative of the incoming null scalar field at the
regular axis is half the axis expansion times `h_v`. -/
theorem Box.zeta_v_axis {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {u : ℝ} (hu : u ∈ Icc a b) :
    (fderivWithin ℝ x.1.toTriple.zeta (closedCoordTriangle a b) (u, u)) (0, 1) =
      x.1.toTriple.lam (u, u) *
        (fderivWithin ℝ x.1.toTriple.h (closedCoordTriangle a b) (u, u)) (0, 1) / 2 := by
  have hp : (u, u) ∈ closedCoordTriangle a b := ⟨hu.1, le_rfl, hu.2⟩
  rw [x.zeta_v_eq_neg_nu_phi_v hab hM hsmall hfixed hp,
    (x.phi_axis_jets hab hM hsmall hfixed hu).2]
  have hnu : x.1.toTriple.nu (u, u) = -x.1.toTriple.lam (u, u) := by
    simpa only [TripleJet.toTriple] using x.nu_axis ⟨u, hu⟩
  rw [hnu]
  ring

/-- The vertical derivative of the outgoing null scalar field at the
regular axis is half the axis expansion times `h_v`. -/
theorem Box.theta_v_axis {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {u : ℝ} (hu : u ∈ Icc a b) :
    (fderivWithin ℝ x.1.toTriple.theta (closedCoordTriangle a b) (u, u)) (0, 1) =
      x.1.toTriple.lam (u, u) *
        (fderivWithin ℝ x.1.toTriple.h (closedCoordTriangle a b) (u, u)) (0, 1) / 2 := by
  let K := closedCoordTriangle a b
  have hp : (u, u) ∈ K := ⟨hu.1, le_rfl, hu.2⟩
  have hunique : UniqueDiffWithinAt ℝ K (u, u) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab) _ hp
  have hlam := x.lam_c1.differentiableOn (by norm_num) _ hp
  have hscalar := (x.h_c1.sub (x.phi_c1 hab)).differentiableOn (by norm_num) _ hp
  have hfun : x.1.toTriple.theta =
      x.1.toTriple.lam * (x.1.toTriple.h - x.1.toTriple.phi) := by
    funext p
    simp only [Pi.mul_apply, Pi.sub_apply, Triple.theta, Triple.alpha]
    ring
  rw [hfun]
  change (fderivWithin ℝ
    (x.1.1.extendValue * (x.1.2.2.extendValue - x.1.toTriple.phi)) K (u, u))
    (0, 1) = _
  have hsub : x.1.2.2.extendValue - x.1.toTriple.phi =
      fun q => x.1.2.2.extendValue q - x.1.toTriple.phi q := by
    funext q
    simp only [Pi.sub_apply]
  rw [hsub]
  rw [fderivWithin_mul hunique hlam hscalar]
  simp only [add_apply, smul_apply, smul_eq_mul]
  have hdiag : x.1.toTriple.h (u, u) - x.1.toTriple.phi (u, u) = 0 := by
    rw [Triple.phi_diag x hu]
    ring
  change x.1.2.2.extendValue (u, u) - x.1.toTriple.phi (u, u) = 0 at hdiag
  rw [hdiag, zero_mul, add_zero]
  have hhdiff := x.h_c1.differentiableOn (by norm_num) _ hp
  have hphidiff := (x.phi_c1 hab).differentiableOn (by norm_num) _ hp
  rw [← hsub, fderivWithin_sub hunique hhdiff hphidiff]
  simp only [sub_apply]
  rw [(x.phi_axis_jets hab hM hsmall hfixed hu).2]
  simp only [K, TripleJet.toTriple]
  ring_nf

/-- A `C¹` field whose diagonal trace vanishes has opposite coordinate
jets at every point of the diagonal, including both vertices. -/
theorem zero_diagonal_coordinate_jets {a b : ℝ} (hab : a < b)
    {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b))
    (hdiag : ∀ u ∈ Icc a b, f (u, u) = 0)
    {u : ℝ} (hu : u ∈ Icc a b) :
    (fderivWithin ℝ f (closedCoordTriangle a b) (u, u)) (1, 0) +
      (fderivWithin ℝ f (closedCoordTriangle a b) (u, u)) (0, 1) = 0 := by
  let K := closedCoordTriangle a b
  have hp : (u, u) ∈ K := ⟨hu.1, le_rfl, hu.2⟩
  have hF := (hf.differentiableOn (by norm_num) _ hp).hasFDerivWithinAt
  have hpath : HasDerivAt (fun t : ℝ => (t, t)) (1, 1) u :=
    (hasDerivAt_id' u).prodMk (hasDerivAt_id' u)
  have hmap : MapsTo (fun t : ℝ => (t, t)) (Icc a b) K := by
    intro t ht
    exact ⟨ht.1, le_rfl, ht.2⟩
  have hcomp := HasFDerivWithinAt.comp_hasDerivWithinAt
    (f := fun t : ℝ => (t, t)) u hF hpath.hasDerivWithinAt hmap
  change HasDerivWithinAt (fun t : ℝ => f (t, t))
    ((fderivWithin ℝ f K (u, u)) (1, 1)) (Icc a b) u at hcomp
  have hzero : HasDerivWithinAt (fun t : ℝ => f (t, t)) 0 (Icc a b) u :=
    (hasDerivWithinAt_const u (Icc a b) (0 : ℝ)).congr
      (fun t ht => hdiag t ht) (hdiag u hu)
  have huniq := uniqueDiffOn_Icc hab u hu
  have htotal : (fderivWithin ℝ f K (u, u)) (1, 1) = 0 :=
    (hcomp.derivWithin huniq).symm.trans (hzero.derivWithin huniq)
  have hvec : ((1 : ℝ), (1 : ℝ)) = (1, 0) + (0, 1) := by
    ext <;> norm_num
  rw [hvec, map_add] at htotal
  exact htotal

/-- The horizontal derivative of the incoming null scalar field is minus
half the axis expansion times `h_v`. -/
theorem Box.zeta_u_axis {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {u : ℝ} (hu : u ∈ Icc a b) :
    (fderivWithin ℝ x.1.toTriple.zeta (closedCoordTriangle a b) (u, u)) (1, 0) =
      -x.1.toTriple.lam (u, u) *
        (fderivWithin ℝ x.1.toTriple.h (closedCoordTriangle a b) (u, u)) (0, 1) / 2 := by
  have hdiag : ∀ t ∈ Icc a b, x.1.toTriple.zeta (t, t) = 0 :=
    fun t ht => (Triple.theta_zeta_diag x ht).2
  have hsum := zero_diagonal_coordinate_jets hab
    (x.zeta_c1 hab hM hsmall) hdiag hu
  rw [x.zeta_v_axis hab hM hsmall hfixed hu] at hsum
  linarith only [hsum]

/-- Both scalar Picard evolution jets vanish on the regular axis. -/
theorem Box.scalar_axis_evolution_jets {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {u : ℝ} (hu : u ∈ Icc a b) :
    (fderivWithin ℝ x.1.toTriple.alpha (closedCoordTriangle a b) (u, u)) (1, 0) = 0 ∧
    (fderivWithin ℝ x.1.toTriple.beta (closedCoordTriangle a b) (u, u)) (0, 1) = 0 := by
  have hp : (u, u) ∈ closedCoordTriangle a b := ⟨hu.1, le_rfl, hu.2⟩
  constructor
  · rw [x.alpha_u hab hM hsmall hfixed hp]
    simp
  · rw [x.beta_v hab hM hsmall hp]
    simp

end ChristodoulouBV.AxisPicard

end
