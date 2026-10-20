module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointCoefficients
import all ChristodoulouBV.C1Solution.AxisPicardFixedPointFullPair
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.AttenuatedVolterraJet
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMean
import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraRadiusJet
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Reconstruction from an axis Picard triple

The definitions in this file are the canonical fields associated with a
boxed axis Picard triple. The radius and scalar radius are outgoing
primitives, and the mass is the attenuated outgoing Volterra integral.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- The scalar radius, normalized to vanish on the axis. -/
@[expose] def Triple.scalarRadius (x : Triple) (p : ℝ × ℝ) : ℝ :=
  intervalIntegral.weightedDiagonalNumerator x.lam x.h p

/-- The scalar field, including its weighted-mean value on the axis. -/
@[expose] def Triple.phi (x : Triple) (p : ℝ × ℝ) : ℝ :=
  intervalIntegral.weightedDiagonalMean x.lam x.h p

/-- The outgoing scalar derivative. -/
@[expose] def Triple.alpha (x : Triple) (p : ℝ × ℝ) : ℝ :=
  x.lam p * x.h p

/-- The incoming scalar derivative prescribed by the fixed-point equation. -/
@[expose] def Triple.beta (x : Triple) (p : ℝ × ℝ) : ℝ :=
  -x.alpha (p.1, p.1) +
    ∫ s in p.1..p.2, x.gravitational (p.1, s) * x.phi (p.1, s)

/-- The outgoing scalar null derivative. -/
@[expose] def Triple.theta (x : Triple) (p : ℝ × ℝ) : ℝ :=
  x.alpha p - x.lam p * x.phi p

/-- The incoming scalar null derivative. -/
@[expose] def Triple.zeta (x : Triple) (p : ℝ × ℝ) : ℝ :=
  x.beta p - x.nu p * x.phi p

/-- The mass given by the attenuated axis Volterra formula. -/
@[expose] def Triple.mass (x : Triple) (p : ℝ × ℝ) : ℝ :=
  x.massNumerator p / 2

/-- The mass ratio with its removable zero value on the axis. -/
@[expose] def Triple.massRatio (x : Triple) (p : ℝ × ℝ) : ℝ :=
  intervalIntegral.cubicLinearQuotient x.massNumerator x.radius p

/-- The positive conformal factor determined by the reconstructed fields. -/
@[expose] def Triple.conformal (x : Triple) (p : ℝ × ℝ) : ℝ :=
  Real.sqrt (-4 * x.lam p * x.nu p / (1 - x.massRatio p))

/-- The reconstructed radius and scalar radius vanish on the axis. -/
@[simp] theorem Triple.outgoing_primitives_diag (x : Triple) (u : ℝ) :
    x.radius (u, u) = 0 ∧ x.scalarRadius (u, u) = 0 := by
  simp [Triple.radius, Triple.scalarRadius,
    intervalIntegral.weightedDiagonalRadius,
    intervalIntegral.weightedDiagonalNumerator]

/-- The reconstructed mass and mass ratio vanish on the axis. -/
@[simp] theorem Triple.mass_diag (x : Triple) (u : ℝ) :
    x.mass (u, u) = 0 ∧ x.massRatio (u, u) = 0 := by
  simp [Triple.mass, Triple.massRatio, Triple.massNumerator,
    intervalIntegral.cubicLinearQuotient]

/-- The scalar field takes the prescribed normalized value on the axis. -/
theorem Triple.phi_diag {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) {u : ℝ} (hu : u ∈ Icc a b) :
    x.1.toTriple.phi (u, u) = x.1.toTriple.h (u, u) := by
  have hpos : x.1.toTriple.lam (u, u) ≠ 0 := by
    have hmem : (u, u) ∈ closedCoordTriangle a b := by
      change a ≤ u ∧ u ≤ u ∧ u ≤ b
      exact ⟨hu.1, le_rfl, hu.2⟩
    have hbox := (x.lam_value_bounds hmem).1
    change (1 / 4 : ℝ) ≤ x.1.toTriple.lam (u, u) at hbox
    exact ne_of_gt (by linarith only [hbox])
  exact intervalIntegral.weightedDiagonalMean_diag hpos

/-- The outgoing scalar derivative equals `λφ` on the axis. -/
theorem Triple.alpha_diag {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) {u : ℝ} (hu : u ∈ Icc a b) :
    x.1.toTriple.alpha (u, u) =
      x.1.toTriple.lam (u, u) * x.1.toTriple.phi (u, u) := by
  rw [Triple.phi_diag x hu]
  rfl

/-- The incoming scalar derivative is the negative outgoing scalar
derivative on the regular axis. -/
@[simp] theorem Triple.beta_diag (x : Triple) (u : ℝ) :
    x.beta (u, u) = -x.alpha (u, u) := by
  simp [Triple.beta]

/-- Both scalar null derivatives vanish on the regular axis. -/
theorem Triple.theta_zeta_diag {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge)
    {u : ℝ} (hu : u ∈ Icc a b) :
    x.1.toTriple.theta (u, u) = 0 ∧ x.1.toTriple.zeta (u, u) = 0 := by
  have hnu : x.1.toTriple.nu (u, u) = -x.1.toTriple.lam (u, u) := by
    simpa only [TripleJet.toTriple] using x.nu_axis ⟨u, hu⟩
  have hbeta : x.1.toTriple.beta (u, u) = -x.1.toTriple.alpha (u, u) := by
    simp [Triple.beta]
  constructor
  · simp [Triple.theta, Triple.alpha_diag x hu]
  · simp [Triple.zeta, hbeta, hnu, Triple.alpha_diag x hu]

/-- A boxed outgoing expansion is bounded below by one quarter. -/
theorem Box.lam_ge_quarter {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) :
    (1 / 4 : ℝ) ≤ x.1.toTriple.lam p :=
  (x.lam_value_bounds hp).1

/-- The reconstructed radius grows at least linearly away from the axis. -/
theorem Box.radius_ge_quarter_gap {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) :
    (1 / 4 : ℝ) * (p.2 - p.1) ≤ x.1.toTriple.radius p := by
  rcases p with ⟨u, v⟩
  change a ≤ u ∧ u ≤ v ∧ v ≤ b at hp
  exact intervalIntegral.mul_sub_le_weightedDiagonalRadius
    x.lam_c1.continuousOn (fun q hq => x.lam_ge_quarter hq)
    hp.1 hp.2.1 hp.2.2

/-- The reconstructed radius is positive strictly above the axis. -/
theorem Box.radius_pos {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) (hstrict : p.1 < p.2) :
    0 < x.1.toTriple.radius p := by
  have h := x.radius_ge_quarter_gap hp
  nlinarith only [h, sub_pos.mpr hstrict]

/-- The scalar radius is `rφ` off the regular axis. -/
theorem Box.scalarRadius_eq_radius_mul_phi {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hstrict : p.1 < p.2) :
    x.1.toTriple.scalarRadius p =
      x.1.toTriple.radius p * x.1.toTriple.phi p := by
  have hr : x.1.toTriple.radius p ≠ 0 := (x.radius_pos hp hstrict).ne'
  have h := intervalIntegral.weightedDiagonalMean_eq_div
    (w := x.1.toTriple.lam) (f := x.1.toTriple.h) (ne_of_lt hstrict)
  change x.1.toTriple.phi p =
    x.1.toTriple.scalarRadius p / x.1.toTriple.radius p at h
  rw [h]
  field_simp [hr]

/-- A closed-triangle `C¹` field has a closed-triangle `C¹` outgoing
primitive, including at both vertices. -/
theorem outgoing_integral_c1 {a b : ℝ} (hab : a < b)
    {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b)) :
    ContDiffOn ℝ 1 (intervalIntegral.weightedDiagonalRadius f)
      (closedCoordTriangle a b) := by
  let K := closedCoordTriangle a b
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hG := hf.continuousOn_fderivWithin hunique (by norm_num)
  have hdiff : DifferentiableOn ℝ f (interior K) :=
    (hf.differentiableOn (by norm_num)).mono interior_subset
  have hderiv : ∀ p ∈ interior K,
      fderiv ℝ f p = fderivWithin ℝ f K p := by
    intro p hp
    exact (fderivWithin_eq_fderiv (hunique p (interior_subset hp))
      ((hdiff p hp).differentiableAt (isOpen_interior.mem_nhds hp))).symm
  exact intervalIntegral.contDiffOn_weightedDiagonalRadius hab
    hf.continuousOn hG hdiff hderiv

/-- A positive `C¹` weight and a `C¹` function have a `C¹` weighted mean
on the entire closed triangle. -/
theorem weighted_mean_c1 {a b c : ℝ} (hab : a < b) (hc : 0 < c)
    {w f : ℝ × ℝ → ℝ}
    (hw : ContDiffOn ℝ 1 w (closedCoordTriangle a b))
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b))
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p) :
    ContDiffOn ℝ 1 (intervalIntegral.weightedDiagonalMean w f)
      (closedCoordTriangle a b) := by
  let K := closedCoordTriangle a b
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hGw := hw.continuousOn_fderivWithin hunique (by norm_num)
  have hGf := hf.continuousOn_fderivWithin hunique (by norm_num)
  have hdw : DifferentiableOn ℝ w (interior K) :=
    (hw.differentiableOn (by norm_num)).mono interior_subset
  have hdf : DifferentiableOn ℝ f (interior K) :=
    (hf.differentiableOn (by norm_num)).mono interior_subset
  have hderivw : ∀ p ∈ interior K,
      fderiv ℝ w p = fderivWithin ℝ w K p := by
    intro p hp
    exact (fderivWithin_eq_fderiv (hunique p (interior_subset hp))
      ((hdw p hp).differentiableAt (isOpen_interior.mem_nhds hp))).symm
  have hderivf : ∀ p ∈ interior K,
      fderiv ℝ f p = fderivWithin ℝ f K p := by
    intro p hp
    exact (fderivWithin_eq_fderiv (hunique p (interior_subset hp))
      ((hdf p hp).differentiableAt (isOpen_interior.mem_nhds hp))).symm
  exact intervalIntegral.contDiffOn_weightedDiagonalMean hab
    hw.continuousOn hf.continuousOn hGw hGf hdw hdf
    hderivw hderivf hweight hc

/-- The reconstructed radius has a continuous first jet on the closed
triangle. -/
theorem Box.radius_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) :
    ContDiffOn ℝ 1 x.1.toTriple.radius (closedCoordTriangle a b) :=
  outgoing_integral_c1 hab x.lam_c1

/-- The reconstructed scalar field has a continuous first jet on the
closed triangle. -/
theorem Box.phi_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) :
    ContDiffOn ℝ 1 x.1.toTriple.phi (closedCoordTriangle a b) :=
  weighted_mean_c1 hab (by norm_num) x.lam_c1 x.h_c1
    (fun p hp => x.lam_ge_quarter hp)

/-- The outgoing scalar derivative has a continuous first jet on the
closed triangle. -/
theorem Box.alpha_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) :
    ContDiffOn ℝ 1 x.1.toTriple.alpha (closedCoordTriangle a b) :=
  x.lam_c1.mul x.h_c1

/-- The scalar radius has a continuous first jet on the closed triangle. -/
theorem Box.scalarRadius_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) :
    ContDiffOn ℝ 1 x.1.toTriple.scalarRadius
      (closedCoordTriangle a b) := by
  have hproduct := x.lam_c1.mul x.h_c1
  exact outgoing_integral_c1 hab hproduct

/-- The reconstructed scalar radius agrees with `rφ` everywhere on the
closed triangle, including the regular axis. -/
theorem Box.scalarRadius_eq_radius_mul_phi_on {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    x.1.toTriple.scalarRadius p =
      x.1.toTriple.radius p * x.1.toTriple.phi p := by
  by_cases hstrict : p.1 < p.2
  · exact x.scalarRadius_eq_radius_mul_phi hp hstrict
  · rcases p with ⟨u, v⟩
    have hcoord : a ≤ u ∧ u ≤ v ∧ v ≤ b := hp
    have heq : u = v := le_antisymm hcoord.2.1 (le_of_not_gt hstrict)
    subst v
    simp [Triple.outgoing_primitives_diag]

/-- The radius outgoing first jet equals the Picard expansion on the
closed triangle. -/
theorem Box.radius_v {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ x.1.toTriple.radius (closedCoordTriangle a b) p) (0, 1) =
      x.1.toTriple.lam p :=
  intervalIntegral.radius_vertical_jet_of_contDiffOn hab x.lam_c1 hp

/-- The scalar-radius outgoing first jet equals `α` on the closed
triangle. -/
theorem Box.scalarRadius_v {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ x.1.toTriple.scalarRadius
      (closedCoordTriangle a b) p) (0, 1) =
      x.1.toTriple.alpha p :=
  intervalIntegral.radius_vertical_jet_of_contDiffOn hab x.alpha_c1 hp

/-- The outgoing null scalar derivative equals `r φ_v` on the whole
closed triangle; on the axis both sides vanish. -/
theorem Box.theta_eq_radius_mul_phi_v {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    x.1.toTriple.theta p = x.1.toTriple.radius p *
      (fderivWithin ℝ x.1.toTriple.phi
        (closedCoordTriangle a b) p) (0, 1) := by
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
  have hv := congrArg (fun F : (ℝ × ℝ) →L[ℝ] ℝ => F (0, 1)) hderiv
  simp only [add_apply, smul_apply, smul_eq_mul] at hv
  rw [x.scalarRadius_v hab hp, x.radius_v hab hp] at hv
  unfold Triple.theta
  linarith only [hv]

/-- The attenuated mass numerator and the mass have continuous first jets
up to the regular axis. -/
theorem Box.mass_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) :
    ContDiffOn ℝ 1 x.1.toTriple.mass (closedCoordTriangle a b) := by
  obtain ⟨hj, hk⟩ := x.massSource_attenuation_c1 hab
  have hJ := intervalIntegral.contDiffOn_attenuatedVolterraIntegral hab hj hk
  exact hJ.div_const 2

/-- The incoming scalar derivative has a continuous first jet on the
entire closed triangle. This uses only one derivative of the edge data:
the integrand `K_g φ` is `C¹`, while the diagonal term is a composition
of the `C¹` field `α` with the diagonal map. -/
theorem Box.beta_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    ContDiffOn ℝ 1 x.1.toTriple.beta (closedCoordTriangle a b) := by
  let K := closedCoordTriangle a b
  have hdiagMap : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => (p.1, p.1)) K := by
    fun_prop
  have hdiagInto : MapsTo (fun p : ℝ × ℝ => (p.1, p.1)) K K := by
    intro p hp
    change a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b at hp
    exact ⟨hp.1, le_rfl, hp.2.1.trans hp.2.2⟩
  have hdiag : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => x.1.toTriple.alpha (p.1, p.1)) K :=
    x.alpha_c1.comp hdiagMap hdiagInto
  have hsource := (x.picard_coefficients_c1 hab hM hsmall).1.mul (x.phi_c1 hab)
  have hint := outgoing_integral_c1 hab hsource
  exact hdiag.neg.add hint

/-- The incoming null scalar derivative is `C¹` on the closed triangle,
including both vertices. -/
theorem Box.zeta_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    ContDiffOn ℝ 1 x.1.toTriple.zeta (closedCoordTriangle a b) :=
  (x.beta_c1 hab hM hsmall).sub (x.nu_c1.mul (x.phi_c1 hab))

/-- The outgoing null scalar derivative is `C¹` on the closed triangle. -/
theorem Box.theta_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) :
    ContDiffOn ℝ 1 x.1.toTriple.theta (closedCoordTriangle a b) :=
  x.alpha_c1.sub (x.lam_c1.mul (x.phi_c1 hab))

/-- The removable mass ratio has a continuous first jet on the closed
triangle. -/
theorem Box.massRatio_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    ContDiffOn ℝ 1 x.1.toTriple.massRatio (closedCoordTriangle a b) := by
  let B := x.toCubicRationalFullPairBox x hab hM hsmall
  have h := B.pair.first.contDiffOn_coefficients hab
    (by norm_num : (0 : ℝ) < 1 / 4) B.ε_pos
    (fun p hp hoff => by linarith [B.complement_first p hp])
  rw [x.fullPair_first x hab hM hsmall] at h
  exact h.2.1

/-- The boxed mass ratio lies between zero and one quarter. -/
theorem Box.massRatio_bounds {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    0 ≤ x.1.toTriple.massRatio p ∧
      x.1.toTriple.massRatio p ≤ (1 / 4 : ℝ) := by
  let B := x.toCubicRationalFullPairBox x hab hM hsmall
  have hμ := (B.pair.linearQuotient_value_bounds
    (by norm_num : (0 : ℝ) < 1 / 4) p hp).1
  have hcomp := B.complement_first p hp
  have hε : B.ε = (3 / 4 : ℝ) := rfl
  rw [x.fullPair_first x hab hM hsmall] at hμ
  rw [hε, x.fullPair_first x hab hM hsmall] at hcomp
  change 0 ≤ x.1.toTriple.massRatio p at hμ
  change (3 / 4 : ℝ) ≤ 1 - x.1.toTriple.massRatio p at hcomp
  exact ⟨hμ, by linarith only [hcomp]⟩

/-- The reconstructed incoming expansion is negative in the numerical
Picard box. -/
theorem Box.nu_signs {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hg : ∀ v ∈ Icc a b, 3 / 8 ≤ g v)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    -(3 / 4 : ℝ) ≤ x.1.toTriple.nu p ∧
      x.1.toTriple.nu p ≤ -(1 / 4 : ℝ) := by
  have habs := x.nu_value_bound hp
  have hupper := x.nu_le_neg_quarter hab hM hsmall hg hp
  exact ⟨(abs_le.mp habs).1, hupper⟩

/-- The conformal factor is positive and satisfies the reconstructed
Einstein conformal relation on the closed triangle. -/
theorem Box.conformal_relation {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hg : ∀ v ∈ Icc a b, 3 / 8 ≤ g v)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    0 < x.1.toTriple.conformal p ∧
      (1 - x.1.toTriple.massRatio p) * x.1.toTriple.conformal p ^ 2 =
        -4 * x.1.toTriple.lam p * x.1.toTriple.nu p := by
  have hlam : 0 < x.1.toTriple.lam p := by
    linarith only [x.lam_ge_quarter hp]
  have hnu : x.1.toTriple.nu p < 0 := by
    linarith only [(x.nu_signs hab hM hsmall hg hp).2]
  have hden : 0 < 1 - x.1.toTriple.massRatio p := by
    linarith only [(x.massRatio_bounds hab hM hsmall hp).2]
  have hnum : 0 < -4 * x.1.toTriple.lam p * x.1.toTriple.nu p := by
    nlinarith only [mul_pos hlam (neg_pos.mpr hnu)]
  have harg : 0 < -4 * x.1.toTriple.lam p * x.1.toTriple.nu p /
      (1 - x.1.toTriple.massRatio p) := div_pos hnum hden
  constructor
  · exact Real.sqrt_pos.2 harg
  · dsimp only [Triple.conformal]
    rw [Real.sq_sqrt harg.le]
    field_simp [hden.ne']

end ChristodoulouBV.AxisPicard

end
