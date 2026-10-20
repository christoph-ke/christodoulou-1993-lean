module

public import ChristodoulouBV.C1Solution.AxisReconstructionMixed
public import ChristodoulouBV.C1Solution.AxisReconstructionGeometry
import ChristodoulouBV.C1Solution.RectangleMassConstraint
public import ChristodoulouBV.ForMathlib.IntervalIntegral.LinearEquation
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# The incoming mass defect on the axis triangle

The outgoing Volterra mass equation and the reconstructed scalar fields give
the initial trace and the continuous coefficient for the incoming constraint.
-/

public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.AxisPicard

/-- A homogeneous linear ODE with a continuous coefficient propagates zero
data from the endpoint even when the derivative is known only in the open
interval. This is the form needed because mixed mass regularity is proved
only away from the regular axis. -/
theorem eq_zero_of_linear_ode_interior {a b : ℝ} (hab : a ≤ b)
    {e c : ℝ → ℝ}
    (he : ContinuousOn e (Icc a b))
    (hc : ContinuousOn c (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt e (c t * e t) t)
    (hinit : e a = 0) :
    ∀ t ∈ Icc a b, e t = 0 := by
  have hce : ContinuousOn (fun t => c t * e t) (Icc a b) := hc.mul he
  have hk : IntervalIntegrable c volume a b := hc.intervalIntegrable_of_Icc hab
  have hky : IntervalIntegrable (fun t => c t * e t) volume a b :=
    hce.intervalIntegrable_of_Icc hab
  have hzero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a b :=
    intervalIntegrable_const
  have hint (t : ℝ) (ht : t ∈ Icc a b) :
      e t - e a = ∫ s in a..t, (c s * e s + 0) := by
    have he' : ContinuousOn e (Icc a t) :=
      he.mono (Icc_subset_Icc le_rfl ht.2)
    have hce' : ContinuousOn (fun s => c s * e s) (Icc a t) :=
      hce.mono (Icc_subset_Icc le_rfl ht.2)
    have hdt : ∀ s ∈ Ioo a t, HasDerivAt e (c s * e s) s := by
      intro s hs
      exact hderiv s ⟨hs.1, hs.2.trans_le ht.2⟩
    have hFTC := intervalIntegral.integral_eq_sub_of_continuousOn_hasDerivAt
      ht.1 he' hce' hdt
    simp only [add_zero]
    exact hFTC.symm
  have hintZero (t : ℝ) (_ht : t ∈ Icc a b) :
      (0 : ℝ) - 0 = ∫ s in a..t, (c s * 0 + 0) := by simp
  have hsame := intervalIntegral.eq_on_of_integral_eq hab hk hzero hky
    (by simpa only [mul_zero] using hzero) hint hintZero hinit
  exact fun t ht => hsame ht

/-- A relative `C¹` jet on the triangle gives the ordinary horizontal
slice derivative at an interior point. -/
theorem horizontal_hasDerivAt_of_triangle_c1 {a b : ℝ}
    {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b))
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle a b) :
    HasDerivAt (fun t => f (t, v))
      ((fderivWithin ℝ f (closedCoordTriangle a b) (u, v)) (1, 0)) u := by
  have hpi : (u, v) ∈ interior (closedCoordTriangle a b) := by
    rw [interior_closedCoordTriangle]
    exact hp
  have hKn : closedCoordTriangle a b ∈ 𝓝 (u, v) :=
    mem_of_superset (isOpen_interior.mem_nhds hpi) interior_subset
  have hdiff : DifferentiableAt ℝ f (u, v) :=
    (hf.differentiableOn (by norm_num) (u, v) (interior_subset hpi)).differentiableAt hKn
  have hline : HasDerivAt (fun t : ℝ => (t, v)) (1, 0) u :=
    (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
  have h := hdiff.hasFDerivAt.comp_hasDerivAt u hline
  change HasDerivAt (fun t => f (t, v)) ((fderiv ℝ f (u, v)) (1, 0)) u at h
  rwa [fderivWithin_of_mem_nhds hKn]

/-- A relative `C¹` jet on the triangle gives the ordinary vertical
slice derivative at an interior point. -/
theorem vertical_hasDerivAt_of_triangle_c1 {a b : ℝ}
    {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle a b))
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle a b) :
    HasDerivAt (fun t => f (u, t))
      ((fderivWithin ℝ f (closedCoordTriangle a b) (u, v)) (0, 1)) v := by
  have hpi : (u, v) ∈ interior (closedCoordTriangle a b) := by
    rw [interior_closedCoordTriangle]
    exact hp
  have hKn : closedCoordTriangle a b ∈ 𝓝 (u, v) :=
    mem_of_superset (isOpen_interior.mem_nhds hpi) interior_subset
  have hdiff : DifferentiableAt ℝ f (u, v) :=
    (hf.differentiableOn (by norm_num) (u, v) (interior_subset hpi)).differentiableAt hKn
  have hline : HasDerivAt (fun t : ℝ => (u, t)) (0, 1) v :=
    (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
  have h := hdiff.hasFDerivAt.comp_hasDerivAt v hline
  change HasDerivAt (fun t => f (u, t)) ((fderiv ℝ f (u, v)) (0, 1)) v at h
  rwa [fderivWithin_of_mem_nhds hKn]

/-- The proposed incoming mass constraint, expressed as a defect of the
horizontal mass jet. The quotient is used only strictly above the axis. -/
@[expose] def Box.massDefect {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (p : ℝ × ℝ) : ℝ :=
  (fderivWithin ℝ x.1.toTriple.mass (closedCoordTriangle a b) p) (1, 0) -
    (1 - x.1.toTriple.massRatio p) * x.1.toTriple.zeta p ^ 2 /
      (2 * x.1.toTriple.nu p)

/-- The mass defect has zero trace on the regular axis, including the
initial and final vertices. This uses the diagonal chain rule through the
proved zero mass jets. -/
theorem Box.massDefect_axis {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b)
    {u : ℝ} (hu : u ∈ Icc a b) :
    x.massDefect (u, u) = 0 := by
  have hm := (x.mass_axis_jets hab hu).1
  have hz := (Triple.theta_zeta_diag x hu).2
  simp only [Box.massDefect, hm, hz, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, zero_div, sub_zero]

/-- The regular attenuation coefficient is continuous through the axis. -/
theorem Box.attenuation_continuousOn {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge) (hab : a < b) :
    ContinuousOn x.1.toTriple.attenuation (closedCoordTriangle a b) :=
  (x.massSource_attenuation_c1 hab).2.continuousOn

/-- With the box sign estimate, the proposed incoming mass defect extends
continuously to the whole closed axis triangle. -/
theorem Box.massDefect_continuousOn {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge) (hab : a < b)
    (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hg : ∀ v ∈ Icc a b, 3 / 8 ≤ g v) :
    ContinuousOn x.massDefect (closedCoordTriangle a b) := by
  let K := closedCoordTriangle a b
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hmu := (x.massRatio_c1 hab hM hsmall).continuousOn
  have hzeta := (x.zeta_c1 hab hM hsmall).continuousOn
  have hnu := x.nu_c1.continuousOn
  have hmjet : ContinuousOn
      (fun p => (fderivWithin ℝ x.1.toTriple.mass K p) (1, 0)) K :=
    ((x.mass_c1 hab).continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const
  have hnu_ne : ∀ p ∈ K, 2 * x.1.toTriple.nu p ≠ 0 := by
    intro p hp
    have hn := (x.nu_signs hab hM hsmall hg hp).2
    exact mul_ne_zero two_ne_zero (ne_of_lt (by linarith only [hn]))
  have hquot : ContinuousOn
      (fun p => (1 - x.1.toTriple.massRatio p) *
        x.1.toTriple.zeta p ^ 2 / (2 * x.1.toTriple.nu p)) K :=
    ((continuousOn_const.sub hmu).mul (hzeta.pow 2)).div
      (continuousOn_const.mul hnu) hnu_ne
  exact hmjet.sub hquot

/-- The continuous attenuation kernel is the singular-looking coefficient
`θ²/(rλ)` strictly above the axis. Thus the coefficient in the defect ODE
has a canonical continuous extension to the closed triangle. -/
theorem Box.attenuation_eq_theta_sq_div {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hstrict : p.1 < p.2) :
    x.1.toTriple.attenuation p =
      x.1.toTriple.theta p ^ 2 /
        (x.1.toTriple.radius p * x.1.toTriple.lam p) := by
  have hr : x.1.toTriple.radius p ≠ 0 := (x.radius_pos hp hstrict).ne'
  have hl : x.1.toTriple.lam p ≠ 0 := ne_of_gt (by
    linarith only [x.lam_ge_quarter hp])
  rw [x.attenuation_off_axis hstrict,
    x.1.toTriple.massSource_eq p,
    x.1.toTriple.theta_eq_lam_mul_error p]
  field_simp [hr, hl]

/-- The horizontal mass jet has an ordinary vertical derivative at every
interior off-axis point. It is the horizontal jet of the outgoing mass jet;
no second derivative of the Picard data is assumed. -/
theorem Box.mass_u_hasDerivAt_vertical {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge) (hab : a < b)
    {u v : ℝ} (huv : (u, v) ∈ openCoordTriangle a b) :
    HasDerivAt
      (fun t => (fderivWithin ℝ x.1.toTriple.mass
        (closedCoordTriangle a b) (u, t)) (1, 0))
      ((fderivWithin ℝ
        (fun q => (fderivWithin ℝ x.1.toTriple.mass
          (closedCoordTriangle a b) q) (0, 1))
        (closedCoordTriangle a b) (u, v)) (1, 0)) v := by
  have hparts : a < u ∧ u < v ∧ v < b := huv
  let u₀ := (a + u) / 2
  let u₁ := (2 * u + v) / 3
  let v₀ := (u + 2 * v) / 3
  let v₁ := (v + b) / 2
  have ha : a < u₀ := by dsimp [u₀]; linarith only [hparts.1]
  have hu : u₀ < u₁ := by
    dsimp [u₀, u₁]
    linarith only [hparts.1, hparts.2.1]
  have hgap : u₁ < v₀ := by
    dsimp [u₁, v₀]
    linarith only [hparts.2.1]
  have hv : v₀ < v₁ := by
    dsimp [v₀, v₁]
    linarith only [hparts.2.1, hparts.2.2]
  have hb : v₁ < b := by dsimp [v₁]; linarith only [hparts.2.2]
  have hu_mem : u ∈ Icc u₀ u₁ := by
    dsimp [u₀, u₁]
    constructor <;> linarith only [hparts.1, hparts.2.1]
  have hv_mem : v ∈ Icc v₀ v₁ := by
    dsimp [v₀, v₁]
    constructor <;> linarith only [hparts.2.1, hparts.2.2]
  have hv_interior : v₀ < v ∧ v < v₁ := by
    dsimp [v₀, v₁]
    constructor <;> linarith only [hparts.2.1, hparts.2.2]
  have h := x.mass_u_vertical_derivative hab ha hu hgap hv hb hu_mem hv_mem
  exact h.hasDerivAt (Icc_mem_nhds hv_interior.1 hv_interior.2)

/-- The mass gap is nonzero strictly above the axis, as a consequence of
the positive radius and the boxed mass-ratio bound. -/
theorem Box.mass_gap_ne_zero {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge) (hab : a < b)
    (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hstrict : p.1 < p.2) :
    x.1.toTriple.radius p - 2 * x.1.toTriple.mass p ≠ 0 := by
  have hr : x.1.toTriple.radius p ≠ 0 := (x.radius_pos hp hstrict).ne'
  have hμ := x.massRatio_off_axis hstrict
  have hbound := (x.massRatio_bounds hab hM hsmall hp).2
  intro hzero
  have heq : 2 * x.1.toTriple.mass p = x.1.toTriple.radius p := by
    linarith only [hzero]
  rw [hμ, heq, div_self hr] at hbound
  norm_num at hbound

/-- The reconstructed gravitational coefficient has the mass-gap form
used in the pointwise mass-defect cancellation. -/
theorem Box.gravitational_eq_mass_gap {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge) (hab : a < b)
    (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hstrict : p.1 < p.2) :
    x.1.toTriple.gravitational p =
      2 * x.1.toTriple.mass p * x.1.toTriple.lam p *
        x.1.toTriple.nu p /
        (x.1.toTriple.radius p *
          (x.1.toTriple.radius p - 2 * x.1.toTriple.mass p)) := by
  have hr : x.1.toTriple.radius p ≠ 0 := (x.radius_pos hp hstrict).ne'
  have hgap := x.mass_gap_ne_zero hab hM hsmall hp hstrict
  rw [x.gravitational_off_axis hab hM hsmall hp hstrict,
    x.massRatio_off_axis hstrict]
  field_simp [hr, hgap]

/-- Differentiate the proved outgoing mass density in the horizontal
direction, using the reconstructed radius, expansion, and scalar equations.
The horizontal mass jet is left as a variable in the resulting expression;
the incoming mass equation is not used. -/
theorem Box.outgoing_mass_density_u_hasDerivAt {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge) (hab : a < b)
    (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hfixed : x.IsTriangleFixedPoint)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle a b) :
    let d := (fderivWithin ℝ x.1.toTriple.mass
      (closedCoordTriangle a b) (u, v)) (1, 0)
    HasDerivAt
      (fun t => (1 - 2 * x.1.toTriple.mass (t, v) /
        x.1.toTriple.radius (t, v)) * x.1.toTriple.theta (t, v) ^ 2 /
        (2 * x.1.toTriple.lam (t, v)))
      ((-2 * d / x.1.toTriple.radius (u, v) +
          2 * x.1.toTriple.mass (u, v) * x.1.toTriple.nu (u, v) /
            x.1.toTriple.radius (u, v) ^ 2) *
          x.1.toTriple.theta (u, v) ^ 2 /
          (2 * x.1.toTriple.lam (u, v)) +
        (1 - 2 * x.1.toTriple.mass (u, v) /
          x.1.toTriple.radius (u, v)) *
          (2 * x.1.toTriple.theta (u, v) *
            (-x.1.toTriple.lam (u, v) * x.1.toTriple.zeta (u, v) /
              x.1.toTriple.radius (u, v))) /
          (2 * x.1.toTriple.lam (u, v)) -
        (1 - 2 * x.1.toTriple.mass (u, v) /
          x.1.toTriple.radius (u, v)) *
          x.1.toTriple.theta (u, v) ^ 2 *
          (2 * x.1.toTriple.mass (u, v) * x.1.toTriple.lam (u, v) *
            x.1.toTriple.nu (u, v) /
              (x.1.toTriple.radius (u, v) *
                (x.1.toTriple.radius (u, v) - 2 * x.1.toTriple.mass (u, v)))) /
          (2 * x.1.toTriple.lam (u, v) ^ 2)) u := by
  let p := (u, v)
  have hpK : p ∈ closedCoordTriangle a b := by
    change a ≤ u ∧ u ≤ v ∧ v ≤ b
    exact ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have huv : u < v := hp.2.1
  have hr : x.1.toTriple.radius p ≠ 0 := (x.radius_pos hpK huv).ne'
  have hl : x.1.toTriple.lam p ≠ 0 := ne_of_gt (by
    linarith only [x.lam_ge_quarter hpK])
  have hm := horizontal_hasDerivAt_of_triangle_c1 (x.mass_c1 hab) hp
  have hru := horizontal_hasDerivAt_of_triangle_c1 (x.radius_c1 hab) hp
  rw [x.radius_u hab hM hsmall hfixed hpK] at hru
  have hlamu := horizontal_hasDerivAt_of_triangle_c1 x.lam_c1 hp
  change HasDerivAt (fun t => x.1.toTriple.lam (t, v))
    ((fderivWithin ℝ x.1.toTriple.lam
      (closedCoordTriangle a b) (u, v)) (1, 0)) u at hlamu
  rw [x.lam_u hab hM hsmall hfixed hpK,
    x.gravitational_eq_mass_gap hab hM hsmall hpK huv] at hlamu
  have hthetau := horizontal_hasDerivAt_of_triangle_c1 (x.theta_c1 hab) hp
  rw [x.theta_transport hab hM hsmall hfixed hpK huv] at hthetau
  have htheta' : HasDerivAt (fun t => x.1.toTriple.theta (t, v))
      (-x.1.toTriple.lam p * x.1.toTriple.zeta p /
        x.1.toTriple.radius p) u := by
    convert hthetau using 1
    ring
  have hP := C1Solution.outgoing_mass_density_hasDerivWithinAt_horizontal
    (s := Set.univ) (m := fun t => x.1.toTriple.mass (t, v))
    (r := fun t => x.1.toTriple.radius (t, v))
    (lam := fun t => x.1.toTriple.lam (t, v))
    (nu := fun t => x.1.toTriple.nu (t, v))
    (theta := fun t => x.1.toTriple.theta (t, v))
    (zeta := fun t => x.1.toTriple.zeta (t, v))
    (d := fun t => (fderivWithin ℝ x.1.toTriple.mass
      (closedCoordTriangle a b) (t, v)) (1, 0))
    hr hl hm.hasDerivWithinAt hru.hasDerivWithinAt
    hlamu.hasDerivWithinAt htheta'.hasDerivWithinAt
  exact hP.hasDerivAt (by simp)

/-- The outgoing mass equation in derivative form, with precisely the
normalization used to differentiate the incoming defect. -/
theorem Box.mass_v_eq_outgoing_density {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge) (hab : a < b)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hstrict : p.1 < p.2) :
    (fderivWithin ℝ x.1.toTriple.mass
      (closedCoordTriangle a b) p) (0, 1) =
      (1 - x.1.toTriple.massRatio p) * x.1.toTriple.theta p ^ 2 /
        (2 * x.1.toTriple.lam p) := by
  have hl : x.1.toTriple.lam p ≠ 0 := ne_of_gt (by
    linarith only [x.lam_ge_quarter hp])
  apply (eq_div_iff (mul_ne_zero two_ne_zero hl)).2
  calc
    (fderivWithin ℝ x.1.toTriple.mass
        (closedCoordTriangle a b) p) (0, 1) *
        (2 * x.1.toTriple.lam p) =
      2 * x.1.toTriple.lam p *
        (fderivWithin ℝ x.1.toTriple.mass
          (closedCoordTriangle a b) p) (0, 1) := by ring
    _ = (1 - x.1.toTriple.massRatio p) *
      x.1.toTriple.theta p ^ 2 := x.outgoing_mass_equation hab hp hstrict

/-- On the interior of the axis triangle, the incoming mass defect obeys
the homogeneous vertical ODE. Its mixed derivative comes from the proved
outgoing mass equation, not from the incoming constraint. -/
theorem Box.massDefect_hasDerivAt_vertical {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge) (hab : a < b)
    (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hg : ∀ v ∈ Icc a b, 3 / 8 ≤ g v)
    (hfixed : x.IsTriangleFixedPoint)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle a b) :
    HasDerivAt (fun t => x.massDefect (u, t))
      (-x.1.toTriple.attenuation (u, v) * x.massDefect (u, v)) v := by
  let K := closedCoordTriangle a b
  let F := x.1.toTriple.mass
  let R := x.1.toTriple.radius
  let L := x.1.toTriple.lam
  let N := x.1.toTriple.nu
  let T := x.1.toTriple.theta
  let Z := x.1.toTriple.zeta
  let D : ℝ → ℝ := fun t => (fderivWithin ℝ F K (u, t)) (1, 0)
  let G : ℝ × ℝ → ℝ := fun p => (fderivWithin ℝ F K p) (0, 1)
  let H : ℝ :=
    ((-2 * D v / R (u, v) + 2 * F (u, v) * N (u, v) / R (u, v) ^ 2) *
        T (u, v) ^ 2 / (2 * L (u, v)) +
      (1 - 2 * F (u, v) / R (u, v)) *
        (2 * T (u, v) * (-L (u, v) * Z (u, v) / R (u, v))) /
        (2 * L (u, v)) -
      (1 - 2 * F (u, v) / R (u, v)) * T (u, v) ^ 2 *
        (2 * F (u, v) * L (u, v) * N (u, v) /
          (R (u, v) * (R (u, v) - 2 * F (u, v)))) /
        (2 * L (u, v) ^ 2))
  have hpK : (u, v) ∈ K := by
    change a ≤ u ∧ u ≤ v ∧ v ≤ b
    exact ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hr : R (u, v) ≠ 0 := (x.radius_pos hpK hp.2.1).ne'
  have hl : L (u, v) ≠ 0 := ne_of_gt (by
    linarith only [x.lam_ge_quarter hpK])
  have hn : N (u, v) ≠ 0 := ne_of_lt (by
    linarith only [(x.nu_signs hab hM hsmall hg hpK).2])
  have hgap : R (u, v) - 2 * F (u, v) ≠ 0 :=
    x.mass_gap_ne_zero hab hM hsmall hpK hp.2.1
  have hP : HasDerivAt
      (fun t => (1 - 2 * F (t, v) / R (t, v)) * T (t, v) ^ 2 /
        (2 * L (t, v))) H u :=
    x.outgoing_mass_density_u_hasDerivAt hab hM hsmall hfixed hp
  have hG : HasDerivAt (fun t => G (t, v))
      ((fderivWithin ℝ G K (u, v)) (1, 0)) u :=
    horizontal_hasDerivAt_of_triangle_c1 (x.mass_v_c1 hab) hp
  have hGP : (fun t => G (t, v)) =ᶠ[𝓝 u]
      (fun t => (1 - 2 * F (t, v) / R (t, v)) * T (t, v) ^ 2 /
        (2 * L (t, v))) := by
    filter_upwards [Ioo_mem_nhds hp.1 hp.2.1] with t ht
    have htK : (t, v) ∈ K := ⟨ht.1.le, ht.2.le, hp.2.2.le⟩
    exact (x.mass_v_eq_outgoing_density hab htK ht.2).trans (by
      rw [x.massRatio_off_axis ht.2])
  have hW : (fderivWithin ℝ G K (u, v)) (1, 0) = H :=
    hG.unique (hP.congr_of_eventuallyEq hGP)
  have hD : HasDerivAt D H v := by
    have h := x.mass_u_hasDerivAt_vertical hab hp
    change HasDerivAt D ((fderivWithin ℝ G K (u, v)) (1, 0)) v at h
    rwa [hW] at h
  have hm : HasDerivAt (fun t => F (u, t))
      ((1 - 2 * F (u, v) / R (u, v)) * T (u, v) ^ 2 /
        (2 * L (u, v))) v := by
    have h := vertical_hasDerivAt_of_triangle_c1 (x.mass_c1 hab) hp
    rw [x.mass_v_eq_outgoing_density hab hpK hp.2.1,
      x.massRatio_off_axis hp.2.1] at h
    exact h
  have hrv : HasDerivAt (fun t => R (u, t)) (L (u, v)) v := by
    have h := vertical_hasDerivAt_of_triangle_c1 (x.radius_c1 hab) hp
    rwa [x.radius_v hab hpK] at h
  have hnv : HasDerivAt (fun t => N (u, t))
      (2 * F (u, v) * L (u, v) * N (u, v) /
        (R (u, v) * (R (u, v) - 2 * F (u, v)))) v := by
    have h := vertical_hasDerivAt_of_triangle_c1 x.nu_c1 hp
    change HasDerivAt (fun t => x.1.toTriple.nu (u, t))
      ((fderivWithin ℝ x.1.toTriple.nu
        (closedCoordTriangle a b) (u, v)) (0, 1)) v at h
    rw [x.nu_v hab hM hsmall hfixed hpK,
      x.gravitational_eq_mass_gap hab hM hsmall hpK hp.2.1] at h
    exact h
  have hzv : HasDerivAt (fun t => Z (u, t))
      (-N (u, v) * T (u, v) / R (u, v)) v := by
    have h := vertical_hasDerivAt_of_triangle_c1
      (x.zeta_c1 hab hM hsmall) hp
    rw [x.zeta_transport hab hM hsmall hfixed hpK hp.2.1] at h
    convert h using 1
    ring
  have hE := C1Solution.mass_defect_hasDerivWithinAt (s := Set.univ)
    (m := fun t => F (u, t)) (r := fun t => R (u, t))
    (lam := fun t => L (u, t)) (nu := fun t => N (u, t))
    (theta := fun t => T (u, t)) (zeta := fun t => Z (u, t))
    (d := D) hr hl hn hgap hm.hasDerivWithinAt hrv.hasDerivWithinAt
    hnv.hasDerivWithinAt hzv.hasDerivWithinAt hD.hasDerivWithinAt
  have hEAt := hE.hasDerivAt (by simp)
  have hDE : (fun t => x.massDefect (u, t)) =ᶠ[𝓝 v]
      (fun t => D t - (1 - 2 * F (u, t) / R (u, t)) * Z (u, t) ^ 2 /
        (2 * N (u, t))) := by
    filter_upwards [Ioo_mem_nhds hp.2.1 hp.2.2] with t ht
    rw [Box.massDefect, x.massRatio_off_axis ht.1]
  have hEq := hEAt.congr_of_eventuallyEq hDE
  have hcoeff :
      -T (u, v) ^ 2 / (R (u, v) * L (u, v)) *
        (D v - (1 - 2 * F (u, v) / R (u, v)) * Z (u, v) ^ 2 /
          (2 * N (u, v))) =
      -x.1.toTriple.attenuation (u, v) * x.massDefect (u, v) := by
    rw [x.attenuation_eq_theta_sq_div hpK hp.2.1,
      Box.massDefect, x.massRatio_off_axis hp.2.1]
    ring
  rw [hcoeff] at hEq
  exact hEq

/-- The mass defect vanishes at every interior point. The initial value is
its regular-axis trace, and only off-axis mixed derivatives enter the ODE. -/
theorem Box.massDefect_eq_zero_interior {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge) (hab : a < b)
    (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hg : ∀ v ∈ Icc a b, 3 / 8 ≤ g v)
    (hfixed : x.IsTriangleFixedPoint)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle a b) :
    x.massDefect (u, v) = 0 := by
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc u v)
      (closedCoordTriangle a b) := by
    intro t ht
    exact ⟨hp.1.le, ht.1, ht.2.trans hp.2.2.le⟩
  have hline : Continuous (fun t : ℝ => (u, t)) :=
    continuous_const.prodMk continuous_id
  have he : ContinuousOn (fun t => x.massDefect (u, t)) (Icc u v) :=
    (x.massDefect_continuousOn hab hM hsmall hg).comp
      hline.continuousOn hmap
  have hc : ContinuousOn (fun t => -x.1.toTriple.attenuation (u, t))
      (Icc u v) :=
    ((x.attenuation_continuousOn hab).comp hline.continuousOn hmap).neg
  have hderiv : ∀ t ∈ Ioo u v,
      HasDerivAt (fun s => x.massDefect (u, s))
        (-x.1.toTriple.attenuation (u, t) * x.massDefect (u, t)) t := by
    intro t ht
    exact x.massDefect_hasDerivAt_vertical hab hM hsmall hg hfixed
      ⟨hp.1, ht.1, ht.2.trans hp.2.2⟩
  have haxis : x.massDefect (u, u) = 0 :=
    x.massDefect_axis hab ⟨hp.1.le, (hp.2.1.trans hp.2.2).le⟩
  exact eq_zero_of_linear_ode_interior hp.2.1.le he hc hderiv haxis
    v ⟨hp.2.1.le, le_rfl⟩

/-- The incoming mass defect vanishes on the entire closed triangle. The
boundary values use continuity of the relative mass jet, not mixed
derivatives at the regular axis or other edges. -/
theorem Box.massDefect_eq_zero {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge) (hab : a < b)
    (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hg : ∀ v ∈ Icc a b, 3 / 8 ≤ g v)
    (hfixed : x.IsTriangleFixedPoint)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    x.massDefect p = 0 := by
  have hOpen : EqOn x.massDefect (fun _ => (0 : ℝ))
      (openCoordTriangle a b) := by
    rintro ⟨u, v⟩ huv
    exact x.massDefect_eq_zero_interior hab hM hsmall hg hfixed huv
  have hClosed : EqOn x.massDefect (fun _ => (0 : ℝ))
      (closedCoordTriangle a b) :=
    hOpen.of_subset_closure (x.massDefect_continuousOn hab hM hsmall hg)
      continuousOn_const
      (fun _ hq => interior_subset (by rw [interior_closedCoordTriangle]; exact hq))
      (by rw [closure_openCoordTriangle hab])
  exact hClosed hp

/-- Christodoulou's incoming mass constraint (1.15a), as an equality of
relative horizontal coordinate jets on the closed triangle off the axis. -/
theorem Box.incoming_mass_equation {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge) (hab : a < b)
    (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hg : ∀ v ∈ Icc a b, 3 / 8 ≤ g v)
    (hfixed : x.IsTriangleFixedPoint)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (_hstrict : p.1 < p.2) :
    2 * x.1.toTriple.nu p *
      (fderivWithin ℝ x.1.toTriple.mass
        (closedCoordTriangle a b) p) (1, 0) =
      (1 - x.1.toTriple.massRatio p) * x.1.toTriple.zeta p ^ 2 := by
  have hn : x.1.toTriple.nu p ≠ 0 := ne_of_lt (by
    linarith only [(x.nu_signs hab hM hsmall hg hp).2])
  have hzero := x.massDefect_eq_zero hab hM hsmall hg hfixed hp
  have heq : (fderivWithin ℝ x.1.toTriple.mass
      (closedCoordTriangle a b) p) (1, 0) =
      (1 - x.1.toTriple.massRatio p) * x.1.toTriple.zeta p ^ 2 /
        (2 * x.1.toTriple.nu p) := by
    exact sub_eq_zero.mp hzero
  have hmul := (eq_div_iff (mul_ne_zero two_ne_zero hn)).mp heq
  calc
    2 * x.1.toTriple.nu p *
        (fderivWithin ℝ x.1.toTriple.mass
          (closedCoordTriangle a b) p) (1, 0) =
      (fderivWithin ℝ x.1.toTriple.mass
        (closedCoordTriangle a b) p) (1, 0) *
          (2 * x.1.toTriple.nu p) := by ring
    _ = (1 - x.1.toTriple.massRatio p) * x.1.toTriple.zeta p ^ 2 := hmul

/-- The incoming mass constraint as a relative derivative on each
horizontal characteristic, including its endpoint on the incoming edge.
This is the form used to produce the frozen mass primitive clause. -/
theorem Box.mass_hasDerivWithinAt_incoming {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge) (hab : a < b)
    (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hg : ∀ v ∈ Icc a b, 3 / 8 ≤ g v)
    (hfixed : x.IsTriangleFixedPoint)
    {u v : ℝ} (hp : (u, v) ∈ closedCoordTriangle a b) :
    HasDerivWithinAt (fun t => x.1.toTriple.mass (t, v))
      ((1 - x.1.toTriple.massRatio (u, v)) *
        x.1.toTriple.zeta (u, v) ^ 2 /
        (2 * x.1.toTriple.nu (u, v))) (Icc a v) u := by
  have hmap : MapsTo (fun t : ℝ => (t, v)) (Icc a v)
      (closedCoordTriangle a b) := by
    intro t ht
    exact ⟨ht.1, ht.2, hp.2.2⟩
  have hline : HasDerivWithinAt (fun t : ℝ => (t, v)) (1, 0)
      (Icc a v) u :=
    ((hasDerivAt_id' u).prodMk (hasDerivAt_const u v)).hasDerivWithinAt
  have hmass := ((x.mass_c1 hab).differentiableOn (by norm_num) (u, v) hp)
    |>.hasFDerivWithinAt
  have hcomp := hmass.comp_hasDerivWithinAt u hline hmap
  have heq := sub_eq_zero.mp (x.massDefect_eq_zero hab hM hsmall hg hfixed hp)
  change (fderivWithin ℝ x.1.toTriple.mass
    (closedCoordTriangle a b) (u, v)) (1, 0) =
      (1 - x.1.toTriple.massRatio (u, v)) *
        x.1.toTriple.zeta (u, v) ^ 2 /
        (2 * x.1.toTriple.nu (u, v)) at heq
  rw [heq] at hcomp
  exact hcomp

/-- The conformal factor is normalized to one at the first axis point
when the prescribed outgoing expansion is one half there. -/
theorem Box.conformal_initial_axis {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (hg : ∀ v ∈ Icc a b, 3 / 8 ≤ g v)
    (hga : g a = 1 / 2) :
    x.1.toTriple.conformal (a, a) = 1 := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hp : (a, a) ∈ closedCoordTriangle a b := ⟨le_rfl, le_rfl, hab.le⟩
  have hl : x.1.toTriple.lam (a, a) = 1 / 2 := by
    change x.1.1.extendValue (a, a) = 1 / 2
    rw [x.lam_edge ⟨a, ha⟩, hga]
  have hn : x.1.toTriple.nu (a, a) = -(1 / 2 : ℝ) := by
    change x.1.2.1.extendValue (a, a) = -(1 / 2 : ℝ)
    rw [x.nu_axis ⟨a, ha⟩]
    exact congrArg Neg.neg hl
  have hμ := (Triple.mass_diag x.1.toTriple a).2
  have hpos := (x.conformal_relation hab hM hsmall hg hp).1
  have heq := (x.conformal_relation hab hM hsmall hg hp).2
  rw [hμ, hl, hn] at heq
  nlinarith only [hpos, heq]

end ChristodoulouBV.AxisPicard

end
