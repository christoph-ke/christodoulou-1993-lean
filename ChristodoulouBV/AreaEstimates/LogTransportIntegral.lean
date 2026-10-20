module

public import ChristodoulouBV.AreaEstimates.LogTransportCommuted
import ChristodoulouBV.AreaEstimates.LogTransportInitialResidual
import all ChristodoulouBV.AreaEstimates.LogTransportMixed
public import ChristodoulouBV.AreaEstimates.AnalyticArea
public import ChristodoulouBV.AreaEstimates.FieldTransportJacobian
public import ChristodoulouBV.AreaEstimates.FieldTransportIntegral
public import ChristodoulouBV.AreaEstimates.ScalarAreaJacobian
import ChristodoulouBV.AreaEstimates.FieldTransportDerivatives
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Tactic
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import all ChristodoulouBV.AreaEstimates.LogTransportCore

/-!
# Integration of the logarithmic transports

The Jacobian maps and their continuous residual representatives are used to
integrate (4.11a) and the sign-corrected (4.11b) to characteristic edges.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

/-- The two logarithmic Jacobian densities are measurable as extended
nonnegative functions, independently of any choice of carrier. -/
theorem source_log_jacobian_densities_measurable (S : Fields) :
    Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal |(fderiv ℝ (sourcePhiBetaNuMap S) p).det|) ∧
    Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal |(fderiv ℝ (sourcePhiAlphaLamMap S) p).det|) := by
  constructor
  · exact ((ContinuousLinearMap.continuous_det.measurable.comp
      (measurable_fderiv ℝ (sourcePhiBetaNuMap S))).abs).ennreal_ofReal
  · exact ((ContinuousLinearMap.continuous_det.measurable.comp
      (measurable_fderiv ℝ (sourcePhiAlphaLamMap S))).abs).ennreal_ofReal

/-- The outgoing logarithmic Jacobian map is C¹ on every smaller closed
triangle. -/
theorem sourcePhiBetaNuMap_contDiffOn {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    ContDiffOn ℝ 1 (sourcePhiBetaNuMap S) (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  obtain ⟨_, hnu, hphi, _, _⟩ := C1Solution.five_fields_contDiffOn hB hB1 H
  have hbeta := C1Solution.beta_contDiffOn hB hB1 H
  have hnuNe : ∀ p ∈ K, S.nu p.1 p.2 ≠ 0 :=
    fun p hp => ne_of_lt (C1Solution.nu_neg_closed_triangle hB hB1 H hp)
  exact hphi.prodMk (hbeta.div hnu hnuNe)

/-- The incoming logarithmic Jacobian map is C¹ on every smaller closed
triangle. -/
theorem sourcePhiAlphaLamMap_contDiffOn {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    ContDiffOn ℝ 1 (sourcePhiAlphaLamMap S) (closedCoordTriangle 0 B) := by
  obtain ⟨_, _, hphi, _, _⟩ := C1Solution.five_fields_contDiffOn hB hB1 H
  exact hphi.prodMk (C1Solution.alpha_div_lam_contDiffOn hB hB1 H)

private theorem det_fderiv_prodMk_eq_coordinate_derivs
    {f g : ℝ × ℝ → ℝ} {u v : ℝ}
    (hf : DifferentiableAt ℝ f (u, v))
    (hg : DifferentiableAt ℝ g (u, v)) :
    (fderiv ℝ (fun p => (f p, g p)) (u, v)).det =
      deriv (fun x => f (x, v)) u * deriv (fun y => g (u, y)) v -
        deriv (fun y => f (u, y)) v * deriv (fun x => g (x, v)) u := by
  have hfu := (hf.hasFDerivAt.comp_hasDerivAt u
    ((hasDerivAt_id' u).prodMk (hasDerivAt_const u v))).deriv
  have hfv := (hf.hasFDerivAt.comp_hasDerivAt v
    ((hasDerivAt_const v u).prodMk (hasDerivAt_id' v))).deriv
  have hgu := (hg.hasFDerivAt.comp_hasDerivAt u
    ((hasDerivAt_id' u).prodMk (hasDerivAt_const u v))).deriv
  have hgv := (hg.hasFDerivAt.comp_hasDerivAt v
    ((hasDerivAt_const v u).prodMk (hasDerivAt_id' v))).deriv
  change deriv (fun x => f (x, v)) u = _ at hfu
  change deriv (fun y => f (u, y)) v = _ at hfv
  change deriv (fun x => g (x, v)) u = _ at hgu
  change deriv (fun y => g (u, y)) v = _ at hgv
  rw [det_fderiv_prodMk hf hg]
  rw [hfu, hfv, hgu, hgv]

/-- The oriented Jacobian in (4.11a) is the determinant defining its smooth
analytic area. -/
theorem sourceJacobianPhiBetaNu_eq_det {B : ℝ}
    (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    sourceJacobianPhiBetaNu S u v =
      (fderiv ℝ (sourcePhiBetaNuMap S) (u, v)).det := by
  let K := closedCoordTriangle 0 B
  have hpi : (u, v) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact hp
  have hnhds : K ∈ 𝓝 (u, v) :=
    mem_of_superset (isOpen_interior.mem_nhds hpi) interior_subset
  obtain ⟨_, hnu, hphi, _, _⟩ := C1Solution.five_fields_contDiffOn hB hB1 H
  have hbeta := C1Solution.beta_contDiffOn hB hB1 H
  have hphidiff : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => S.phi p.1 p.2) (u, v) :=
    (hphi.differentiableOn (by norm_num) (u, v) (interior_subset hpi)).differentiableAt
      hnhds
  have hnudiff : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => S.nu p.1 p.2) (u, v) :=
    (hnu.differentiableOn (by norm_num) (u, v) (interior_subset hpi)).differentiableAt
      hnhds
  have hbetadiff : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => S.beta p.1 p.2) (u, v) :=
    (hbeta.differentiableOn (by norm_num) (u, v) (interior_subset hpi)).differentiableAt
      hnhds
  have hnune : S.nu u v ≠ 0 := ne_of_lt
    (C1Solution.nu_neg_closed_triangle hB hB1 H (interior_subset hpi))
  have hquotdiff : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => S.beta p.1 p.2 / S.nu p.1 p.2) (u, v) :=
    (((sourcePhiBetaNuMap_contDiffOn hB hB1 H).snd.differentiableOn
      (by norm_num) (u, v) (interior_subset hpi)).differentiableAt hnhds)
  change _ = (fderiv ℝ (fun p : ℝ × ℝ =>
    (S.phi p.1 p.2, S.beta p.1 p.2 / S.nu p.1 p.2)) (u, v)).det
  rw [det_fderiv_prodMk_eq_coordinate_derivs hphidiff
    hquotdiff]
  rw [sourceJacobianPhiBetaNu.eq_1]

/-- The oriented Jacobian in sign-corrected (4.11b) is the determinant
defining its smooth analytic area. -/
theorem sourceJacobianPhiAlphaLam_eq_det {B : ℝ}
    (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    sourceJacobianPhiAlphaLam S u v =
      (fderiv ℝ (sourcePhiAlphaLamMap S) (u, v)).det := by
  let K := closedCoordTriangle 0 B
  have hpi : (u, v) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact hp
  have hnhds : K ∈ 𝓝 (u, v) :=
    mem_of_superset (isOpen_interior.mem_nhds hpi) interior_subset
  obtain ⟨hlam, _, hphi, _, _⟩ := C1Solution.five_fields_contDiffOn hB hB1 H
  have halpha := C1Solution.alpha_contDiffOn hB hB1 H
  have hphidiff : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => S.phi p.1 p.2) (u, v) :=
    (hphi.differentiableOn (by norm_num) (u, v) (interior_subset hpi)).differentiableAt
      hnhds
  have hlamdiff : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => S.lam p.1 p.2) (u, v) :=
    (hlam.differentiableOn (by norm_num) (u, v) (interior_subset hpi)).differentiableAt
      hnhds
  have halphadiff : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => S.alpha p.1 p.2) (u, v) :=
    (halpha.differentiableOn (by norm_num) (u, v) (interior_subset hpi)).differentiableAt
      hnhds
  have hlamne : S.lam u v ≠ 0 := ne_of_gt
    (H.solution.lam_pos (u, v) ⟨hp.1.le, hp.2.1, hp.2.2.trans hB1⟩)
  have hquotdiff : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => S.alpha p.1 p.2 / S.lam p.1 p.2) (u, v) :=
    ((C1Solution.alpha_div_lam_contDiffOn hB hB1 H).differentiableOn
      (by norm_num) (u, v) (interior_subset hpi)).differentiableAt hnhds
  change _ = (fderiv ℝ (fun p : ℝ × ℝ =>
    (S.phi p.1 p.2, S.alpha p.1 p.2 / S.lam p.1 p.2)) (u, v)).det
  rw [det_fderiv_prodMk_eq_coordinate_derivs hphidiff
    hquotdiff]
  rw [sourceJacobianPhiAlphaLam.eq_1]

/-- The outgoing log residual on a closed smaller triangle, using the
canonical removable mass coefficient and the continuous C¹ scalar jet. -/
@[expose] noncomputable def sourceOutgoingLogResidualClosed
    (B : ℝ) (S : Fields) (p : ℝ × ℝ) : ℝ :=
  (fderivWithin ℝ (fun q : ℝ × ℝ => Real.log (S.lam q.1 q.2))
      (closedCoordTriangle 0 B) p) (0, 1) -
    C1Solution.canonicalMixedCoefficient 1 S p / S.nu p.1 p.2 +
    (fderivWithin ℝ (fun q : ℝ × ℝ => S.phi q.1 q.2)
      (closedCoordTriangle 0 B) p) (0, 1) *
      (S.alpha p.1 p.2 / S.lam p.1 p.2 -
        S.beta p.1 p.2 / S.nu p.1 p.2)

/-- The incoming log residual on a closed smaller triangle. Its value at
the axis uses the continuous horizontal jet; the ordinary horizontal
derivative of the total field is only used at interior points. -/
@[expose] noncomputable def sourceIncomingLogResidualClosed
    (B : ℝ) (S : Fields) (p : ℝ × ℝ) : ℝ :=
  (fderivWithin ℝ (fun q : ℝ × ℝ => Real.log (-S.nu q.1 q.2))
      (closedCoordTriangle 0 B) p) (1, 0) -
    C1Solution.canonicalMixedCoefficient 1 S p / S.lam p.1 p.2 -
    (fderivWithin ℝ (fun q : ℝ × ℝ => S.phi q.1 q.2)
      (closedCoordTriangle 0 B) p) (1, 0) *
      (S.alpha p.1 p.2 / S.lam p.1 p.2 -
        S.beta p.1 p.2 / S.nu p.1 p.2)

/-- Both canonical logarithmic residuals are continuous on every smaller
closed triangle, including the initial edge and the regular axis. -/
theorem closed_log_residual_data {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    let K := closedCoordTriangle 0 B
    ContinuousOn (sourceOutgoingLogResidualClosed B S) K ∧
      ContinuousOn (sourceIncomingLogResidualClosed B S) K := by
  let K := closedCoordTriangle 0 B
  have hUnique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  obtain ⟨hlam, hnu, hphi, _, _⟩ := C1Solution.five_fields_contDiffOn hB hB1 H
  have halpha := C1Solution.alpha_contDiffOn hB hB1 H
  have hbeta := C1Solution.beta_contDiffOn hB hB1 H
  obtain ⟨c, hc, hcl⟩ := C1Solution.exists_lam_lower_bound hB hB1 H
  have hlamNe : ∀ p ∈ K, S.lam p.1 p.2 ≠ 0 := by
    intro p hp
    exact ne_of_gt (hc.trans_le (hcl p hp))
  have hnuNe : ∀ p ∈ K, S.nu p.1 p.2 ≠ 0 :=
    fun p hp => ne_of_lt (C1Solution.nu_neg_closed_triangle hB hB1 H hp)
  have hlogLam : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => Real.log (S.lam p.1 p.2)) K :=
    hlam.log hlamNe
  have hlogNu : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => Real.log (-S.nu p.1 p.2)) K :=
    hnu.neg.log (fun p hp => neg_ne_zero.mpr (hnuNe p hp))
  have hLv : ContinuousOn
      (fun p => (fderivWithin ℝ
        (fun q : ℝ × ℝ => Real.log (S.lam q.1 q.2)) K p) (0, 1)) K :=
    (hlogLam.continuousOn_fderivWithin hUnique (by norm_num)).clm_apply continuousOn_const
  have hNu : ContinuousOn
      (fun p => (fderivWithin ℝ
        (fun q : ℝ × ℝ => Real.log (-S.nu q.1 q.2)) K p) (1, 0)) K :=
    (hlogNu.continuousOn_fderivWithin hUnique (by norm_num)).clm_apply continuousOn_const
  have hPhiV : ContinuousOn
      (fun p => (fderivWithin ℝ
        (fun q : ℝ × ℝ => S.phi q.1 q.2) K p) (0, 1)) K :=
    (hphi.continuousOn_fderivWithin hUnique (by norm_num)).clm_apply continuousOn_const
  have hPhiU : ContinuousOn
      (fun p => (fderivWithin ℝ
        (fun q : ℝ × ℝ => S.phi q.1 q.2) K p) (1, 0)) K :=
    (hphi.continuousOn_fderivWithin hUnique (by norm_num)).clm_apply continuousOn_const
  have hCoeff : ContinuousOn
      (fun p => C1Solution.canonicalMixedCoefficient 1 S p) K :=
    C1Solution.canonicalMixedCoefficient_continuousOn hB hB1 H
  have hQuot : ContinuousOn
      (fun p : ℝ × ℝ => S.alpha p.1 p.2 / S.lam p.1 p.2 -
        S.beta p.1 p.2 / S.nu p.1 p.2) K :=
    (halpha.continuousOn.div hlam.continuousOn hlamNe).sub
      (hbeta.continuousOn.div hnu.continuousOn hnuNe)
  exact ⟨(hLv.sub (hCoeff.div hnu.continuousOn hnuNe)).add
      (hPhiV.mul hQuot),
    (hNu.sub (hCoeff.div hlam.continuousOn hlamNe)).sub
      (hPhiU.mul hQuot)⟩

private theorem vertical_slice_deriv_eq_fderivWithin {B : ℝ} (_hB : 0 < B)
    {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle 0 B))
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v < B) :
    deriv (fun t => f (u, t)) v =
      (fderivWithin ℝ f (closedCoordTriangle 0 B) (u, v)) (0, 1) := by
  rcases hu.eq_or_lt with rfl | huPos
  · have hvI : v ∈ Ioo (0 : ℝ) B := ⟨huv, hv⟩
    exact (vertical_edge_hasDerivAt hf hvI).deriv
  · let K := closedCoordTriangle 0 B
    have hpInt : (u, v) ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact ⟨huPos, huv, hv⟩
    have hnhds : K ∈ 𝓝 (u, v) :=
      mem_of_superset (isOpen_interior.mem_nhds hpInt) interior_subset
    have hdiff : DifferentiableAt ℝ f (u, v) :=
      (hf.differentiableOn (by norm_num) (u, v)
        (interior_subset hpInt)).differentiableAt hnhds
    have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt v
      ((hasDerivAt_const v u).prodMk (hasDerivAt_id' v))
    change HasDerivAt (fun t => f (u, t))
      ((fderiv ℝ f (u, v)) (0, 1)) v at hcomp
    rw [fderivWithin_of_mem_nhds hnhds]
    exact hcomp.deriv

private theorem horizontal_slice_deriv_eq_fderivWithin {B : ℝ}
    {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle 0 B))
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < B) :
    deriv (fun t => f (t, v)) u =
      (fderivWithin ℝ f (closedCoordTriangle 0 B) (u, v)) (1, 0) := by
  let K := closedCoordTriangle 0 B
  have hpInt : (u, v) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact ⟨hu, huv, hv⟩
  have hnhds : K ∈ 𝓝 (u, v) :=
    mem_of_superset (isOpen_interior.mem_nhds hpInt) interior_subset
  have hdiff : DifferentiableAt ℝ f (u, v) :=
    (hf.differentiableOn (by norm_num) (u, v)
      (interior_subset hpInt)).differentiableAt hnhds
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt u
    ((hasDerivAt_id' u).prodMk (hasDerivAt_const u v))
  change HasDerivAt (fun t => f (t, v))
    ((fderiv ℝ f (u, v)) (1, 0)) u at hcomp
  rw [fderivWithin_of_mem_nhds hnhds]
  exact hcomp.deriv

/-- On the open development and its initial edge, the continuous outgoing
representative is exactly the source residual from (4.12a). -/
theorem sourceOutgoingLogResidualClosed_eq {B : ℝ}
    (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v < B) :
    sourceOutgoingLogResidualClosed B S (u, v) =
      sourceOutgoingLogResidual S u v := by
  let K := closedCoordTriangle 0 B
  have hpK : (u, v) ∈ K := ⟨hu, huv.le, hv.le⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hu, huv, hv.trans hB1⟩
  have hlog : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => Real.log (S.lam p.1 p.2)) K := by
    have hlam := (C1Solution.five_fields_contDiffOn hB hB1 H).1
    obtain ⟨c, hc, hcl⟩ := C1Solution.exists_lam_lower_bound hB hB1 H
    exact hlam.log (fun p hp => ne_of_gt (hc.trans_le (hcl p hp)))
  have hlogJet := vertical_slice_deriv_eq_fderivWithin hB hlog hu huv hv
  have hrne : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hlamne : S.lam u v ≠ 0 := ne_of_gt (H.solution.lam_pos (u, v) hpU)
  have hnune : S.nu u v ≠ 0 := ne_of_lt
    (C1Solution.nu_neg_closed_triangle hB hB1 H hpK)
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hgapne : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hratio := (hBV.mass_ratio_bounds hpU).2
    linarith
  have hCoeff : C1Solution.canonicalMixedCoefficient 1 S (u, v) /
      S.nu u v =
      (2 * S.m u v / S.r u v) /
        (1 - 2 * S.m u v / S.r u v) * (S.lam u v / S.r u v) := by
    rw [C1Solution.canonicalMixedCoefficient_eq_frozen hB hB1 H hu huv hv.le]
    field_simp [hrne, hnune, hgapne]
  have hCorr :
      (fderivWithin ℝ (fun q : ℝ × ℝ => S.phi q.1 q.2) K
        (u, v)) (0, 1) *
        (S.alpha u v / S.lam u v - S.beta u v / S.nu u v) =
      sourceLogCorrection S u v := by
    have hTheta := C1Solution.theta_eq_canonicalRadius_mul_phi_vertical_jet
      hB hB1 H hpK
    rw [C1Solution.canonicalRadius_eq_radius hB hB1 H hu huv hv.le] at hTheta
    rw [eq4_9a S u v hlamne hnune]
    rw [hTheta]
    field_simp [hrne]
    ring
  rw [sourceOutgoingLogResidualClosed, sourceOutgoingLogResidual.eq_1,
    ← hlogJet, hCoeff, hCorr]

/-- In the strict triangle, the continuous incoming representative is the
sign-corrected source residual. -/
theorem sourceIncomingLogResidualClosed_eq {B : ℝ}
    (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < B) :
    sourceIncomingLogResidualClosed B S (u, v) =
      sourceIncomingLogResidual S u v := by
  let K := closedCoordTriangle 0 B
  have hpK : (u, v) ∈ K := ⟨hu.le, huv.le, hv.le⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hu.le, huv, hv.trans hB1⟩
  have hlog : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => Real.log (-S.nu p.1 p.2)) K := by
    have hnu := (C1Solution.five_fields_contDiffOn hB hB1 H).2.1
    exact hnu.neg.log (fun p hp =>
      neg_ne_zero.mpr (C1Solution.nu_neg_closed_triangle hB hB1 H hp).ne)
  have hlogJet := horizontal_slice_deriv_eq_fderivWithin hlog hu huv hv
  have hrne : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hlamne : S.lam u v ≠ 0 := ne_of_gt (H.solution.lam_pos (u, v) hpU)
  have hnune : S.nu u v ≠ 0 := ne_of_lt
    (C1Solution.nu_neg_closed_triangle hB hB1 H hpK)
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hgapne : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hratio := (hBV.mass_ratio_bounds hpU).2
    linarith
  have hCoeff : C1Solution.canonicalMixedCoefficient 1 S (u, v) /
      S.lam u v =
      (2 * S.m u v / S.r u v) /
        (1 - 2 * S.m u v / S.r u v) * (S.nu u v / S.r u v) := by
    rw [C1Solution.canonicalMixedCoefficient_eq_frozen hB hB1 H hu.le huv hv.le]
    field_simp [hrne, hlamne, hgapne]
  have hCorr :
      (fderivWithin ℝ (fun q : ℝ × ℝ => S.phi q.1 q.2) K
        (u, v)) (1, 0) *
        (S.alpha u v / S.lam u v - S.beta u v / S.nu u v) =
      sourceLogCorrectionStar S u v := by
    have hZeta := C1Solution.zeta_eq_canonicalRadius_mul_phi_horizontal_jet
      hB hB1 H hpK
    rw [C1Solution.canonicalRadius_eq_radius hB hB1 H hu.le huv hv.le] at hZeta
    rw [eq4_9b S u v hlamne hnune]
    rw [hZeta]
    field_simp [hrne]
    ring
  rw [sourceIncomingLogResidualClosed, sourceIncomingLogResidual.eq_1,
    ← hlogJet, hCoeff, hCorr]

private theorem outgoing_log_vertical_jet_differentiableAt {B : ℝ}
    (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    DifferentiableAt ℝ
      (fun x => deriv (fun y => Real.log (S.lam x y)) v) u := by
  let T := openCoordTriangle 0 B
  let K := closedCoordTriangle 0 B
  let F : ℝ × ℝ → ℝ := fun p => Real.log (S.lam p.1 p.2)
  let G : ℝ × ℝ → ℝ := fun p =>
    C1Solution.canonicalMixedCoefficient 1 S p / S.lam p.1 p.2
  have hT : IsOpen T := by
    change IsOpen {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < B}
    exact (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const))
  have hsub : T ⊆ K := fun p hp => ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hF : ContDiffOn ℝ 1 F T :=
    (((C1Solution.five_fields_contDiffOn hB hB1 H).1.mono hsub).log
      (fun p hp => (H.solution.lam_pos p
        ⟨hp.1.le, hp.2.1, hp.2.2.trans hB1⟩).ne'))
  have hG : ContDiffOn ℝ 1 G T :=
    (log_transport_coefficients_contDiffOn hB hB1 H).1
  have hsource (p : ℝ × ℝ) (hpT : p ∈ T) :
      (fderiv ℝ F p) (1, 0) = G p :=
    (log_transport_first_jets hB hB1 H hpT).1
  let a := u / 2
  let a' := (u + v) / 2
  let d := (u + 3 * v) / 4
  let d' := (v + B) / 2
  have ha0 : 0 < a := by dsimp [a]; linarith [hp.1]
  have hau : a < u := by dsimp [a]; linarith [hp.1]
  have hua' : u < a' := by dsimp [a']; linarith [hp.2.1]
  have ha'd : a' < d := by dsimp [a', d]; linarith [hp.2.1]
  have hdv : d < v := by dsimp [d]; linarith [hp.2.1]
  have hvd' : v < d' := by dsimp [d']; linarith [hp.2.2]
  have hd'B : d' < B := by dsimp [d']; linarith [hp.2.2]
  have hR : Icc a a' ×ˢ Icc d d' ⊆ T := by
    intro p hpR
    exact ⟨ha0.trans_le hpR.1.1,
      (hpR.1.2.trans_lt ha'd).trans_le hpR.2.1,
      hpR.2.2.trans_lt hd'B⟩
  have hReg := mixed_horizontal_on_rectangle hT hF hG hsource
    (hau.trans hua') (hdv.trans hvd') hR
    ⟨hau.le, hua'.le⟩ ⟨hdv.le, hvd'.le⟩
  have hEq : (fun x => deriv (fun y => F (x, y)) v) =ᶠ[𝓝 u]
      (fun x => (fderiv ℝ F (x, v)) (0, 1)) := by
    filter_upwards [Ioo_mem_nhds hau hua'] with x hx
    have hxp : (x, v) ∈ T := hR
      ⟨⟨hx.1.le, hx.2.le⟩, ⟨hdv.le, hvd'.le⟩⟩
    have hdiff : DifferentiableAt ℝ F (x, v) :=
      (hF.differentiableOn (by norm_num) (x, v) hxp).differentiableAt
        (hT.mem_nhds hxp)
    have hpath : HasDerivAt (fun y : ℝ => (x, y)) (0, 1) v :=
      (hasDerivAt_const v x).prodMk (hasDerivAt_id' v)
    exact (hdiff.hasFDerivAt.comp_hasDerivAt v hpath).deriv
  have hJet : HasDerivAt
      (fun x => (fderiv ℝ F (x, v)) (0, 1))
      ((fderiv ℝ G (u, v)) (0, 1)) u :=
    hReg.hasDerivAt (Icc_mem_nhds hau hua')
  have h := hJet.congr_of_eventuallyEq hEq
  exact h.differentiableAt

private theorem outgoing_mass_correction_differentiableAt {B : ℝ}
    (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    DifferentiableAt ℝ (fun x =>
      (2 * S.m x v / S.r x v) / (1 - 2 * S.m x v / S.r x v) *
        (S.lam x v / S.r x v) - sourceLogCorrection S x v) u := by
  let T := openCoordTriangle 0 B
  let K := closedCoordTriangle 0 B
  have hT : IsOpen T := by
    change IsOpen {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < B}
    exact (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const))
  have hsub : T ⊆ K := fun p hp => ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  obtain ⟨hlamK, hnuK, _, hthetaK, hzetaK⟩ :=
    C1Solution.five_fields_contDiffOn hB hB1 H
  have hlam := hlamK.mono hsub
  have hnu := hnuK.mono hsub
  have htheta := hthetaK.mono hsub
  have hzeta := hzetaK.mono hsub
  have hr := (C1Solution.canonicalRadius_contDiffOn hB hB1 H).mono hsub
  have hlamNe : ∀ p ∈ T, S.lam p.1 p.2 ≠ 0 := by
    intro p hpT
    exact ne_of_gt (H.solution.lam_pos p
      ⟨hpT.1.le, hpT.2.1, hpT.2.2.trans hB1⟩)
  have hnuNe : ∀ p ∈ T, S.nu p.1 p.2 ≠ 0 :=
    fun p hpT => ne_of_lt
      (C1Solution.nu_neg_closed_triangle hB hB1 H (hsub hpT))
  have hrNe : ∀ p ∈ T, C1Solution.canonicalRadius S p ≠ 0 := by
    intro p hpT
    rw [C1Solution.canonicalRadius_eq_radius hB hB1 H
      hpT.1.le hpT.2.1 hpT.2.2.le]
    exact ne_of_gt (H.solution.radius_pos p
      ⟨hpT.1.le, hpT.2.1, hpT.2.2.trans hB1⟩)
  have hCanonicalMass : ContDiffOn ℝ 1
      (fun p => C1Solution.canonicalMixedCoefficient 1 S p / S.nu p.1 p.2) T :=
    (mixed_coefficient_contDiffOn hB hB1 H).div hnu hnuNe
  have hCanonicalCorrection : ContDiffOn ℝ 1
      (fun p => S.theta p.1 p.2 / C1Solution.canonicalRadius S p *
        (S.theta p.1 p.2 / S.lam p.1 p.2 -
          S.zeta p.1 p.2 / S.nu p.1 p.2)) T :=
    (htheta.div hr hrNe).mul
      ((htheta.div hlam hlamNe).sub (hzeta.div hnu hnuNe))
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hMassEq (p : ℝ × ℝ) (hpT : p ∈ T) :
      (2 * S.m p.1 p.2 / S.r p.1 p.2) /
        (1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) *
        (S.lam p.1 p.2 / S.r p.1 p.2) =
      C1Solution.canonicalMixedCoefficient 1 S p / S.nu p.1 p.2 := by
    rcases p with ⟨x, y⟩
    have hpU : (x, y) ∈ developmentWithInitialEdge 1 :=
      ⟨hpT.1.le, hpT.2.1, hpT.2.2.trans hB1⟩
    have hrne : S.r x y ≠ 0 := ne_of_gt (H.solution.radius_pos (x, y) hpU)
    have hnune : S.nu x y ≠ 0 := hnuNe (x, y) hpT
    have hgapne : 1 - 2 * S.m x y / S.r x y ≠ 0 := by
      have hratio := (hBV.mass_ratio_bounds hpU).2
      linarith
    rw [C1Solution.canonicalMixedCoefficient_eq_frozen hB hB1 H
      hpT.1.le hpT.2.1 hpT.2.2.le]
    field_simp [hrne, hnune, hgapne]
  have hCorrEq (p : ℝ × ℝ) (hpT : p ∈ T) :
      sourceLogCorrection S p.1 p.2 =
        S.theta p.1 p.2 / C1Solution.canonicalRadius S p *
          (S.theta p.1 p.2 / S.lam p.1 p.2 -
            S.zeta p.1 p.2 / S.nu p.1 p.2) := by
    rw [sourceLogCorrection.eq_1,
      C1Solution.canonicalRadius_eq_radius hB hB1 H
        hpT.1.le hpT.2.1 hpT.2.2.le]
  have hRaw : ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
      (2 * S.m p.1 p.2 / S.r p.1 p.2) /
        (1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) *
        (S.lam p.1 p.2 / S.r p.1 p.2) -
        sourceLogCorrection S p.1 p.2) T :=
    (hCanonicalMass.congr hMassEq).sub
      (hCanonicalCorrection.congr hCorrEq)
  have hdiff : DifferentiableAt ℝ (fun p : ℝ × ℝ =>
      (2 * S.m p.1 p.2 / S.r p.1 p.2) /
        (1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) *
        (S.lam p.1 p.2 / S.r p.1 p.2) -
        sourceLogCorrection S p.1 p.2) (u, v) :=
    (hRaw.differentiableOn (by norm_num) (u, v) hp).differentiableAt
      (hT.mem_nhds hp)
  exact (hdiff.hasFDerivAt.comp_hasDerivAt u
    ((hasDerivAt_id' u).prodMk (hasDerivAt_const u v))).differentiableAt

private theorem outgoing_closed_residual_hasDerivAt {B : ℝ}
    (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hrGauge : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    HasDerivAt (fun x => sourceOutgoingLogResidualClosed B S (x, v))
      ((fderiv ℝ (sourcePhiBetaNuMap S) (u, v)).det) u := by
  let A : ℝ → ℝ := fun x => deriv (fun y => Real.log (S.lam x y)) v
  let M : ℝ → ℝ := fun x =>
    (2 * S.m x v / S.r x v) / (1 - 2 * S.m x v / S.r x v) *
      (S.lam x v / S.r x v) - sourceLogCorrection S x v
  have hA : DifferentiableAt ℝ A u :=
    outgoing_log_vertical_jet_differentiableAt hB hB1 H hp
  have hM : DifferentiableAt ℝ M u :=
    outgoing_mass_correction_differentiableAt hB hB1 H hp
  have hDiff : deriv A u - deriv M u = sourceJacobianPhiBetaNu S u v := by
    have h := eq4_11a hB hB1 H hrGauge hcenter hboot hp
    dsimp [A, M] at *
    linarith only [h]
  have hRaw : HasDerivAt (fun x => A x - M x)
      (sourceJacobianPhiBetaNu S u v) u := by
    have h := hA.hasDerivAt.sub hM.hasDerivAt
    rw [hDiff] at h
    exact h
  have hEq : (fun x => sourceOutgoingLogResidualClosed B S (x, v)) =ᶠ[𝓝 u]
      (fun x => A x - M x) := by
    filter_upwards [Ioo_mem_nhds hp.1 hp.2.1] with x hx
    rw [sourceOutgoingLogResidualClosed_eq hB hB1 H hx.1.le hx.2 hp.2.2,
      sourceOutgoingLogResidual.eq_1]
    dsimp [A, M]
    ring
  have h := hRaw.congr_of_eventuallyEq hEq
  rw [sourceJacobianPhiBetaNu_eq_det hB hB1 H hp] at h
  exact h

/-- Equation (4.12a): the outgoing residual is bounded by its true initial
edge value and the absolute Jacobian on the preceding characteristic. -/
theorem eq4_12a {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hrGauge : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 1) :
    ENNReal.ofReal |sourceOutgoingLogResidual S u v| ≤
      ENNReal.ofReal |sourceOutgoingLogResidual S 0 v| +
        ∫⁻ x in Ioo 0 u,
          ENNReal.ofReal |(fderiv ℝ (sourcePhiBetaNuMap S) (x, v)).det| := by
  let B : ℝ := (v + 1) / 2
  let K := closedCoordTriangle 0 B
  let F := sourcePhiBetaNuMap S
  let R : ℝ → ℝ := fun x => sourceOutgoingLogResidualClosed B S (x, v)
  let J : ℝ → ℝ := fun x =>
    (fderivWithin ℝ F K (x, v)).det
  have hB : 0 < B := by dsimp [B]; linarith [hp.1, hp.2.1]
  have hB1 : B < 1 := by dsimp [B]; linarith [hp.2.2]
  have hvB : v < B := by dsimp [B]; linarith [hp.2.2]
  have hSeg : ∀ x ∈ Icc (0 : ℝ) u, (x, v) ∈ K := by
    intro x hx
    exact ⟨hx.1, hx.2.trans hp.2.1.le, hvB.le⟩
  have hPath : ContinuousOn (fun x : ℝ => (x, v)) (Icc 0 u) := by
    fun_prop
  have hRcont : ContinuousOn R (Icc 0 u) :=
    (closed_log_residual_data hB hB1 H).1.comp hPath hSeg
  have hUnique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hJcont : ContinuousOn J (Icc 0 u) := by
    have hMap := sourcePhiBetaNuMap_contDiffOn hB hB1 H
    have hWithin := hMap.continuousOn_fderivWithin hUnique (by norm_num)
    have hDet : ContinuousOn (fun p => (fderivWithin ℝ F K p).det) K :=
      ContinuousLinearMap.continuous_det.comp_continuousOn hWithin
    exact hDet.comp hPath hSeg
  have hDeriv (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) u) :
      HasDerivAt R (J x) x := by
    have hpt : (x, v) ∈ openCoordTriangle 0 B :=
      ⟨hx.1, hx.2.trans hp.2.1, hvB⟩
    have hpi : (x, v) ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact hpt
    have hKn : K ∈ 𝓝 (x, v) :=
      mem_of_superset (isOpen_interior.mem_nhds hpi) interior_subset
    have h := outgoing_closed_residual_hasDerivAt hB hB1 H
      hrGauge hcenter hboot hpt
    simpa only [R, J, F, fderivWithin_of_mem_nhds hKn] using h
  have hBound := ofReal_abs_endpoint_le_initial_add_lintegral
    hp.1.le hRcont hJcont hDeriv
  have hIntegral : (∫⁻ x in Ioo 0 u, ENNReal.ofReal |J x|) =
      ∫⁻ x in Ioo 0 u,
        ENNReal.ofReal |(fderiv ℝ F (x, v)).det| := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hpt : (x, v) ∈ openCoordTriangle 0 B :=
      ⟨hx.1, hx.2.trans hp.2.1, hvB⟩
    have hpi : (x, v) ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact hpt
    have hKn : K ∈ 𝓝 (x, v) :=
      mem_of_superset (isOpen_interior.mem_nhds hpi) interior_subset
    simp only [J, fderivWithin_of_mem_nhds hKn]
  have hRu : R u = sourceOutgoingLogResidual S u v :=
    sourceOutgoingLogResidualClosed_eq hB hB1 H hp.1.le hp.2.1 hvB
  have h0v : (0 : ℝ) < v := hp.1.trans hp.2.1
  have hR0 : R 0 = sourceOutgoingLogResidual S 0 v :=
    sourceOutgoingLogResidualClosed_eq hB hB1 H le_rfl h0v hvB
  rw [hIntegral, hRu, hR0] at hBound
  exact hBound

/-- Corrected equation (4.12b): the exact initial residual and the outgoing
analytic Jacobian area control the residual on every ray. The source omitted
the proof of the initial term; its complete value has the established `108 D²`
bound. -/
theorem eq4_12b_corrected {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hrGauge : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ v in Ioo u 1, ENNReal.ofReal |sourceOutgoingLogResidual S u v|) ≤
        (∫⁻ v in Ioo u 1,
          ENNReal.ofReal |sourceOutgoingLogResidual S 0 v|) +
          smoothAnalyticArea (sourcePhiBetaNuMap S)
            (Ioo 0 u ×ˢ Ioo u 1) ∧
    (∫⁻ v in Ioo u 1, ENNReal.ofReal |sourceOutgoingLogResidual S u v|) ≤
        ENNReal.ofReal (108 * (sourceD S).toReal ^ 2) +
          smoothAnalyticArea (sourcePhiBetaNuMap S)
            (openCoordTriangle 0 1) := by
  let A := Ioo (0 : ℝ) u
  let B := Ioo u 1
  let F := sourcePhiBetaNuMap S
  let R : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal |sourceOutgoingLogResidual S u v|
  let I : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal |sourceOutgoingLogResidual S 0 v|
  let J : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal |(fderiv ℝ F p).det|
  have hIInt := initial_log_residual_integrable H hrGauge hcenter hboot
  have hIOn : IntegrableOn (fun v => |sourceOutgoingLogResidual S 0 v|)
      (Ioo (0 : ℝ) 1) := by
    have h := hIInt.1
    exact h.mono_set Ioo_subset_Ioc_self
  have hBSub : B ⊆ Ioo (0 : ℝ) 1 := by
    intro v hv
    exact ⟨hu.1.trans hv.1, hv.2⟩
  have hI : AEMeasurable I (volume.restrict B) :=
    ((hIOn.mono_set hBSub).aestronglyMeasurable.aemeasurable).ennreal_ofReal
  have hJ : AEMeasurable J ((volume.restrict A).prod (volume.restrict B)) :=
    (source_log_jacobian_densities_measurable S).1.aemeasurable
  have hPoint (v : ℝ) (hv : v ∈ B) :
      R v ≤ I v + ∫⁻ x in A, J (x, v) := by
    have hp : (u, v) ∈ openCoordTriangle 0 1 := ⟨hu.1, hv.1, hv.2⟩
    simpa only [R, I, J, F, A] using
      eq4_12a H hrGauge hcenter hboot hp
  have hRaw := lintegral_residual_le_initial_add_rectangle
    A B R I J measurableSet_Ioo hI hJ hPoint
  have hArea : (∫⁻ p in A ×ˢ B, J p) =
      smoothAnalyticArea F (A ×ˢ B) :=
    (smooth_analytic_area F (measurableSet_Ioo.prod measurableSet_Ioo)).symm
  have hFirst : (∫⁻ v in B, R v) ≤
      (∫⁻ v in B, I v) + smoothAnalyticArea F (A ×ˢ B) := by
    simpa only [hArea] using hRaw
  have hInitial : (∫⁻ v in B, I v) ≤
      ENNReal.ofReal (108 * (sourceD S).toReal ^ 2) := by
    have hMono : (∫⁻ v in B, I v) ≤
        ∫⁻ v in Ioo (0 : ℝ) 1, I v := lintegral_mono_set hBSub
    have hReal : (∫⁻ v in Ioo (0 : ℝ) 1, I v) =
        ENNReal.ofReal
          (∫ v in (0 : ℝ)..1, |sourceOutgoingLogResidual S 0 v|) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        integral_Ioc_eq_integral_Ioo]
      exact (ofReal_integral_eq_lintegral_ofReal hIOn
        (Filter.Eventually.of_forall fun _ => abs_nonneg _)).symm
    calc
      (∫⁻ v in B, I v) ≤ ∫⁻ v in Ioo (0 : ℝ) 1, I v := hMono
      _ = ENNReal.ofReal
          (∫ v in (0 : ℝ)..1, |sourceOutgoingLogResidual S 0 v|) := hReal
      _ ≤ ENNReal.ofReal (108 * (sourceD S).toReal ^ 2) :=
        ENNReal.ofReal_le_ofReal (initial_log_residual H hrGauge hcenter hboot)
  have hRect : A ×ˢ B ⊆ openCoordTriangle 0 1 := by
    intro p hp
    exact ⟨hp.1.1, hp.1.2.trans hp.2.1, hp.2.2⟩
  constructor
  · exact hFirst
  · exact hFirst.trans (add_le_add hInitial (measure_mono hRect))

end ChristodoulouBV

end
