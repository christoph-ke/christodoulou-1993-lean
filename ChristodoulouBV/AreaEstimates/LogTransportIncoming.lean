module

public import ChristodoulouBV.AreaEstimates.LogTransportIntegral
import all ChristodoulouBV.AreaEstimates.LogTransportCore
import Mathlib.Tactic
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Incoming logarithmic transport to the regular axis

The corrected residual has a continuous axis value. The analytic Jacobian
controls its variation along incoming rays and on the full unit triangle.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

private theorem incoming_log_diagonal_deriv {B : ℝ} (_hB : 0 < B)
    {S : Fields} (hlog : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => Real.log (-S.nu p.1 p.2))
      (closedCoordTriangle 0 B))
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) B) :
    deriv (fun t => Real.log (-S.nu t t)) u =
      (fderivWithin ℝ (fun p : ℝ × ℝ => Real.log (-S.nu p.1 p.2))
        (closedCoordTriangle 0 B) (u, u)) (1, 0) +
      (fderivWithin ℝ (fun p : ℝ × ℝ => Real.log (-S.nu p.1 p.2))
        (closedCoordTriangle 0 B) (u, u)) (0, 1) := by
  let K := closedCoordTriangle 0 B
  have hpK : (u, u) ∈ K := ⟨hu.1.le, le_rfl, hu.2.le⟩
  have hdiff := hlog.differentiableOn (by norm_num) (u, u) hpK
  have hpair : HasDerivAt (fun t : ℝ => (t, t)) (1, 1) u :=
    (hasDerivAt_id' u).prodMk (hasDerivAt_id' u)
  have hnear : ∀ᶠ t in 𝓝 u, (t, t) ∈ K := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with t ht
    exact ⟨ht.1.le, le_rfl, ht.2.le⟩
  have hcomp := hdiff.hasFDerivWithinAt.comp_hasDerivAt
    (f := fun t : ℝ => (t, t)) u hpair hnear
  have hvec : ((1 : ℝ), (1 : ℝ)) =
      ((1 : ℝ), (0 : ℝ)) + (0, 1) := by
    ext <;> norm_num
  rw [hvec, map_add] at hcomp
  simpa only [Function.comp_def] using hcomp.deriv

/-- The sign-corrected incoming logarithmic residual extends to the regular
axis as the derivative of the diagonal logarithmic trace. The mass term and
`f*` both vanish there in their canonical continuous forms. -/
theorem sourceIncomingLogResidualClosed_axis {B : ℝ}
    (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) B) :
    sourceIncomingLogResidualClosed B S (u, u) =
      deriv (fun t => Real.log (-S.nu t t)) u := by
  let K := closedCoordTriangle 0 B
  have hpK : (u, u) ∈ K := ⟨hu.1.le, le_rfl, hu.2.le⟩
  have hUnique : UniqueDiffWithinAt ℝ K (u, u) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB) (u, u) hpK
  have hnu := (C1Solution.five_fields_contDiffOn hB hB1 H).2.1
  have hnuDiff : DifferentiableWithinAt ℝ
      (fun p : ℝ × ℝ => -S.nu p.1 p.2) K (u, u) :=
    (hnu.differentiableOn (by norm_num) (u, u) hpK).neg
  have hnuNe : S.nu u u ≠ 0 := ne_of_lt
    (C1Solution.nu_neg_closed_triangle hB hB1 H hpK)
  have hlog : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => Real.log (-S.nu p.1 p.2)) K :=
    hnu.neg.log (fun p hp => neg_ne_zero.mpr
      (C1Solution.nu_neg_closed_triangle hB hB1 H hp).ne)
  have hnuV := (C1Solution.four_mixed_axis_jets hB hB1 H
    ⟨hu.1.le, hu.2.le⟩).2.1
  have hlogV :
      (fderivWithin ℝ (fun p : ℝ × ℝ => Real.log (-S.nu p.1 p.2))
        K (u, u)) (0, 1) = 0 := by
    rw [fderivWithin.log hnuDiff (neg_ne_zero.mpr hnuNe) hUnique]
    rw [fderivWithin_fun_neg hUnique]
    simp only [smul_apply, neg_apply]
    rw [hnuV]
    simp
  have hLamNe : S.lam u u ≠ 0 := by
    obtain ⟨c, hc, hcl⟩ := C1Solution.exists_lam_lower_bound hB hB1 H
    exact ne_of_gt (hc.trans_le (hcl (u, u) hpK))
  have hQuot :
      S.alpha u u / S.lam u u - S.beta u u / S.nu u u = 0 := by
    rw [C1Solution.alpha_eq_lam_mul_phi_axis hB hB1 H
      ⟨hu.1.le, hu.2.le⟩,
      C1Solution.beta_eq_nu_mul_phi_axis hB hB1 H
      ⟨hu.1.le, hu.2.le⟩]
    field_simp [hLamNe, hnuNe]
    ring
  have hDiag := incoming_log_diagonal_deriv hB hlog hu
  rw [hlogV, add_zero] at hDiag
  rw [sourceIncomingLogResidualClosed,
    C1Solution.canonicalMixedCoefficient_axis, hQuot]
  simp only [zero_div, mul_zero, sub_zero]
  exact hDiag.symm

private theorem incoming_log_horizontal_jet_differentiableAt {B : ℝ}
    (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    DifferentiableAt ℝ
      (fun y => deriv (fun x => Real.log (-S.nu x y)) u) v := by
  let T := openCoordTriangle 0 B
  let K := closedCoordTriangle 0 B
  let F : ℝ × ℝ → ℝ := fun p => Real.log (-S.nu p.1 p.2)
  let G : ℝ × ℝ → ℝ := fun p =>
    C1Solution.canonicalMixedCoefficient 1 S p / S.nu p.1 p.2
  have hT : IsOpen T := by
    change IsOpen {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < B}
    exact (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const))
  have hsub : T ⊆ K := fun p hp => ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hF : ContDiffOn ℝ 1 F T :=
    ((((C1Solution.five_fields_contDiffOn hB hB1 H).2.1.mono hsub).neg).log
      (fun p hp => neg_ne_zero.mpr
        (C1Solution.nu_neg_closed_triangle hB hB1 H (hsub hp)).ne))
  have hG : ContDiffOn ℝ 1 G T :=
    (log_transport_coefficients_contDiffOn hB hB1 H).2
  have hsource (p : ℝ × ℝ) (hpT : p ∈ T) :
      (fderiv ℝ F p) (0, 1) = G p :=
    (log_transport_first_jets hB hB1 H hpT).2
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
  have hReg := mixed_vertical_on_rectangle hT hF hG hsource
    (hau.trans hua') (hdv.trans hvd') hR
    ⟨hau.le, hua'.le⟩ ⟨hdv.le, hvd'.le⟩
  have hEq : (fun y => deriv (fun x => F (x, y)) u) =ᶠ[𝓝 v]
      (fun y => (fderiv ℝ F (u, y)) (1, 0)) := by
    filter_upwards [Ioo_mem_nhds hdv hvd'] with y hy
    have hyp : (u, y) ∈ T := hR
      ⟨⟨hau.le, hua'.le⟩, ⟨hy.1.le, hy.2.le⟩⟩
    have hdiff : DifferentiableAt ℝ F (u, y) :=
      (hF.differentiableOn (by norm_num) (u, y) hyp).differentiableAt
        (hT.mem_nhds hyp)
    have hpath : HasDerivAt (fun x : ℝ => (x, y)) (1, 0) u :=
      (hasDerivAt_id' u).prodMk (hasDerivAt_const u y)
    exact (hdiff.hasFDerivAt.comp_hasDerivAt u hpath).deriv
  have hJet : HasDerivAt
      (fun y => (fderiv ℝ F (u, y)) (1, 0))
      ((fderiv ℝ G (u, v)) (1, 0)) v :=
    hReg.hasDerivAt (Icc_mem_nhds hdv hvd')
  have h := hJet.congr_of_eventuallyEq hEq
  exact h.differentiableAt

private theorem incoming_mass_correction_differentiableAt {B : ℝ}
    (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    DifferentiableAt ℝ (fun y =>
      (2 * S.m u y / S.r u y) / (1 - 2 * S.m u y / S.r u y) *
        (S.nu u y / S.r u y) + sourceLogCorrectionStar S u y) v := by
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
      (fun p => C1Solution.canonicalMixedCoefficient 1 S p / S.lam p.1 p.2) T :=
    (mixed_coefficient_contDiffOn hB hB1 H).div hlam hlamNe
  have hCanonicalCorrection : ContDiffOn ℝ 1
      (fun p => S.zeta p.1 p.2 / C1Solution.canonicalRadius S p *
        (S.theta p.1 p.2 / S.lam p.1 p.2 -
          S.zeta p.1 p.2 / S.nu p.1 p.2)) T :=
    (hzeta.div hr hrNe).mul
      ((htheta.div hlam hlamNe).sub (hzeta.div hnu hnuNe))
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hMassEq (p : ℝ × ℝ) (hpT : p ∈ T) :
      (2 * S.m p.1 p.2 / S.r p.1 p.2) /
        (1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) *
        (S.nu p.1 p.2 / S.r p.1 p.2) =
      C1Solution.canonicalMixedCoefficient 1 S p / S.lam p.1 p.2 := by
    rcases p with ⟨x, y⟩
    have hpU : (x, y) ∈ developmentWithInitialEdge 1 :=
      ⟨hpT.1.le, hpT.2.1, hpT.2.2.trans hB1⟩
    have hrne : S.r x y ≠ 0 := ne_of_gt (H.solution.radius_pos (x, y) hpU)
    have hlamne : S.lam x y ≠ 0 := hlamNe (x, y) hpT
    have hgapne : 1 - 2 * S.m x y / S.r x y ≠ 0 := by
      have hratio := (hBV.mass_ratio_bounds hpU).2
      linarith
    rw [C1Solution.canonicalMixedCoefficient_eq_frozen hB hB1 H
      hpT.1.le hpT.2.1 hpT.2.2.le]
    field_simp [hrne, hlamne, hgapne]
  have hCorrEq (p : ℝ × ℝ) (hpT : p ∈ T) :
      sourceLogCorrectionStar S p.1 p.2 =
        S.zeta p.1 p.2 / C1Solution.canonicalRadius S p *
          (S.theta p.1 p.2 / S.lam p.1 p.2 -
            S.zeta p.1 p.2 / S.nu p.1 p.2) := by
    rw [sourceLogCorrectionStar.eq_1,
      C1Solution.canonicalRadius_eq_radius hB hB1 H
        hpT.1.le hpT.2.1 hpT.2.2.le]
  have hRaw : ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
      (2 * S.m p.1 p.2 / S.r p.1 p.2) /
        (1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) *
        (S.nu p.1 p.2 / S.r p.1 p.2) +
        sourceLogCorrectionStar S p.1 p.2) T :=
    (hCanonicalMass.congr hMassEq).add
      (hCanonicalCorrection.congr hCorrEq)
  have hdiff : DifferentiableAt ℝ (fun p : ℝ × ℝ =>
      (2 * S.m p.1 p.2 / S.r p.1 p.2) /
        (1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) *
        (S.nu p.1 p.2 / S.r p.1 p.2) +
        sourceLogCorrectionStar S p.1 p.2) (u, v) :=
    (hRaw.differentiableOn (by norm_num) (u, v) hp).differentiableAt
      (hT.mem_nhds hp)
  exact (hdiff.hasFDerivAt.comp_hasDerivAt v
    ((hasDerivAt_const v u).prodMk (hasDerivAt_id' v))).differentiableAt

private theorem incoming_closed_residual_hasDerivAt {B : ℝ}
    (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hrGauge : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    HasDerivAt (fun y => sourceIncomingLogResidualClosed B S (u, y))
      (-(fderiv ℝ (sourcePhiAlphaLamMap S) (u, v)).det) v := by
  let A : ℝ → ℝ := fun y => deriv (fun x => Real.log (-S.nu x y)) u
  let M : ℝ → ℝ := fun y =>
    (2 * S.m u y / S.r u y) / (1 - 2 * S.m u y / S.r u y) *
      (S.nu u y / S.r u y) + sourceLogCorrectionStar S u y
  have hA : DifferentiableAt ℝ A v :=
    incoming_log_horizontal_jet_differentiableAt hB hB1 H hp
  have hM : DifferentiableAt ℝ M v :=
    incoming_mass_correction_differentiableAt hB hB1 H hp
  have hDiff : deriv A v - deriv M v = -sourceJacobianPhiAlphaLam S u v := by
    have h := eq4_11b_corrected hB hB1 H hrGauge hcenter hboot hp
    dsimp [A, M] at *
    linarith only [h]
  have hRaw : HasDerivAt (fun y => A y - M y)
      (-sourceJacobianPhiAlphaLam S u v) v := by
    have h := hA.hasDerivAt.sub hM.hasDerivAt
    rw [hDiff] at h
    exact h
  have hEq : (fun y => sourceIncomingLogResidualClosed B S (u, y)) =ᶠ[𝓝 v]
      (fun y => A y - M y) := by
    filter_upwards [Ioo_mem_nhds hp.2.1 hp.2.2] with y hy
    rw [sourceIncomingLogResidualClosed_eq hB hB1 H hp.1 hy.1 hy.2,
      sourceIncomingLogResidual.eq_1]
    dsimp [A, M]
    ring
  have h := hRaw.congr_of_eventuallyEq hEq
  rw [sourceJacobianPhiAlphaLam_eq_det hB hB1 H hp] at h
  exact h

/-- Sign-corrected equation (4.13a): the incoming residual with `− f*` is
bounded by the diagonal log derivative and the absolute `(φ, α/λ)` Jacobian. -/
theorem eq4_13a {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hrGauge : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 1) :
    ENNReal.ofReal |sourceIncomingLogResidual S u v| ≤
      ENNReal.ofReal |deriv (fun t => Real.log (-S.nu t t)) u| +
        ∫⁻ y in Ioo u v,
          ENNReal.ofReal |(fderiv ℝ (sourcePhiAlphaLamMap S) (u, y)).det| := by
  let B : ℝ := (v + 1) / 2
  let K := closedCoordTriangle 0 B
  let F := sourcePhiAlphaLamMap S
  let R : ℝ → ℝ := fun y => sourceIncomingLogResidualClosed B S (u, y)
  let J : ℝ → ℝ := fun y =>
    -(fderivWithin ℝ F K (u, y)).det
  have hB : 0 < B := by dsimp [B]; linarith [hp.1, hp.2.1]
  have hB1 : B < 1 := by dsimp [B]; linarith [hp.2.2]
  have hvB : v < B := by dsimp [B]; linarith [hp.2.2]
  have hSeg : ∀ y ∈ Icc u v, (u, y) ∈ K := by
    intro y hy
    exact ⟨hp.1.le, hy.1, hy.2.trans hvB.le⟩
  have hPath : ContinuousOn (fun y : ℝ => (u, y)) (Icc u v) := by
    fun_prop
  have hRcont : ContinuousOn R (Icc u v) :=
    (closed_log_residual_data hB hB1 H).2.comp hPath hSeg
  have hUnique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hJcont : ContinuousOn J (Icc u v) := by
    have hMap := sourcePhiAlphaLamMap_contDiffOn hB hB1 H
    have hWithin := hMap.continuousOn_fderivWithin hUnique (by norm_num)
    have hDet : ContinuousOn (fun p => -(fderivWithin ℝ F K p).det) K :=
      (ContinuousLinearMap.continuous_det.comp_continuousOn hWithin).neg
    exact hDet.comp hPath hSeg
  have hDeriv (y : ℝ) (hy : y ∈ Ioo u v) :
      HasDerivAt R (J y) y := by
    have hpt : (u, y) ∈ openCoordTriangle 0 B :=
      ⟨hp.1, hy.1, hy.2.trans hvB⟩
    have hpi : (u, y) ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact hpt
    have hKn : K ∈ 𝓝 (u, y) :=
      mem_of_superset (isOpen_interior.mem_nhds hpi) interior_subset
    have h := incoming_closed_residual_hasDerivAt hB hB1 H
      hrGauge hcenter hboot hpt
    simpa only [R, J, F, fderivWithin_of_mem_nhds hKn] using h
  have hBound := ofReal_abs_endpoint_le_initial_add_lintegral
    hp.2.1.le hRcont hJcont hDeriv
  have hIntegral : (∫⁻ y in Ioo u v, ENNReal.ofReal |J y|) =
      ∫⁻ y in Ioo u v,
        ENNReal.ofReal |(fderiv ℝ F (u, y)).det| := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hpt : (u, y) ∈ openCoordTriangle 0 B :=
      ⟨hp.1, hy.1, hy.2.trans hvB⟩
    have hpi : (u, y) ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact hpt
    have hKn : K ∈ 𝓝 (u, y) :=
      mem_of_superset (isOpen_interior.mem_nhds hpi) interior_subset
    simp only [J, fderivWithin_of_mem_nhds hKn, abs_neg]
  have hRv : R v = sourceIncomingLogResidual S u v :=
    sourceIncomingLogResidualClosed_eq hB hB1 H hp.1 hp.2.1 hvB
  have huB : u ∈ Ioo (0 : ℝ) B := ⟨hp.1, hp.2.1.trans hvB⟩
  have hRu : R u = deriv (fun t => Real.log (-S.nu t t)) u :=
    sourceIncomingLogResidualClosed_axis hB hB1 H huB
  rw [hIntegral, hRv, hRu] at hBound
  exact hBound

/-- The diagonal log derivative on a finite initial axis segment is bounded
by variation of the full diagonal trace. -/
theorem axis_log_derivative_lintegral_le_variation {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ u in Ioo 0 v,
      ENNReal.ofReal |deriv (fun t => Real.log (-S.nu t t)) u|) ≤
      eVariationOn (fun t => Real.log (-S.nu t t)) (Ioo 0 1) := by
  let B : ℝ := (v + 1) / 2
  let K := closedCoordTriangle 0 B
  let L : ℝ → ℝ := fun t => Real.log (-S.nu t t)
  have hB : 0 < B := by dsimp [B]; linarith [hv.1]
  have hB1 : B < 1 := by dsimp [B]; linarith [hv.2]
  have hvB : v < B := by dsimp [B]; linarith [hv.2]
  have hnu := (C1Solution.five_fields_contDiffOn hB hB1 H).2.1
  have hlog : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => Real.log (-S.nu p.1 p.2)) K :=
    hnu.neg.log (fun p hp => neg_ne_zero.mpr
      (C1Solution.nu_neg_closed_triangle hB hB1 H hp).ne)
  have hmap : MapsTo (fun t : ℝ => (t, t)) (Icc 0 v) K := by
    intro t ht
    exact ⟨ht.1, le_rfl, ht.2.trans hvB.le⟩
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => (t, t)) (Icc 0 v) := by
    fun_prop
  have hAxis : ContDiffOn ℝ 1 L (Icc 0 v) :=
    hlog.comp hpair hmap
  have hAC : AbsolutelyContinuousOnInterval L 0 v :=
    (show ContDiffOn ℝ 1 L (uIcc 0 v) by
      simpa only [uIcc_of_le hv.1.le] using hAxis).absolutelyContinuousOnInterval
  have hEq : (∫⁻ u in Ioo 0 v, ENNReal.ofReal |deriv L u|) =
      eVariationOn L (Ioo 0 v) :=
    null_lintegral_eq_scalar_variation hv.1.le hAC (fun _ _ => rfl)
  rw [hEq]
  apply eVariationOn.mono
  intro u hu
  exact ⟨hu.1, hu.2.trans hv.2⟩

/-- Sign-corrected equation (4.13b): the incoming residual with `− f*` has
integral bounded by diagonal log variation and the analytic `(φ, α/λ)` area.
The first bound retains the preceding triangle; the second uses the unit
triangle as in the source display. -/
theorem eq4_13b_corrected {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hrGauge : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ u in Ioo 0 v, ENNReal.ofReal |sourceIncomingLogResidual S u v|) ≤
        eVariationOn (fun t => Real.log (-S.nu t t)) (Ioo 0 1) +
          smoothAnalyticArea (sourcePhiAlphaLamMap S)
            (openCoordTriangle 0 v) ∧
    (∫⁻ u in Ioo 0 v, ENNReal.ofReal |sourceIncomingLogResidual S u v|) ≤
        eVariationOn (fun t => Real.log (-S.nu t t)) (Ioo 0 1) +
          smoothAnalyticArea (sourcePhiAlphaLamMap S)
            (openCoordTriangle 0 1) := by
  let A := Ioo (0 : ℝ) v
  let E := openCoordTriangle 0 v
  let F := sourcePhiAlphaLamMap S
  let R : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal |sourceIncomingLogResidual S u v|
  let I : ℝ → ℝ≥0∞ := fun u =>
    ENNReal.ofReal |deriv (fun t => Real.log (-S.nu t t)) u|
  let J : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal |(fderiv ℝ F p).det|
  have hI : AEMeasurable I (volume.restrict A) :=
    ((measurable_deriv (fun t => Real.log (-S.nu t t))).abs.ennreal_ofReal).aemeasurable
  have hJ : AEMeasurable J (volume.restrict E) :=
    (source_log_jacobian_densities_measurable S).2.aemeasurable
  have hPoint (u : ℝ) (hu : u ∈ A) :
      R u ≤ I u + ∫⁻ y in Ioo u v, J (u, y) := by
    have hp : (u, v) ∈ openCoordTriangle 0 1 :=
      ⟨hu.1, hu.2, hv.2⟩
    simpa only [R, I, J, F] using
      eq4_13a H hrGauge hcenter hboot hp
  have hRaw : (∫⁻ u in A, R u) ≤
      (∫⁻ u in A, I u) + ∫⁻ p in E, J p := by
    calc
      (∫⁻ u in A, R u) ≤
          ∫⁻ u in A, I u + ∫⁻ y in Ioo u v, J (u, y) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        exact hPoint u hu
      _ = (∫⁻ u in A, I u) +
          ∫⁻ u in A, ∫⁻ y in Ioo u v, J (u, y) := by
        rw [lintegral_add_left' hI]
      _ = (∫⁻ u in A, I u) + ∫⁻ p in E, J p := by
        congr 1
        have hSet : E =
            {p : ℝ × ℝ | p.1 ∈ Ioo 0 v ∧ p.2 ∈ Ioo p.1 v} := by
          ext p
          simp only [E, openCoordTriangle, mem_ofPred_eq, mem_Ioo]
          constructor
          · rintro ⟨h0, h12, h2v⟩
            exact ⟨⟨h0, h12.trans h2v⟩, ⟨h12, h2v⟩⟩
          · rintro ⟨⟨h0, _⟩, ⟨h12, h2v⟩⟩
            exact ⟨h0, h12, h2v⟩
        exact (lintegral_open_triangle 0 v J (by
          simpa only [← hSet] using hJ)).symm.trans (by rw [← hSet])
  have hOpen : IsOpen E := by
    change IsOpen (openCoordTriangle 0 v)
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior
  have hArea : (∫⁻ p in E, J p) = smoothAnalyticArea F E :=
    (smooth_analytic_area F hOpen.measurableSet).symm
  have hFirst : (∫⁻ u in A, R u) ≤
      eVariationOn (fun t => Real.log (-S.nu t t)) (Ioo 0 1) +
        smoothAnalyticArea F E := by
    calc
      (∫⁻ u in A, R u) ≤ (∫⁻ u in A, I u) + ∫⁻ p in E, J p := hRaw
      _ ≤ eVariationOn (fun t => Real.log (-S.nu t t)) (Ioo 0 1) +
          smoothAnalyticArea F E := by
        rw [hArea]
        exact add_le_add
          (axis_log_derivative_lintegral_le_variation H hv) le_rfl
  have hSub : E ⊆ openCoordTriangle 0 1 := by
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.trans hv.2⟩
  constructor
  · exact hFirst
  · exact hFirst.trans (add_le_add le_rfl (measure_mono hSub))

end ChristodoulouBV

end
