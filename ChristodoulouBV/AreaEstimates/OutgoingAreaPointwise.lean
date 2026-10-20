module

public import ChristodoulouBV.AreaEstimates.OutgoingAreaAlgebra
public import ChristodoulouBV.AreaEstimates.ScalarAreaDensityCore
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Pointwise Jacobian identities for the area estimates

The incoming logarithmic residual has the corrected `- f*` sign from the
sign correction of (4.11b)–(4.13b) and its extension to the area estimates;
see ERRATA.md, ERR-23.
-/

public section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Exact outgoing Jacobian decomposition preceding (4.21). -/
theorem sourceLamPhi_jacobian_rho {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (_hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (_hcenter : S.phi 0 0 = 0) (_hboot : s4_bootstrap S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 1) :
    (fderiv ℝ (sourceLamPhiMap S) (u, v)).det =
      -(S.lam u v * S.zeta u v / S.r u v) *
        sourceOutgoingLogResidual S u v +
      S.lam u v * sourceRho S u v / S.r u v ^ 3 *
        (S.theta u v / S.lam u v - S.zeta u v / S.nu u v) := by
  let B : ℝ := (v + 1) / 2
  let K := closedCoordTriangle 0 B
  have hB : 0 < B := by dsimp [B]; linarith only [hp.1, hp.2.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hp.2.2]
  have hvB : v < B := by dsimp [B]; linarith only [hp.2.2]
  have hpK : (u, v) ∈ K := ⟨hp.1.le, hp.2.1.le, hvB.le⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hp.1.le, hp.2.1, hp.2.2⟩
  have hKn : K ∈ 𝓝 (u, v) := by
    apply mem_of_superset (isOpen_interior.mem_nhds ?_) interior_subset
    rw [interior_closedCoordTriangle]
    exact ⟨hp.1, hp.2.1, hvB⟩
  have hfields := C1Solution.five_fields_contDiffOn hB hB1 H
  have hLam : DifferentiableAt ℝ (fun p : ℝ × ℝ => S.lam p.1 p.2) (u, v) :=
    (hfields.1.differentiableOn (by norm_num) _ hpK).differentiableAt hKn
  have hPhi : DifferentiableAt ℝ (fun p : ℝ × ℝ => S.phi p.1 p.2) (u, v) :=
    (hfields.2.2.1.differentiableOn (by norm_num) _ hpK).differentiableAt hKn
  have hLamPos : 0 < S.lam u v := H.solution.lam_pos (u, v) hpU
  have hLamNe : S.lam u v ≠ 0 := ne_of_gt hLamPos
  have hNuNe : S.nu u v ≠ 0 :=
    ne_of_lt (C1Solution.nu_neg_closed_triangle hB hB1 H hpK)
  have hRNe : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hGapNe : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hratio := (hBV.mass_ratio_bounds hpU).2
    linarith
  have hLamU :
      (fderiv ℝ (fun p : ℝ × ℝ => S.lam p.1 p.2) (u, v)) (1, 0) =
        (2 * S.m u v / S.r u v) /
          (1 - 2 * S.m u v / S.r u v) *
            S.lam u v * S.nu u v / S.r u v := by
    rw [← fderivWithin_of_mem_nhds hKn,
      (C1Solution.four_mixed_coordinate_jets hB hB1 H hpK).1,
      C1Solution.canonicalMixedCoefficient_eq_frozen hB hB1 H
        hp.1.le hp.2.1 hvB.le]
    field_simp [hRNe, hGapNe]
  have hPhiU :
      (fderiv ℝ (fun p : ℝ × ℝ => S.phi p.1 p.2) (u, v)) (1, 0) =
        S.zeta u v / S.r u v := by
    have h := C1Solution.zeta_eq_canonicalRadius_mul_phi_horizontal_jet
      hB hB1 H hpK
    rw [C1Solution.canonicalRadius_eq_radius hB hB1 H
      hp.1.le hp.2.1 hvB.le,
      fderivWithin_of_mem_nhds hKn] at h
    apply (eq_div_iff hRNe).2
    simpa only [Prod.fst, Prod.snd, mul_comm] using h.symm
  have hPhiV :
      (fderiv ℝ (fun p : ℝ × ℝ => S.phi p.1 p.2) (u, v)) (0, 1) =
        S.theta u v / S.r u v := by
    have h := C1Solution.theta_eq_canonicalRadius_mul_phi_vertical_jet
      hB hB1 H hpK
    rw [C1Solution.canonicalRadius_eq_radius hB hB1 H
      hp.1.le hp.2.1 hvB.le,
      fderivWithin_of_mem_nhds hKn] at h
    apply (eq_div_iff hRNe).2
    simpa only [Prod.fst, Prod.snd, mul_comm] using h.symm
  have hLamVHas : HasDerivAt (S.lam u)
      ((fderiv ℝ (fun p : ℝ × ℝ => S.lam p.1 p.2) (u, v)) (0, 1)) v := by
    have hline : HasDerivAt (fun t : ℝ => (u, t)) (0, 1) v :=
      (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
    simpa only [Function.comp_def] using
      hLam.hasFDerivAt.comp_hasDerivAt v hline
  have hLog : deriv (fun t => Real.log (S.lam u t)) v =
      (fderiv ℝ (fun p : ℝ × ℝ => S.lam p.1 p.2) (u, v)) (0, 1) /
        S.lam u v := by
    simpa only [div_eq_mul_inv] using (hLamVHas.log hLamNe).deriv
  change (fderiv ℝ (fun p : ℝ × ℝ =>
      (S.lam p.1 p.2, S.phi p.1 p.2)) (u, v)).det = _
  rw [det_fderiv_prodMk hLam hPhi, hPhiU, hPhiV]
  have halg := outgoing_area_jacobian_algebra
    (theta := S.theta u v) (zeta := S.zeta u v)
    (lamV := (fderiv ℝ (fun p : ℝ × ℝ => S.lam p.1 p.2) (u, v)) (0, 1))
    hRNe hLamNe hNuNe hGapNe hLamU
  rw [← hLog] at halg
  convert halg using 1
  unfold sourceOutgoingLogResidual sourceLogCorrection sourceRho
  field_simp [hRNe, hGapNe]

/-- Exact incoming Jacobian decomposition preceding corrected (4.26).
The incoming residual uses `-f*`, as required by the sign correction of
(4.11b)–(4.13b) and its extension to the area estimates; see ERRATA.md, ERR-23. -/
theorem sourceNuPhi_jacobian_rho_corrected {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (_hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (_hcenter : S.phi 0 0 = 0) (_hboot : s4_bootstrap S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 1) :
    (fderiv ℝ (sourceNuPhiMap S) (u, v)).det =
      (S.nu u v * S.theta u v / S.r u v) *
        sourceIncomingLogResidual S u v +
      S.nu u v * sourceRho S u v / S.r u v ^ 3 *
        (S.theta u v / S.lam u v - S.zeta u v / S.nu u v) := by
  let B : ℝ := (v + 1) / 2
  let K := closedCoordTriangle 0 B
  have hB : 0 < B := by dsimp [B]; linarith only [hp.1, hp.2.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hp.2.2]
  have hvB : v < B := by dsimp [B]; linarith only [hp.2.2]
  have hpK : (u, v) ∈ K := ⟨hp.1.le, hp.2.1.le, hvB.le⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hp.1.le, hp.2.1, hp.2.2⟩
  have hKn : K ∈ 𝓝 (u, v) := by
    apply mem_of_superset (isOpen_interior.mem_nhds ?_) interior_subset
    rw [interior_closedCoordTriangle]
    exact ⟨hp.1, hp.2.1, hvB⟩
  have hfields := C1Solution.five_fields_contDiffOn hB hB1 H
  have hNu : DifferentiableAt ℝ (fun p : ℝ × ℝ => S.nu p.1 p.2) (u, v) :=
    (hfields.2.1.differentiableOn (by norm_num) _ hpK).differentiableAt hKn
  have hPhi : DifferentiableAt ℝ (fun p : ℝ × ℝ => S.phi p.1 p.2) (u, v) :=
    (hfields.2.2.1.differentiableOn (by norm_num) _ hpK).differentiableAt hKn
  have hLamNe : S.lam u v ≠ 0 := ne_of_gt (H.solution.lam_pos (u, v) hpU)
  have hNuNeg : S.nu u v < 0 :=
    C1Solution.nu_neg_closed_triangle hB hB1 H hpK
  have hNuNe : S.nu u v ≠ 0 := ne_of_lt hNuNeg
  have hRNe : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hGapNe : 1 - 2 * S.m u v / S.r u v ≠ 0 := by
    have hratio := (hBV.mass_ratio_bounds hpU).2
    linarith
  have hNuV :
      (fderiv ℝ (fun p : ℝ × ℝ => S.nu p.1 p.2) (u, v)) (0, 1) =
        (2 * S.m u v / S.r u v) /
          (1 - 2 * S.m u v / S.r u v) *
            S.lam u v * S.nu u v / S.r u v := by
    rw [← fderivWithin_of_mem_nhds hKn,
      (C1Solution.four_mixed_coordinate_jets hB hB1 H hpK).2.1,
      C1Solution.canonicalMixedCoefficient_eq_frozen hB hB1 H
        hp.1.le hp.2.1 hvB.le]
    field_simp [hRNe, hGapNe]
  have hPhiU :
      (fderiv ℝ (fun p : ℝ × ℝ => S.phi p.1 p.2) (u, v)) (1, 0) =
        S.zeta u v / S.r u v := by
    have h := C1Solution.zeta_eq_canonicalRadius_mul_phi_horizontal_jet
      hB hB1 H hpK
    rw [C1Solution.canonicalRadius_eq_radius hB hB1 H
      hp.1.le hp.2.1 hvB.le,
      fderivWithin_of_mem_nhds hKn] at h
    apply (eq_div_iff hRNe).2
    simpa only [Prod.fst, Prod.snd, mul_comm] using h.symm
  have hPhiV :
      (fderiv ℝ (fun p : ℝ × ℝ => S.phi p.1 p.2) (u, v)) (0, 1) =
        S.theta u v / S.r u v := by
    have h := C1Solution.theta_eq_canonicalRadius_mul_phi_vertical_jet
      hB hB1 H hpK
    rw [C1Solution.canonicalRadius_eq_radius hB hB1 H
      hp.1.le hp.2.1 hvB.le,
      fderivWithin_of_mem_nhds hKn] at h
    apply (eq_div_iff hRNe).2
    simpa only [Prod.fst, Prod.snd, mul_comm] using h.symm
  have hNuUHas : HasDerivAt (fun t => S.nu t v)
      ((fderiv ℝ (fun p : ℝ × ℝ => S.nu p.1 p.2) (u, v)) (1, 0)) u := by
    have hline : HasDerivAt (fun t : ℝ => (t, v)) (1, 0) u :=
      (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
    simpa only [Function.comp_def] using
      hNu.hasFDerivAt.comp_hasDerivAt u hline
  have hLog : deriv (fun t => Real.log (-S.nu t v)) u =
      (fderiv ℝ (fun p : ℝ × ℝ => S.nu p.1 p.2) (u, v)) (1, 0) /
        S.nu u v := by
    have h := (hNuUHas.neg.log (ne_of_gt (neg_pos.mpr hNuNeg))).deriv
    simpa only [Pi.neg_apply, inv_neg, mul_neg, neg_mul, neg_neg,
      div_eq_mul_inv] using h
  change (fderiv ℝ (fun p : ℝ × ℝ =>
      (S.nu p.1 p.2, S.phi p.1 p.2)) (u, v)).det = _
  rw [det_fderiv_prodMk hNu hPhi, hPhiU, hPhiV]
  have halg := incoming_area_jacobian_algebra
    (theta := S.theta u v) (zeta := S.zeta u v)
    (nuU := (fderiv ℝ (fun p : ℝ × ℝ => S.nu p.1 p.2) (u, v)) (1, 0))
    hRNe hLamNe hNuNe hGapNe hNuV
  rw [← hLog] at halg
  convert halg using 1
  unfold sourceIncomingLogResidual sourceLogCorrectionStar sourceRho
  field_simp [hRNe, hGapNe]

end ChristodoulouBV

end
