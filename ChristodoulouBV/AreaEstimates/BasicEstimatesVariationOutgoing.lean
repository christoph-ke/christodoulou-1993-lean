module

public import ChristodoulouBV.AreaEstimates.BasicEstimatesVariationCore
public import ChristodoulouBV.AreaEstimates.GaugeAxis
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Outgoing variation bound of Lemma 4.1

The weighted numerator is formed from the canonical radius and scalar
radius. This avoids assigning a value to the frozen radius on the axis.
-/

public section

open Set MeasureTheory Filter
open scoped Topology Interval

namespace ChristodoulouBV

private theorem deriv_vertical_slice {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 1))
    {u t : ℝ} (hu : 0 < u) (hut : u < t) (ht : t < 1) :
    deriv (fun s => F (u, s)) t =
      (fderivWithin ℝ F (closedCoordTriangle 0 1) (u, t)) (0, 1) := by
  let K := closedCoordTriangle 0 1
  have hp : (u, t) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact ⟨hu, hut, ht⟩
  have hpK : (u, t) ∈ K := interior_subset hp
  have hdiff : DifferentiableAt ℝ F (u, t) :=
    ((hF.differentiableOn (by norm_num)).mono interior_subset (u, t) hp)
      |>.differentiableAt (isOpen_interior.mem_nhds hp)
  have hpair : HasDerivAt (fun s : ℝ => (u, s)) (0, 1) t :=
    (hasDerivAt_const t u).prodMk (hasDerivAt_id' t)
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt t hpair
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 1)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty (by norm_num))
  rw [fderivWithin_eq_fderiv (hunique (u, t) hpK) hdiff]
  simpa only [Function.comp_def] using hcomp.deriv

private theorem outgoing_weighted_numerator_interval {b u c : ℝ}
    (hb : 1 < b) (hu : u ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo u 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    let F : ℝ → ℝ := fun t => S.alpha u t / S.lam u t
    let I : ℝ → ℝ := fun t =>
      C1Solution.canonicalRadius S (u, t) * F t -
        C1Solution.canonicalScalarRadius S (u, t)
    (∫ t in c..1,
      |I t| * S.lam u t / (C1Solution.canonicalRadius S (u, t)) ^ 2) ≤
      |I c| / C1Solution.canonicalRadius S (u, c) +
        ∫ t in c..1, |deriv F t| := by
  dsimp only
  let K := closedCoordTriangle 0 1
  let R : ℝ × ℝ → ℝ := C1Solution.canonicalRadius S
  let N : ℝ × ℝ → ℝ := C1Solution.canonicalScalarRadius S
  let Q : ℝ × ℝ → ℝ := C1Solution.outgoingQuotient S
  let F : ℝ → ℝ := fun t => Q (u, t)
  let I : ℝ → ℝ := fun t => R (u, t) * F t - N (u, t)
  have hR : ContDiffOn ℝ 1 R K :=
    C1Solution.canonicalRadius_contDiffOn (by norm_num) hb H
  have hN : ContDiffOn ℝ 1 N K :=
    C1Solution.canonicalScalarRadius_contDiffOn (by norm_num) hb H
  have hQ : ContDiffOn ℝ 1 Q K :=
    C1Solution.alpha_div_lam_contDiffOn (by norm_num) hb H
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc c 1) K := by
    intro t ht
    exact ⟨hu.1.le, (hc.1.trans_le ht.1).le, ht.2⟩
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => (u, t)) (Icc c 1) := by
    fun_prop
  have hRs : ContDiffOn ℝ 1 (fun t => R (u, t)) (Icc c 1) :=
    hR.comp hpair hmap
  have hNs : ContDiffOn ℝ 1 (fun t => N (u, t)) (Icc c 1) :=
    hN.comp hpair hmap
  have hFs : ContDiffOn ℝ 1 F (Icc c 1) :=
    hQ.comp hpair hmap
  have hIs : ContDiffOn ℝ 1 I (Icc c 1) :=
    (hRs.mul hFs).sub hNs
  have hRpos : ∀ t ∈ Icc c 1, 0 < R (u, t) := by
    intro t ht
    change 0 < C1Solution.canonicalRadius S (u, t)
    rw [C1Solution.canonicalRadius_eq_radius (by norm_num) hb H
      hu.1.le (hc.1.trans_le ht.1) ht.2]
    exact H.solution.radius_pos (u, t)
      ⟨hu.1.le, hc.1.trans_le ht.1, ht.2.trans_lt hb⟩
  have hIderiv : ∀ t ∈ Ioo c 1,
      deriv I t = R (u, t) * deriv F t := by
    intro t ht
    have hut : u < t := hc.1.trans ht.1
    have hpK : (u, t) ∈ K := ⟨hu.1.le, hut.le, ht.2.le⟩
    have hlamPos : 0 < S.lam u t :=
      H.solution.lam_pos (u, t) ⟨hu.1.le, hut, ht.2.trans hb⟩
    have hRd := deriv_vertical_slice hR hu.1 hut ht.2
    have hNd := deriv_vertical_slice hN hu.1 hut ht.2
    rw [C1Solution.canonicalRadius_vertical_jet
      (by norm_num) hb H hpK] at hRd
    rw [C1Solution.canonicalScalarRadius_vertical_jet
      (by norm_num) hb H hpK] at hNd
    have hRdiff : DifferentiableAt ℝ (fun s => R (u, s)) t :=
      (hRs.differentiableOn (by norm_num) t
        ⟨ht.1.le, ht.2.le⟩).differentiableAt
        (Icc_mem_nhds ht.1 ht.2)
    have hFdiff : DifferentiableAt ℝ F t :=
      (hFs.differentiableOn (by norm_num) t
        ⟨ht.1.le, ht.2.le⟩).differentiableAt
        (Icc_mem_nhds ht.1 ht.2)
    have hNdiff : DifferentiableAt ℝ (fun s => N (u, s)) t :=
      (hNs.differentiableOn (by norm_num) t
        ⟨ht.1.le, ht.2.le⟩).differentiableAt
        (Icc_mem_nhds ht.1 ht.2)
    change deriv (fun s => R (u, s) * F s - N (u, s)) t = _
    have hprodDeriv := deriv_mul hRdiff hFdiff
    change deriv (fun s => R (u, s) * F s) t =
      deriv (fun s => R (u, s)) t * F t + R (u, t) * deriv F t at hprodDeriv
    have hsubDeriv := deriv_sub (hRdiff.mul hFdiff) hNdiff
    change deriv (fun s => R (u, s) * F s - N (u, s)) t =
      deriv (fun s => R (u, s) * F s) t - deriv (fun s => N (u, s)) t at hsubDeriv
    rw [hsubDeriv, hprodDeriv, hRd, hNd]
    dsimp [F, Q, C1Solution.outgoingQuotient]
    field_simp [hlamPos.ne']
    ring
  have hcore := weighted_numerator_finite_interval_bound hc.2.le
    hIs hRs hFs hRpos hIderiv
  have hRderiv : ∀ t ∈ Ioo c 1,
      deriv (fun s => R (u, s)) t = S.lam u t := by
    intro t ht
    have hpK : (u, t) ∈ K :=
      ⟨hu.1.le, (hc.1.trans ht.1).le, ht.2.le⟩
    exact (deriv_vertical_slice hR hu.1 (hc.1.trans ht.1) ht.2).trans
      (C1Solution.canonicalRadius_vertical_jet (by norm_num) hb H hpK)
  have hleft : (∫ t in c..1,
      |I t| * deriv (fun s => R (u, s)) t / (R (u, t)) ^ 2) =
      ∫ t in c..1, |I t| * S.lam u t / (R (u, t)) ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with t hne ht
    rw [uIoc_of_le hc.2.le] at ht
    exact congrArg (fun x => |I t| * x / (R (u, t)) ^ 2)
      (hRderiv t ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩)
  rw [hleft] at hcore
  exact hcore

/-- The outgoing variation estimate on a slice kept away from the regular
axis. The boundary term is removed when the lower endpoint approaches `u`. -/
theorem outgoing_scalar_interval_bound {b u c : ℝ}
    (hb : 1 < b) (hu : u ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo u 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    (∫ t in c..1, |S.theta u t| / S.r u t) ≤
      |sourceI S u c| / S.r u c +
        ∫ t in c..1, |deriv (fun s => S.alpha u s / S.lam u s) t| := by
  let R : ℝ × ℝ → ℝ := C1Solution.canonicalRadius S
  let N : ℝ × ℝ → ℝ := C1Solution.canonicalScalarRadius S
  let F : ℝ → ℝ := fun t => S.alpha u t / S.lam u t
  let I : ℝ → ℝ := fun t => R (u, t) * F t - N (u, t)
  have hbase := outgoing_weighted_numerator_interval hb hu hc H
  change (∫ t in c..1, |I t| * S.lam u t / (R (u, t)) ^ 2) ≤
      |I c| / R (u, c) + ∫ t in c..1, |deriv F t| at hbase
  have hpoint (t : ℝ) (ht : t ∈ Ico c 1) :
      |S.theta u t| / S.r u t =
        |I t| * S.lam u t / (R (u, t)) ^ 2 := by
    have hut : u < t := hc.1.trans_le ht.1
    have hr := C1Solution.canonicalRadius_eq_radius (by norm_num) hb H
      hu.1.le hut ht.2.le
    have hn := C1Solution.canonicalScalarRadius_eq_radius_mul_phi
      (by norm_num) hb H hu.1.le hut ht.2.le
    have hlam : 0 < S.lam u t :=
      H.solution.lam_pos (u, t) ⟨hu.1.le, hut, ht.2.trans hb⟩
    have hrpos : 0 < S.r u t :=
      H.solution.radius_pos (u, t) ⟨hu.1.le, hut, ht.2.trans hb⟩
    change R (u, t) = S.r u t at hr
    change N (u, t) = S.r u t * S.phi u t at hn
    dsimp [I, F]
    rw [hr, hn]
    unfold Fields.theta
    have hfact : S.alpha u t - S.lam u t * S.phi u t =
        S.lam u t * (S.alpha u t / S.lam u t - S.phi u t) := by
      field_simp [hlam.ne']
    rw [hfact, abs_mul, abs_of_pos hlam]
    rw [← mul_sub, abs_mul, abs_of_pos hrpos]
    field_simp [hrpos.ne']
  have hleft : (∫ t in c..1, |S.theta u t| / S.r u t) =
      ∫ t in c..1, |I t| * S.lam u t / (R (u, t)) ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with t hne ht
    rw [uIoc_of_le hc.2.le] at ht
    exact hpoint t ⟨ht.1.le, lt_of_le_of_ne ht.2 hne⟩
  have hIc : I c = sourceI S u c := by
    have hr := C1Solution.canonicalRadius_eq_radius (by norm_num) hb H
      hu.1.le hc.1 hc.2.le
    have hn := C1Solution.canonicalScalarRadius_eq_radius_mul_phi
      (by norm_num) hb H hu.1.le hc.1 hc.2.le
    have hi := sourceI_eq_radius_mul_quotient_sub_phi (by norm_num) hb H
      hu.1.le hc.1 hc.2.le
    change R (u, c) * (S.alpha u c / S.lam u c) - N (u, c) =
      sourceI S u c
    dsimp [R, N]
    rw [hr, hn, hi]
    ring
  have hRc : R (u, c) = S.r u c :=
    C1Solution.canonicalRadius_eq_radius (by norm_num) hb H
      hu.1.le hc.1 hc.2.le
  rw [hIc, hRc] at hbase
  rw [hleft]
  simpa only [F] using hbase

/-- The outgoing scalar derivative is the source integrand on the open
development. -/
theorem outgoing_theta_over_r_eq_abs_phi_deriv {b u t : ℝ}
    (hb : 1 < b) (hu : u ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo u 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    |S.theta u t| / S.r u t = |deriv (S.phi u) t| := by
  let K := closedCoordTriangle 0 1
  have hphi : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => S.phi p.1 p.2) K :=
    (C1Solution.five_fields_contDiffOn (by norm_num) hb H).2.2.1
  have hpK : (u, t) ∈ K := ⟨hu.1.le, ht.1.le, ht.2.le⟩
  have hderiv := deriv_vertical_slice hphi hu.1 ht.1 ht.2
  have htheta := C1Solution.theta_eq_canonicalRadius_mul_phi_vertical_jet
    (by norm_num) hb H hpK
  have hr := C1Solution.canonicalRadius_eq_radius (by norm_num) hb H
    hu.1.le ht.1 ht.2.le
  have hrpos : 0 < S.r u t :=
    H.solution.radius_pos (u, t) ⟨hu.1.le, ht.1, ht.2.trans hb⟩
  rw [hr, ← hderiv] at htheta
  rw [htheta, abs_mul, abs_of_pos hrpos]
  field_simp [hrpos.ne']

/-- The outgoing integral estimate after the regular-axis boundary term
has vanished. -/
theorem outgoing_scalar_integral_bound {b u : ℝ}
    (hb : 1 < b) (hu : u ∈ Ioo (0 : ℝ) 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    (∫ t in u..1, |deriv (S.phi u) t|) ≤
      ∫ t in u..1,
        |deriv (fun s => S.alpha u s / S.lam u s) t| := by
  let K := closedCoordTriangle 0 1
  let F : ℝ → ℝ := fun t => S.alpha u t / S.lam u t
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc u 1) K := by
    intro t ht
    exact ⟨hu.1.le, ht.1, ht.2⟩
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => (u, t)) (Icc u 1) := by
    fun_prop
  have hphi : ContDiffOn ℝ 1 (S.phi u) (Icc u 1) :=
    ((C1Solution.five_fields_contDiffOn (by norm_num) hb H).2.2.1).comp
      hpair hmap
  have hF : ContDiffOn ℝ 1 F (Icc u 1) :=
    (C1Solution.alpha_div_lam_contDiffOn (by norm_num) hb H).comp
      hpair hmap
  have hphiAC : AbsolutelyContinuousOnInterval (S.phi u) u 1 :=
    (show ContDiffOn ℝ 1 (S.phi u) (uIcc u 1) by
      simpa only [uIcc_of_le hu.2.le] using hphi).absolutelyContinuousOnInterval
  have hFAC : AbsolutelyContinuousOnInterval F u 1 :=
    (show ContDiffOn ℝ 1 F (uIcc u 1) by
      simpa only [uIcc_of_le hu.2.le] using hF).absolutelyContinuousOnInterval
  have hq := s4_i_axis (by norm_num) hb H hu
  apply interval_bound_of_vanishing_left_boundary hu.2
    hphiAC.intervalIntegrable_deriv.abs hFAC.intervalIntegrable_deriv.abs hq
  intro c hc
  have hfinite := outgoing_scalar_interval_bound hb hu hc H
  have hleft : (∫ t in c..1, |deriv (S.phi u) t|) =
      ∫ t in c..1, |S.theta u t| / S.r u t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with t hne ht
    rw [uIoc_of_le hc.2.le] at ht
    symm
    exact outgoing_theta_over_r_eq_abs_phi_deriv hb hu
      ⟨hc.1.trans ht.1, lt_of_le_of_ne ht.2 hne⟩ H
  rw [hleft]
  have hrpos : 0 < S.r u c :=
    H.solution.radius_pos (u, c) ⟨hu.1.le, hc.1, hc.2.trans hb⟩
  rw [abs_div, abs_of_pos hrpos]
  simpa only [F] using hfinite

/-- The outgoing half of Lemma 4.1, with the source's extended integral
and total variation on the open characteristic. -/
theorem outgoing_scalar_variation_bound {b u : ℝ}
    (hb : 1 < b) (hu : u ∈ Ioo (0 : ℝ) 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    (∫⁻ t in Ioo u 1, ENNReal.ofReal (|S.theta u t| / S.r u t)) ≤
      eVariationOn (fun t => S.alpha u t / S.lam u t) (Ioo u 1) := by
  let K := closedCoordTriangle 0 1
  let F : ℝ → ℝ := fun t => S.alpha u t / S.lam u t
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc u 1) K := by
    intro t ht
    exact ⟨hu.1.le, ht.1, ht.2⟩
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => (u, t)) (Icc u 1) := by
    fun_prop
  have hphi : ContDiffOn ℝ 1 (S.phi u) (Icc u 1) :=
    ((C1Solution.five_fields_contDiffOn (by norm_num) hb H).2.2.1).comp
      hpair hmap
  have hF : ContDiffOn ℝ 1 F (Icc u 1) :=
    (C1Solution.alpha_div_lam_contDiffOn (by norm_num) hb H).comp
      hpair hmap
  have hphiAC : AbsolutelyContinuousOnInterval (S.phi u) u 1 :=
    (show ContDiffOn ℝ 1 (S.phi u) (uIcc u 1) by
      simpa only [uIcc_of_le hu.2.le] using hphi).absolutelyContinuousOnInterval
  have hFAC : AbsolutelyContinuousOnInterval F u 1 :=
    (show ContDiffOn ℝ 1 F (uIcc u 1) by
      simpa only [uIcc_of_le hu.2.le] using hF).absolutelyContinuousOnInterval
  have hlin := null_lintegral_eq_scalar_variation hu.2.le hphiAC
    (fun t ht => outgoing_theta_over_r_eq_abs_phi_deriv hb hu ht H)
  have hreal := outgoing_scalar_integral_bound hb hu H
  calc
    (∫⁻ t in Ioo u 1, ENNReal.ofReal (|S.theta u t| / S.r u t)) =
        eVariationOn (S.phi u) (Ioo u 1) := hlin
    _ = ENNReal.ofReal (∫ t in u..1, |deriv (S.phi u) t|) :=
      AbsolutelyContinuousOnInterval.eVariationOn_Ioo_eq_integral_abs_deriv
        hu.2.le hphiAC
    _ ≤ ENNReal.ofReal (∫ t in u..1, |deriv F t|) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = eVariationOn F (Ioo u 1) :=
      (AbsolutelyContinuousOnInterval.eVariationOn_Ioo_eq_integral_abs_deriv
        hu.2.le hFAC).symm

end ChristodoulouBV

end
