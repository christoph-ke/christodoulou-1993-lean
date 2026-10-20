module

public import ChristodoulouBV.AreaEstimates.BasicEstimatesVariationCore
public import ChristodoulouBV.AreaEstimates.GaugeAxis
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Incoming variation bound of Lemma 4.1

The incoming numerator is formed from the canonical radius and scalar
radius, with the terminal axis approached from the left.
-/

public section

open Set MeasureTheory Filter
open scoped Topology Interval

namespace ChristodoulouBV

/-- The incoming weighted numerator, expressed using canonical primitives
so that it is defined at the regular axis. -/
noncomputable def sourceJ (S : Fields) (u v : ℝ) : ℝ :=
  C1Solution.canonicalRadius S (u, v) * (S.beta u v / S.nu u v) -
    C1Solution.canonicalScalarRadius S (u, v)

private theorem deriv_horizontal_slice {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 1))
    {t v : ℝ} (ht : 0 < t) (htv : t < v) (hv : v < 1) :
    deriv (fun s => F (s, v)) t =
      (fderivWithin ℝ F (closedCoordTriangle 0 1) (t, v)) (1, 0) := by
  let K := closedCoordTriangle 0 1
  have hp : (t, v) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact ⟨ht, htv, hv⟩
  have hpK : (t, v) ∈ K := interior_subset hp
  have hdiff : DifferentiableAt ℝ F (t, v) :=
    ((hF.differentiableOn (by norm_num)).mono interior_subset (t, v) hp)
      |>.differentiableAt (isOpen_interior.mem_nhds hp)
  have hpair : HasDerivAt (fun s : ℝ => (s, v)) (1, 0) t :=
    (hasDerivAt_id' t).prodMk (hasDerivAt_const t v)
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt t hpair
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 1)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty (by norm_num))
  rw [fderivWithin_eq_fderiv (hunique (t, v) hpK) hdiff]
  simpa only [Function.comp_def] using hcomp.deriv

/-- The incoming weighted numerator inequality on a compact slice ending
strictly before the regular axis. -/
theorem incoming_weighted_numerator_interval {b v c : ℝ}
    (hb : 1 < b) (hv : v ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo 0 v)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    let F : ℝ → ℝ := fun t => S.beta t v / S.nu t v
    let I : ℝ → ℝ := fun t =>
      C1Solution.canonicalRadius S (t, v) * F t -
        C1Solution.canonicalScalarRadius S (t, v)
    (∫ t in 0..c,
      |I t| * (-S.nu t v) / (C1Solution.canonicalRadius S (t, v)) ^ 2) ≤
      |I c| / C1Solution.canonicalRadius S (c, v) +
        ∫ t in 0..c, |deriv F t| := by
  dsimp only
  let K := closedCoordTriangle 0 1
  let R : ℝ × ℝ → ℝ := C1Solution.canonicalRadius S
  let N : ℝ × ℝ → ℝ := C1Solution.canonicalScalarRadius S
  let F : ℝ → ℝ := fun t => S.beta t v / S.nu t v
  let I : ℝ → ℝ := fun t => R (t, v) * F t - N (t, v)
  have hR : ContDiffOn ℝ 1 R K :=
    C1Solution.canonicalRadius_contDiffOn (by norm_num) hb H
  have hN : ContDiffOn ℝ 1 N K :=
    C1Solution.canonicalScalarRadius_contDiffOn (by norm_num) hb H
  have hβ : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.beta p.1 p.2) K :=
    C1Solution.beta_contDiffOn (by norm_num) hb H
  have hν : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.nu p.1 p.2) K :=
    (C1Solution.five_fields_contDiffOn (by norm_num) hb H).2.1
  have hmap : MapsTo (fun t : ℝ => (t, v)) (Icc 0 c) K := by
    intro t ht
    exact ⟨ht.1, (ht.2.trans_lt hc.2).le, hv.2.le⟩
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => (t, v)) (Icc 0 c) := by
    fun_prop
  have hRs : ContDiffOn ℝ 1 (fun t => R (t, v)) (Icc 0 c) :=
    hR.comp hpair hmap
  have hNs : ContDiffOn ℝ 1 (fun t => N (t, v)) (Icc 0 c) :=
    hN.comp hpair hmap
  have hβs : ContDiffOn ℝ 1 (fun t => S.beta t v) (Icc 0 c) :=
    hβ.comp hpair hmap
  have hνs : ContDiffOn ℝ 1 (fun t => S.nu t v) (Icc 0 c) :=
    hν.comp hpair hmap
  have hνneg : ∀ t ∈ Icc 0 c, S.nu t v < 0 := by
    intro t ht
    exact C1Solution.nu_neg (by norm_num) hb H ht.1
      (ht.2.trans_lt hc.2) hv.2.le
  have hFs : ContDiffOn ℝ 1 F (Icc 0 c) :=
    hβs.div hνs (fun t ht => (hνneg t ht).ne)
  have hIs : ContDiffOn ℝ 1 I (Icc 0 c) :=
    (hRs.mul hFs).sub hNs
  have hRpos : ∀ t ∈ Icc 0 c, 0 < R (t, v) := by
    intro t ht
    change 0 < C1Solution.canonicalRadius S (t, v)
    rw [C1Solution.canonicalRadius_eq_radius (by norm_num) hb H
      ht.1 (ht.2.trans_lt hc.2) hv.2.le]
    exact H.solution.radius_pos (t, v)
      ⟨ht.1, ht.2.trans_lt hc.2, hv.2.trans hb⟩
  have hIderiv : ∀ t ∈ Ioo 0 c,
      deriv I t = R (t, v) * deriv F t := by
    intro t ht
    have htv : t < v := ht.2.trans hc.2
    have hpK : (t, v) ∈ K := ⟨ht.1.le, htv.le, hv.2.le⟩
    have hνne : S.nu t v ≠ 0 := (hνneg t ⟨ht.1.le, ht.2.le⟩).ne
    have hRd := deriv_horizontal_slice hR ht.1 htv hv.2
    have hNd := deriv_horizontal_slice hN ht.1 htv hv.2
    rw [C1Solution.canonicalRadius_horizontal_jet
      (by norm_num) hb H hpK] at hRd
    rw [C1Solution.canonicalScalarRadius_horizontal_jet
      (by norm_num) hb H hpK] at hNd
    have hRdiff : DifferentiableAt ℝ (fun s => R (s, v)) t :=
      (hRs.differentiableOn (by norm_num) t
        ⟨ht.1.le, ht.2.le⟩).differentiableAt
        (Icc_mem_nhds ht.1 ht.2)
    have hFdiff : DifferentiableAt ℝ F t :=
      (hFs.differentiableOn (by norm_num) t
        ⟨ht.1.le, ht.2.le⟩).differentiableAt
        (Icc_mem_nhds ht.1 ht.2)
    have hNdiff : DifferentiableAt ℝ (fun s => N (s, v)) t :=
      (hNs.differentiableOn (by norm_num) t
        ⟨ht.1.le, ht.2.le⟩).differentiableAt
        (Icc_mem_nhds ht.1 ht.2)
    change deriv (fun s => R (s, v) * F s - N (s, v)) t = _
    have hprodDeriv := deriv_mul hRdiff hFdiff
    change deriv (fun s => R (s, v) * F s) t =
      deriv (fun s => R (s, v)) t * F t + R (t, v) * deriv F t at hprodDeriv
    have hsubDeriv := deriv_sub (hRdiff.mul hFdiff) hNdiff
    change deriv (fun s => R (s, v) * F s - N (s, v)) t =
      deriv (fun s => R (s, v) * F s) t - deriv (fun s => N (s, v)) t at hsubDeriv
    rw [hsubDeriv, hprodDeriv, hRd, hNd]
    dsimp [F]
    field_simp [hνne]
    ring
  have hcore := weighted_numerator_finite_interval_bound_incoming hc.1.le
    hIs hRs hFs hRpos hIderiv
  have hRderiv : ∀ t ∈ Ioo 0 c,
      deriv (fun s => R (s, v)) t = S.nu t v := by
    intro t ht
    have hpK : (t, v) ∈ K :=
      ⟨ht.1.le, (ht.2.trans hc.2).le, hv.2.le⟩
    exact (deriv_horizontal_slice hR ht.1 (ht.2.trans hc.2) hv.2).trans
      (C1Solution.canonicalRadius_horizontal_jet (by norm_num) hb H hpK)
  have hleft : (∫ t in 0..c,
      |I t| * (-deriv (fun s => R (s, v)) t) / (R (t, v)) ^ 2) =
      ∫ t in 0..c, |I t| * (-S.nu t v) / (R (t, v)) ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume c] with t hne ht
    rw [uIoc_of_le hc.1.le] at ht
    exact congrArg (fun x => |I t| * (-x) / (R (t, v)) ^ 2)
      (hRderiv t ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩)
  rw [hleft] at hcore
  exact hcore

/-- The incoming finite-slice inequality in the paper's `|ζ|/r` form. -/
theorem incoming_scalar_interval_bound {b v c : ℝ}
    (hb : 1 < b) (hv : v ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo 0 v)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    let F : ℝ → ℝ := fun t => S.beta t v / S.nu t v
    let I : ℝ → ℝ := fun t =>
      C1Solution.canonicalRadius S (t, v) * F t -
        C1Solution.canonicalScalarRadius S (t, v)
    (∫ t in 0..c, |S.zeta t v| / S.r t v) ≤
      |I c| / S.r c v + ∫ t in 0..c, |deriv F t| := by
  dsimp only
  let R : ℝ × ℝ → ℝ := C1Solution.canonicalRadius S
  let N : ℝ × ℝ → ℝ := C1Solution.canonicalScalarRadius S
  let F : ℝ → ℝ := fun t => S.beta t v / S.nu t v
  let I : ℝ → ℝ := fun t => R (t, v) * F t - N (t, v)
  have hbase := incoming_weighted_numerator_interval hb hv hc H
  change (∫ t in 0..c, |I t| * (-S.nu t v) / (R (t, v)) ^ 2) ≤
      |I c| / R (c, v) + ∫ t in 0..c, |deriv F t| at hbase
  have hpoint (t : ℝ) (ht : t ∈ Ico 0 c) :
      |S.zeta t v| / S.r t v =
        |I t| * (-S.nu t v) / (R (t, v)) ^ 2 := by
    have htv : t < v := ht.2.trans hc.2
    have hr := C1Solution.canonicalRadius_eq_radius (by norm_num) hb H
      ht.1 htv hv.2.le
    have hn := C1Solution.canonicalScalarRadius_eq_radius_mul_phi
      (by norm_num) hb H ht.1 htv hv.2.le
    have hν : S.nu t v < 0 :=
      C1Solution.nu_neg (by norm_num) hb H ht.1 htv hv.2.le
    have hrpos : 0 < S.r t v :=
      H.solution.radius_pos (t, v) ⟨ht.1, htv, hv.2.trans hb⟩
    change R (t, v) = S.r t v at hr
    change N (t, v) = S.r t v * S.phi t v at hn
    dsimp [I, F]
    rw [hr, hn]
    unfold Fields.zeta
    have hfact : S.beta t v - S.nu t v * S.phi t v =
        S.nu t v * (S.beta t v / S.nu t v - S.phi t v) := by
      field_simp [hν.ne]
    rw [hfact, abs_mul, abs_of_neg hν, ← mul_sub, abs_mul,
      abs_of_pos hrpos]
    field_simp [hrpos.ne']
  have hleft : (∫ t in 0..c, |S.zeta t v| / S.r t v) =
      ∫ t in 0..c, |I t| * (-S.nu t v) / (R (t, v)) ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume c] with t hne ht
    rw [uIoc_of_le hc.1.le] at ht
    exact hpoint t ⟨ht.1.le, lt_of_le_of_ne ht.2 hne⟩
  have hRc : R (c, v) = S.r c v :=
    C1Solution.canonicalRadius_eq_radius (by norm_num) hb H
      hc.1.le hc.2 hv.2.le
  rw [hRc] at hbase
  rw [hleft]
  simpa only [F] using hbase

/-- The incoming boundary contribution `J/r` vanishes at the regular axis. -/
theorem sourceJ_axis {b v : ℝ} (hb : 1 < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun u => sourceJ S u v / S.r u v)
      (𝓝[<] v) (𝓝 (0 : ℝ)) := by
  let K := closedCoordTriangle 0 1
  let F : ℝ × ℝ → ℝ := fun p =>
    S.beta p.1 p.2 / S.nu p.1 p.2 - S.phi p.1 p.2
  have hνaxis : S.nu v v < 0 := by
    have hν := C1Solution.nu_eq_neg_lam_axis (by norm_num) hb H
      (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2.le⟩)
    obtain ⟨c, hc, hcl⟩ :=
      C1Solution.exists_lam_lower_bound (by norm_num) hb H
    have hlam : 0 < S.lam v v :=
      hc.trans_le (hcl (v, v) ⟨hv.1.le, le_rfl, hv.2.le⟩)
    linarith only [hν, hlam]
  have hνneg : ∀ p ∈ K, S.nu p.1 p.2 < 0 := by
    rintro ⟨u, w⟩ hp
    rcases eq_or_lt_of_le hp.2.1 with heq | hlt
    · change u = w at heq
      subst w
      have hν := C1Solution.nu_eq_neg_lam_axis (by norm_num) hb H
        (show u ∈ Icc (0 : ℝ) 1 from ⟨hp.1, hp.2.2⟩)
      obtain ⟨c, hc, hcl⟩ :=
        C1Solution.exists_lam_lower_bound (by norm_num) hb H
      have hlam : 0 < S.lam u u :=
        hc.trans_le (hcl (u, u) ⟨hp.1, le_rfl, hp.2.2⟩)
      linarith only [hν, hlam]
    · exact C1Solution.nu_neg (by norm_num) hb H hp.1 hlt hp.2.2
  have hF : ContinuousOn F K := by
    have hβ := (C1Solution.beta_contDiffOn (by norm_num) hb H).continuousOn
    have hν := ((C1Solution.five_fields_contDiffOn (by norm_num) hb H).2.1).continuousOn
    have hφ := ((C1Solution.five_fields_contDiffOn (by norm_num) hb H).2.2.1).continuousOn
    exact (hβ.div hν (fun p hp => (hνneg p hp).ne)).sub hφ
  have hslice : ContinuousOn (fun u => F (u, v)) (Icc 0 v) :=
    hF.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => ⟨hu.1, hu.2, hv.2.le⟩)
  have hFzero : F (v, v) = 0 := by
    dsimp [F]
    rw [C1Solution.beta_eq_nu_mul_phi_axis (by norm_num) hb H
      (show v ∈ Icc (0 : ℝ) 1 from ⟨hv.1.le, hv.2.le⟩)]
    field_simp [hνaxis.ne]
    ring
  have hleft : ContinuousWithinAt (fun u => F (u, v)) (Iic v) v :=
    (continuousWithinAt_Icc_iff_Iic hv.1).mp
      (hslice.continuousWithinAt ⟨hv.1.le, le_rfl⟩)
  have hlim : Tendsto (fun u => F (u, v)) (𝓝[<] v) (𝓝 (0 : ℝ)) := by
    simpa only [hFzero] using (hleft.mono Iio_subset_Iic_self).tendsto
  have heq : (fun u => sourceJ S u v / S.r u v) =ᶠ[𝓝[<] v]
      (fun u => F (u, v)) := by
    filter_upwards [Ioo_mem_nhdsLT hv.1] with u hu
    have hr := C1Solution.canonicalRadius_eq_radius (by norm_num) hb H
      hu.1.le hu.2 hv.2.le
    have hn := C1Solution.canonicalScalarRadius_eq_radius_mul_phi
      (by norm_num) hb H hu.1.le hu.2 hv.2.le
    have hrpos : S.r u v ≠ 0 := ne_of_gt
      (H.solution.radius_pos (u, v) ⟨hu.1.le, hu.2, hv.2.trans hb⟩)
    dsimp [F, sourceJ]
    rw [hr, hn]
    field_simp [hrpos]
  exact hlim.congr' heq.symm

/-- The incoming scalar derivative is the source integrand on the open
development. -/
theorem incoming_zeta_over_r_eq_abs_phi_deriv {b t v : ℝ}
    (hb : 1 < b) (hv : v ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Ioo 0 v)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    |S.zeta t v| / S.r t v = |deriv (fun s => S.phi s v) t| := by
  let K := closedCoordTriangle 0 1
  have hphi : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => S.phi p.1 p.2) K :=
    (C1Solution.five_fields_contDiffOn (by norm_num) hb H).2.2.1
  have hpK : (t, v) ∈ K := ⟨ht.1.le, ht.2.le, hv.2.le⟩
  have hderiv := deriv_horizontal_slice hphi ht.1 ht.2 hv.2
  have hzeta := C1Solution.zeta_eq_canonicalRadius_mul_phi_horizontal_jet
    (by norm_num) hb H hpK
  have hr := C1Solution.canonicalRadius_eq_radius (by norm_num) hb H
    ht.1.le ht.2 hv.2.le
  have hrpos : 0 < S.r t v :=
    H.solution.radius_pos (t, v) ⟨ht.1.le, ht.2, hv.2.trans hb⟩
  rw [hr, ← hderiv] at hzeta
  rw [hzeta, abs_mul, abs_of_pos hrpos]
  field_simp [hrpos.ne']

/-- The incoming integral estimate after the regular-axis boundary term
has vanished. -/
theorem incoming_scalar_integral_bound {b v : ℝ}
    (hb : 1 < b) (hv : v ∈ Ioo (0 : ℝ) 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    (∫ t in 0..v, |deriv (fun s => S.phi s v) t|) ≤
      ∫ t in 0..v, |deriv (fun s => S.beta s v / S.nu s v) t| := by
  let K := closedCoordTriangle 0 1
  let F : ℝ → ℝ := fun t => S.beta t v / S.nu t v
  have hmap : MapsTo (fun t : ℝ => (t, v)) (Icc 0 v) K := by
    intro t ht
    exact ⟨ht.1, ht.2, hv.2.le⟩
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => (t, v)) (Icc 0 v) := by
    fun_prop
  have hphi : ContDiffOn ℝ 1 (fun t => S.phi t v) (Icc 0 v) :=
    ((C1Solution.five_fields_contDiffOn (by norm_num) hb H).2.2.1).comp
      hpair hmap
  have hβ : ContDiffOn ℝ 1 (fun t => S.beta t v) (Icc 0 v) :=
    (C1Solution.beta_contDiffOn (by norm_num) hb H).comp hpair hmap
  have hν : ContDiffOn ℝ 1 (fun t => S.nu t v) (Icc 0 v) :=
    ((C1Solution.five_fields_contDiffOn (by norm_num) hb H).2.1).comp
      hpair hmap
  have hνneg : ∀ t ∈ Icc 0 v, S.nu t v < 0 := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with heq | hlt
    · subst v
      have hνaxis := C1Solution.nu_eq_neg_lam_axis (by norm_num) hb H
        (show t ∈ Icc (0 : ℝ) 1 from ⟨ht.1, hv.2.le⟩)
      obtain ⟨c, hc, hcl⟩ :=
        C1Solution.exists_lam_lower_bound (by norm_num) hb H
      have hlam : 0 < S.lam t t :=
        hc.trans_le (hcl (t, t) ⟨ht.1, le_rfl, hv.2.le⟩)
      linarith only [hνaxis, hlam]
    · exact C1Solution.nu_neg (by norm_num) hb H ht.1 hlt hv.2.le
  have hF : ContDiffOn ℝ 1 F (Icc 0 v) :=
    hβ.div hν (fun t ht => (hνneg t ht).ne)
  have hphiAC : AbsolutelyContinuousOnInterval (fun t => S.phi t v) 0 v :=
    (show ContDiffOn ℝ 1 (fun t => S.phi t v) (uIcc 0 v) by
      simpa only [uIcc_of_le hv.1.le] using hphi).absolutelyContinuousOnInterval
  have hFAC : AbsolutelyContinuousOnInterval F 0 v :=
    (show ContDiffOn ℝ 1 F (uIcc 0 v) by
      simpa only [uIcc_of_le hv.1.le] using hF).absolutelyContinuousOnInterval
  have hq := sourceJ_axis hb H hv
  apply interval_bound_of_vanishing_right_boundary hv.1
    hphiAC.intervalIntegrable_deriv.abs hFAC.intervalIntegrable_deriv.abs hq
  intro c hc
  have hfinite := incoming_scalar_interval_bound hb hv hc H
  have hleft : (∫ t in 0..c, |deriv (fun s => S.phi s v) t|) =
      ∫ t in 0..c, |S.zeta t v| / S.r t v := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume c] with t hne ht
    rw [uIoc_of_le hc.1.le] at ht
    symm
    exact incoming_zeta_over_r_eq_abs_phi_deriv hb hv
      ⟨ht.1, lt_of_le_of_ne ht.2 hne |>.trans hc.2⟩ H
  rw [hleft]
  have hrpos : 0 < S.r c v :=
    H.solution.radius_pos (c, v) ⟨hc.1.le, hc.2, hv.2.trans hb⟩
  rw [abs_div, abs_of_pos hrpos]
  simpa only [F, sourceJ] using hfinite

/-- The incoming half of Lemma 4.1, with the source's extended integral
and total variation on the open characteristic. -/
theorem incoming_scalar_variation_bound {b v : ℝ}
    (hb : 1 < b) (hv : v ∈ Ioo (0 : ℝ) 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    (∫⁻ t in Ioo 0 v, ENNReal.ofReal (|S.zeta t v| / S.r t v)) ≤
      eVariationOn (fun t => S.beta t v / S.nu t v) (Ioo 0 v) := by
  let K := closedCoordTriangle 0 1
  let F : ℝ → ℝ := fun t => S.beta t v / S.nu t v
  have hmap : MapsTo (fun t : ℝ => (t, v)) (Icc 0 v) K := by
    intro t ht
    exact ⟨ht.1, ht.2, hv.2.le⟩
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => (t, v)) (Icc 0 v) := by
    fun_prop
  have hphi : ContDiffOn ℝ 1 (fun t => S.phi t v) (Icc 0 v) :=
    ((C1Solution.five_fields_contDiffOn (by norm_num) hb H).2.2.1).comp
      hpair hmap
  have hβ : ContDiffOn ℝ 1 (fun t => S.beta t v) (Icc 0 v) :=
    (C1Solution.beta_contDiffOn (by norm_num) hb H).comp hpair hmap
  have hν : ContDiffOn ℝ 1 (fun t => S.nu t v) (Icc 0 v) :=
    ((C1Solution.five_fields_contDiffOn (by norm_num) hb H).2.1).comp
      hpair hmap
  have hνneg : ∀ t ∈ Icc 0 v, S.nu t v < 0 := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with heq | hlt
    · subst v
      have hνaxis := C1Solution.nu_eq_neg_lam_axis (by norm_num) hb H
        (show t ∈ Icc (0 : ℝ) 1 from ⟨ht.1, hv.2.le⟩)
      obtain ⟨c, hc, hcl⟩ :=
        C1Solution.exists_lam_lower_bound (by norm_num) hb H
      have hlam : 0 < S.lam t t :=
        hc.trans_le (hcl (t, t) ⟨ht.1, le_rfl, hv.2.le⟩)
      linarith only [hνaxis, hlam]
    · exact C1Solution.nu_neg (by norm_num) hb H ht.1 hlt hv.2.le
  have hF : ContDiffOn ℝ 1 F (Icc 0 v) :=
    hβ.div hν (fun t ht => (hνneg t ht).ne)
  have hphiAC : AbsolutelyContinuousOnInterval (fun t => S.phi t v) 0 v :=
    (show ContDiffOn ℝ 1 (fun t => S.phi t v) (uIcc 0 v) by
      simpa only [uIcc_of_le hv.1.le] using hphi).absolutelyContinuousOnInterval
  have hFAC : AbsolutelyContinuousOnInterval F 0 v :=
    (show ContDiffOn ℝ 1 F (uIcc 0 v) by
      simpa only [uIcc_of_le hv.1.le] using hF).absolutelyContinuousOnInterval
  have hlin := null_lintegral_eq_scalar_variation hv.1.le hphiAC
    (fun t ht => incoming_zeta_over_r_eq_abs_phi_deriv hb hv ht H)
  have hreal := incoming_scalar_integral_bound hb hv H
  calc
    (∫⁻ t in Ioo 0 v, ENNReal.ofReal (|S.zeta t v| / S.r t v)) =
        eVariationOn (fun t => S.phi t v) (Ioo 0 v) := hlin
    _ = ENNReal.ofReal (∫ t in 0..v,
          |deriv (fun s => S.phi s v) t|) :=
      AbsolutelyContinuousOnInterval.eVariationOn_Ioo_eq_integral_abs_deriv
        hv.1.le hphiAC
    _ ≤ ENNReal.ofReal (∫ t in 0..v, |deriv F t|) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = eVariationOn F (Ioo 0 v) :=
      (AbsolutelyContinuousOnInterval.eVariationOn_Ioo_eq_integral_abs_deriv
        hv.1.le hFAC).symm

end ChristodoulouBV

end
