module

public import ChristodoulouBV.AreaEstimates.LogTransportCore
import Mathlib.Tactic
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Initial-edge logarithmic residual

The initial scalar Hardy estimate is combined with the quadratic correction
and the mass-ratio estimate on the normalized initial edge.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV

/-- The correction `f` is continuous on the open initial edge. -/
private theorem initial_log_correction_continuousOn {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2) :
    ContinuousOn (sourceLogCorrection S 0) (Ioo (0 : ℝ) 1) := by
  let I := Ioo (0 : ℝ) 1
  have hK := C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
    (by norm_num : (0 : ℝ) < 1)
  have hmap : MapsTo (fun v : ℝ => ((0 : ℝ), v)) I
      (closedCoordTriangle 0 1) := by
    intro v hv
    exact ⟨le_rfl, hv.1.le, hv.2.le⟩
  have hpair : ContinuousOn (fun v : ℝ => ((0 : ℝ), v)) I := by
    fun_prop
  have htheta : ContinuousOn (S.theta 0) I :=
    (hK ▸ H.theta_c1).continuousOn.comp hpair hmap
  have hzeta : ContinuousOn (S.zeta 0) I :=
    (hK ▸ H.zeta_c1).continuousOn.comp hpair hmap
  have hlam : ContinuousOn (S.lam 0) I :=
    (hK ▸ H.lam_c1).continuousOn.comp hpair hmap
  have hnu : ContinuousOn (S.nu 0) I :=
    (hK ▸ H.nu_c1).continuousOn.comp hpair hmap
  have hradius : ContinuousOn (fun v : ℝ => v / 2) I := by fun_prop
  have hrne : ∀ v ∈ I, v / 2 ≠ 0 := by
    intro v hv
    exact ne_of_gt (half_pos hv.1)
  have hlamne : ∀ v ∈ I, S.lam 0 v ≠ 0 := by
    intro v hv
    exact ne_of_gt (H.solution.lam_pos (0, v) ⟨le_rfl, hv.1, hv.2⟩)
  have hnune : ∀ v ∈ I, S.nu 0 v ≠ 0 := by
    intro v hv
    let B : ℝ := (v + 1) / 2
    have hB : 0 < B := by dsimp [B]; linarith only [hv.1]
    have hvB : v < B := by dsimp [B]; linarith only [hv.2]
    have hB1 : B < 1 := by dsimp [B]; linarith only [hv.2]
    have hp : ((0 : ℝ), v) ∈ closedCoordTriangle 0 B :=
      ⟨le_rfl, hv.1.le, hvB.le⟩
    exact ne_of_lt (C1Solution.nu_neg_closed_triangle hB hB1 H hp)
  have hcont : ContinuousOn (fun v => S.theta 0 v / (v / 2) *
      (S.theta 0 v / S.lam 0 v - S.zeta 0 v / S.nu 0 v)) I :=
    (htheta.div hradius hrne).mul
      ((htheta.div hlam hlamne).sub (hzeta.div hnu hnune))
  apply hcont.congr
  intro v hv
  simp only [sourceLogCorrection, hr v hv]

private theorem initial_log_correction_integrable_and_bound {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    IntervalIntegrable (fun v => |sourceLogCorrection S 0 v|) volume 0 1 ∧
    (∫ v in (0 : ℝ)..1, |sourceLogCorrection S 0 v|) ≤
      78 * (sourceD S).toReal ^ 2 := by
  let D := (sourceD S).toReal
  let F : ℝ → ℝ := fun v => |sourceLogCorrection S 0 v|
  let G : ℝ → ℝ := fun v => 39 * D * (|S.theta 0 v| / S.r 0 v)
  have hnull := initial_theta_over_r_integrable H
  have hGI : IntervalIntegrable G volume 0 1 := hnull.const_mul (39 * D)
  have hFcont : ContinuousOn F (Ioo (0 : ℝ) 1) :=
    (initial_log_correction_continuousOn H hr).abs
  have hFmeas : AEStronglyMeasurable F
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact hFcont.aestronglyMeasurable measurableSet_Ioo
  have hpoint (v : ℝ) (hv : v ∈ Ioo (0 : ℝ) 1) : F v ≤ G v := by
    have hp : ((0 : ℝ), v) ∈ developmentWithInitialEdge 1 :=
      ⟨le_rfl, hv.1, hv.2⟩
    exact source_log_correction_bound H hr hcenter hboot hp
  have hnorm : (fun v => ‖F v‖) ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] G := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro v hv
    change ‖F v‖ ≤ G v
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact hpoint v hv
  have hFI : IntervalIntegrable F volume 0 1 :=
    hGI.mono_fun'
      (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hFmeas)
      (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hnorm)
  have hmono : (∫ v in (0 : ℝ)..1, F v) ≤ ∫ v in (0 : ℝ)..1, G v := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num : (0 : ℝ) ≤ 1) hFI hGI
    exact hpoint
  have hD : 0 ≤ D := ENNReal.toReal_nonneg
  refine ⟨hFI, ?_⟩
  calc
    (∫ v in (0 : ℝ)..1, F v) ≤ ∫ v in (0 : ℝ)..1, G v := hmono
    _ = 39 * D * (∫ v in (0 : ℝ)..1, |S.theta 0 v| / S.r 0 v) := by
      dsimp [G]
      rw [← intervalIntegral.integral_const_mul]
    _ ≤ 39 * D * (2 * D) := by
      exact mul_le_mul_of_nonneg_left (initial_theta_integral_le_sourceD H hr)
        (by positivity)
    _ = 78 * D ^ 2 := by ring

/-- The quadratic correction is integrable on the initial edge. -/
theorem initial_log_correction_integrable {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    IntervalIntegrable (fun v => |sourceLogCorrection S 0 v|) volume 0 1 :=
  (initial_log_correction_integrable_and_bound H hr hcenter hboot).1

/-- The initial quadratic correction has integral at most `78D²`. -/
theorem initial_log_correction_integral_le_sourceD {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    (∫ v in (0 : ℝ)..1, |sourceLogCorrection S 0 v|) ≤
      78 * (sourceD S).toReal ^ 2 :=
  (initial_log_correction_integrable_and_bound H hr hcenter hboot).2

private theorem initial_mass_ratio_integrable_and_bound {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    IntervalIntegrable (fun t =>
      (2 * S.m 0 t / S.r 0 t) * S.lam 0 t /
        ((1 - 2 * S.m 0 t / S.r 0 t) * S.r 0 t)) volume 0 1 ∧
    (∫ t in (0 : ℝ)..1,
      (2 * S.m 0 t / S.r 0 t) * S.lam 0 t /
        ((1 - 2 * S.m 0 t / S.r 0 t) * S.r 0 t)) ≤
      30 * (sourceD S).toReal ^ 2 := by
  let D := (sourceD S).toReal
  let F : ℝ → ℝ := IsBVSolution.nuCoeff S 0
  let G : ℝ → ℝ := fun t =>
    (2 * S.m 0 t / S.r 0 t) * S.lam 0 t /
      ((1 - 2 * S.m 0 t / S.r 0 t) * S.r 0 t)
  let b : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2)
  have hbmem (n : ℕ) : b n ∈ Ioo (0 : ℝ) 1 := by
    dsimp [b]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    constructor
    · have h : 1 / ((n : ℝ) + 2) < 1 := (div_lt_iff₀ (by positivity)).2 (by linarith)
      linarith
    · have h : 0 < 1 / ((n : ℝ) + 2) := by positivity
      linarith
  have hb : Tendsto b atTop (𝓝 (1 : ℝ)) := by
    have hz : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2))
        atTop (𝓝 (0 : ℝ)) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 1)
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc,
        one_add_one_eq_two] using h
    simpa only [b, sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub hz
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hM : ∀ p ∈ developmentWithInitialEdge 1,
      |S.theta p.1 p.2 / S.lam p.1 p.2| ≤ 15 * D := by
    intro p hp
    exact source_theta_div_lam_le_sourceD H hr hcenter hboot hp
  have hfi (n : ℕ) : IntegrableOn F (Ioc 0 (b n)) := by
    have hp : ((0 : ℝ), b n) ∈ developmentWithInitialEdge 1 :=
      ⟨le_rfl, (hbmem n).1, (hbmem n).2⟩
    exact hBV.nu_coeff_integrable_axis hp (fun t ht =>
      hM (0, t) (hBV.solution.development.outgoing_mem hp ht.1 ht.2))
  have hbound (n : ℕ) :
      (∫ t in Ioc (0 : ℝ) (b n), ‖F t‖) ≤ 30 * D ^ 2 := by
    have hp : ((0 : ℝ), b n) ∈ developmentWithInitialEdge 1 :=
      ⟨le_rfl, (hbmem n).1, (hbmem n).2⟩
    have hnorm : (∫ t in Ioc (0 : ℝ) (b n), ‖F t‖) =
        ∫ t in (0 : ℝ)..b n, F t := by
      rw [intervalIntegral.integral_of_le (hbmem n).1.le]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      change ‖F t‖ = F t
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact IsBVSolution.nu_coeff_nonneg hBV.solution.development hBV
        (hBV.solution.development.outgoing_mem hp ht.1 ht.2)
    have heq : (∫ t in (0 : ℝ)..b n, F t) =
        ∫ t in (0 : ℝ)..b n,
          (2 * S.m 0 t / S.r 0 t) * S.lam 0 t /
            ((1 - 2 * S.m 0 t / S.r 0 t) * S.r 0 t) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (hbmem n).1.le
      intro t ht
      exact hBV.nuCoeff_eq_mass_ratio_coefficient_out
        (hBV.solution.development.outgoing_mem hp ht.1 ht.2.le)
    rw [hnorm, heq]
    exact initial_mass_ratio_cutoff_le_sourceD H hr hcenter hboot (hbmem n)
  have hfull : IntegrableOn F (Ioc (0 : ℝ) 1) :=
    integrableOn_Ioc_of_intervalIntegral_norm_bounded_right hfi hb
      (Filter.Eventually.of_forall hbound)
  have hEq : F =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] G := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    have hp : ((0 : ℝ), t) ∈ developmentWithInitialEdge 1 :=
      ⟨le_rfl, ht.1, ht.2⟩
    exact hBV.nuCoeff_eq_mass_ratio_coefficient_out hp
  have hGInt : IntervalIntegrable G volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).2 (hfull.congr_fun_ae hEq)
  have hcover : AECover (volume.restrict (Ioc (0 : ℝ) 1)) atTop
      (fun n : ℕ => Ioc (0 : ℝ) (b n)) := by
    exact aecover_Ioc_of_Ioc tendsto_const_nhds hb
  have hlim : Tendsto
      (fun n : ℕ => ∫ t in Ioc (0 : ℝ) (b n), F t)
      atTop (𝓝 (∫ t in Ioc (0 : ℝ) 1, F t)) := by
    convert hcover.integral_tendsto_of_countably_generated hfull using 1
    · ext n
      rw [Measure.restrict_restrict measurableSet_Ioc]
      have hs : Ioc (0 : ℝ) (b n) ∩ Ioc 0 1 = Ioc 0 (b n) :=
        inter_eq_left.mpr (Ioc_subset_Ioc le_rfl (hbmem n).2.le)
      rw [hs]
  have hle : (∫ t in Ioc (0 : ℝ) 1, F t) ≤ 30 * D ^ 2 := by
    apply le_of_tendsto hlim
    filter_upwards with n
    have heq : (∫ t in Ioc (0 : ℝ) (b n), F t) =
        ∫ t in (0 : ℝ)..b n,
          (2 * S.m 0 t / S.r 0 t) * S.lam 0 t /
            ((1 - 2 * S.m 0 t / S.r 0 t) * S.r 0 t) := by
      rw [intervalIntegral.integral_of_le (hbmem n).1.le]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      have hp : ((0 : ℝ), t) ∈ developmentWithInitialEdge 1 :=
        ⟨le_rfl, ht.1, ht.2.trans_lt (hbmem n).2⟩
      exact hBV.nuCoeff_eq_mass_ratio_coefficient_out hp
    rw [heq]
    exact initial_mass_ratio_cutoff_le_sourceD H hr hcenter hboot (hbmem n)
  refine ⟨hGInt, ?_⟩
  change (∫ t in (0 : ℝ)..1, G t) ≤ 30 * D ^ 2
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  calc
    (∫ t in Ioc (0 : ℝ) 1, G t) = ∫ t in Ioc (0 : ℝ) 1, F t :=
      integral_congr_ae hEq.symm
    _ ≤ 30 * D ^ 2 := hle

/-- The mass-ratio term is integrable on the full initial edge. -/
theorem initial_mass_ratio_integrable {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    IntervalIntegrable (fun t =>
      (2 * S.m 0 t / S.r 0 t) * S.lam 0 t /
        ((1 - 2 * S.m 0 t / S.r 0 t) * S.r 0 t)) volume 0 1 :=
  (initial_mass_ratio_integrable_and_bound H hr hcenter hboot).1

/-- The initial-edge mass-ratio contribution is at most `30D²`. -/
theorem initial_mass_ratio_integral_le_sourceD {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    (∫ t in (0 : ℝ)..1,
      (2 * S.m 0 t / S.r 0 t) * S.lam 0 t /
        ((1 - 2 * S.m 0 t / S.r 0 t) * S.r 0 t)) ≤
      30 * (sourceD S).toReal ^ 2 :=
  (initial_mass_ratio_integrable_and_bound H hr hcenter hboot).2

private theorem initial_log_residual_integrable_and_bound {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    IntervalIntegrable (fun v => |sourceOutgoingLogResidual S 0 v|) volume 0 1 ∧
    (∫ v in (0 : ℝ)..1, |sourceOutgoingLogResidual S 0 v|) ≤
      108 * (sourceD S).toReal ^ 2 := by
  let D := (sourceD S).toReal
  let G : ℝ → ℝ := fun v =>
    (2 * S.m 0 v / S.r 0 v) * S.lam 0 v /
      ((1 - 2 * S.m 0 v / S.r 0 v) * S.r 0 v)
  let f : ℝ → ℝ := sourceLogCorrection S 0
  have hGI : IntervalIntegrable G volume 0 1 :=
    initial_mass_ratio_integrable H hr hcenter hboot
  have hfMeas : AEStronglyMeasurable f
      (volume.restrict (uIoc (0 : ℝ) 1)) := by
    simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact (initial_log_correction_continuousOn H hr).aestronglyMeasurable
      measurableSet_Ioo
  have hfI : IntervalIntegrable f volume 0 1 := by
    apply (IntervalIntegrable.intervalIntegrable_norm_iff hfMeas).1
    simpa only [Real.norm_eq_abs] using
      initial_log_correction_integrable H hr hcenter hboot
  have hExprI : IntervalIntegrable (fun v => -G v + f v) volume 0 1 :=
    hGI.neg.add hfI
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hEq (v : ℝ) (hv : v ∈ Ioo (0 : ℝ) 1) :
      sourceOutgoingLogResidual S 0 v = -G v + f v := by
    have hzero := initial_log_lam_deriv_eq_zero H hr hv
    have hp : ((0 : ℝ), v) ∈ developmentWithInitialEdge 1 :=
      ⟨le_rfl, hv.1, hv.2⟩
    have hrnz : S.r 0 v ≠ 0 := ne_of_gt (H.solution.radius_pos (0, v) hp)
    have hgapnz : 1 - 2 * S.m 0 v / S.r 0 v ≠ 0 := by
      have hg := (hBV.mass_ratio_bounds hp).2
      linarith
    dsimp [sourceOutgoingLogResidual, G, f]
    rw [hzero]
    field_simp [hrnz, hgapnz]
    <;> ring
  have hGnonneg (v : ℝ) (hv : v ∈ Ioo (0 : ℝ) 1) : 0 ≤ G v := by
    have hp : ((0 : ℝ), v) ∈ developmentWithInitialEdge 1 :=
      ⟨le_rfl, hv.1, hv.2⟩
    change 0 ≤ (2 * S.m 0 v / S.r 0 v) * S.lam 0 v /
      ((1 - 2 * S.m 0 v / S.r 0 v) * S.r 0 v)
    rw [← hBV.nuCoeff_eq_mass_ratio_coefficient_out hp]
    exact IsBVSolution.nu_coeff_nonneg hBV.solution.development hBV hp
  have hRI : IntervalIntegrable (fun v => |sourceOutgoingLogResidual S 0 v|)
      volume 0 1 := by
    apply (intervalIntegrable_congr_uIoo (a := (0 : ℝ)) (b := 1)
      (f := fun v => |sourceOutgoingLogResidual S 0 v|)
      (g := fun v => |-G v + f v|) ?_).2 hExprI.abs
    intro v hv
    have hv' : v ∈ Ioo (0 : ℝ) 1 := by
      simpa only [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hv
    change |sourceOutgoingLogResidual S 0 v| = |-G v + f v|
    rw [hEq v hv']
  have hpoint (v : ℝ) (hv : v ∈ Ioo (0 : ℝ) 1) :
      |sourceOutgoingLogResidual S 0 v| ≤ G v + |f v| := by
    rw [hEq v hv]
    calc
      |-G v + f v| ≤ |-G v| + |f v| := abs_add_le _ _
      _ = G v + |f v| := by rw [abs_neg, abs_of_nonneg (hGnonneg v hv)]
  have hmono : (∫ v in (0 : ℝ)..1, |sourceOutgoingLogResidual S 0 v|) ≤
      ∫ v in (0 : ℝ)..1, (G v + |f v|) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num : (0 : ℝ) ≤ 1) hRI
      (hGI.add (initial_log_correction_integrable H hr hcenter hboot))
    exact hpoint
  refine ⟨hRI, ?_⟩
  calc
    (∫ v in (0 : ℝ)..1, |sourceOutgoingLogResidual S 0 v|) ≤
        ∫ v in (0 : ℝ)..1, (G v + |f v|) := hmono
    _ = (∫ v in (0 : ℝ)..1, G v) +
        ∫ v in (0 : ℝ)..1, |f v| := by
      rw [intervalIntegral.integral_add hGI
        (initial_log_correction_integrable H hr hcenter hboot)]
    _ ≤ 30 * D ^ 2 + 78 * D ^ 2 := add_le_add
      (initial_mass_ratio_integral_le_sourceD H hr hcenter hboot)
      (initial_log_correction_integral_le_sourceD H hr hcenter hboot)
    _ = 108 * D ^ 2 := by ring

/-- The complete initial outgoing logarithmic residual is integrable. -/
theorem initial_log_residual_integrable {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    IntervalIntegrable (fun v => |sourceOutgoingLogResidual S 0 v|) volume 0 1 :=
  (initial_log_residual_integrable_and_bound H hr hcenter hboot).1

/-- The true initial-edge residual bound in Section 4: all three terms,
including the mass ratio and quadratic correction, are controlled by a
universal multiple of the squared initial variation. -/
theorem initial_log_residual {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    (∫ v in (0 : ℝ)..1, |sourceOutgoingLogResidual S 0 v|) ≤
      108 * (sourceD S).toReal ^ 2 :=
  (initial_log_residual_integrable_and_bound H hr hcenter hboot).2

end ChristodoulouBV

end
