module

public import ChristodoulouBV.AreaEstimates.BasicEstimates
import ChristodoulouBV.BVSolution.C1ToBV
import ChristodoulouBV.AreaEstimates.SourceInputs
import ChristodoulouBV.ForMathlib.MeasureTheory.HardyIntegral
import Mathlib.Tactic
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import all ChristodoulouBV.AreaEstimates.BasicEstimatesAmplitude

/-!
# Logarithmic transports in Section 4

The quadratic correction terms in (4.9) are given explicitly here. The
transport and residual estimates use these terms together with the reduced
mass equations.
-/

@[expose] public section

namespace ChristodoulouBV

open Set MeasureTheory
open scoped Topology

private theorem integral_mul_deriv_initial {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc 0 1))
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    v * f v - ∫ t in (0 : ℝ)..v, f t =
      ∫ t in (0 : ℝ)..v, t * deriv f t := by
  have hsub : Icc (0 : ℝ) v ⊆ Icc 0 1 :=
    Icc_subset_Icc le_rfl hv.2.le
  have hAC : AbsolutelyContinuousOnInterval f 0 v :=
    (show ContDiffOn ℝ 1 f (uIcc 0 v) by
      simpa only [uIcc_of_le hv.1.le] using hf.mono hsub).absolutelyContinuousOnInterval
  have hidAC : AbsolutelyContinuousOnInterval (fun t : ℝ => t) 0 v :=
    (show ContDiffOn ℝ 1 (fun t : ℝ => t) (uIcc 0 v) by
      fun_prop).absolutelyContinuousOnInterval
  have hparts := hAC.integral_mul_deriv_eq_deriv_mul hidAC
  simp only [deriv_id'', mul_one, mul_zero, sub_zero] at hparts
  have hcomm : (∫ t in (0 : ℝ)..v, deriv f t * t) =
      ∫ t in (0 : ℝ)..v, t * deriv f t := by
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [mul_comm (f v) v, hcomm] at hparts
  linarith only [hparts]

private theorem initial_alpha_contDiffOn {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    ContDiffOn ℝ 1 (S.alpha 0) (Icc 0 1) := by
  have hK := C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
    (by norm_num : (0 : ℝ) < 1)
  have htheta : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.theta p.1 p.2)
      (closedCoordTriangle 0 1) :=
    hK ▸ H.theta_c1
  have hlam : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.lam p.1 p.2)
      (closedCoordTriangle 0 1) :=
    hK ▸ H.lam_c1
  have hphi : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (closedCoordTriangle 0 1) :=
    hK ▸ H.phi_c1
  have hα : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.alpha p.1 p.2)
      (closedCoordTriangle 0 1) := by
    have heq : (fun p : ℝ × ℝ => S.alpha p.1 p.2) =
        (fun p => S.theta p.1 p.2 + S.lam p.1 p.2 * S.phi p.1 p.2) := by
      funext p
      simp only [Fields.theta]
      ring
    rw [heq]
    exact htheta.add (hlam.mul hphi)
  have hmap : MapsTo (fun t : ℝ => ((0 : ℝ), t)) (Icc 0 1)
      (closedCoordTriangle 0 1) := by
    intro t ht
    exact ⟨le_rfl, ht.1, ht.2⟩
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => ((0 : ℝ), t)) (Icc 0 1) := by
    fun_prop
  exact hα.comp hpair hmap

private theorem vertical_hasDerivAt_initial_edge {B : ℝ}
    {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle 0 B))
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) B) :
    HasDerivAt (fun t => f (0, t))
      ((fderivWithin ℝ f (closedCoordTriangle 0 B) (0, v)) (0, 1)) v := by
  have hp : ((0 : ℝ), v) ∈ closedCoordTriangle 0 B :=
    ⟨le_rfl, hv.1.le, hv.2.le⟩
  have hmap : MapsTo (fun t : ℝ => ((0 : ℝ), t)) (Icc 0 B)
      (closedCoordTriangle 0 B) := by
    intro t ht
    exact ⟨le_rfl, ht.1, ht.2⟩
  have hpath : HasDerivWithinAt (fun t : ℝ => ((0 : ℝ), t)) (0, 1)
      (Icc 0 B) v :=
    ((hasDerivAt_const v (0 : ℝ)).prodMk (hasDerivAt_id' v)).hasDerivWithinAt
  have hfield := (hf.differentiableOn (by norm_num) (0, v) hp).hasFDerivWithinAt
  have h := hfield.comp_hasDerivWithinAt v hpath hmap
  exact h.hasDerivAt (Icc_mem_nhds hv.1 hv.2)

private theorem bounded_amplitude_on_unit {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (closedCoordTriangle 0 1)) :
    BddAbove {x : ℝ | ∃ p ∈ developmentWithInitialEdge 1, x = |F p|} := by
  have hcont : ContinuousOn (fun p => |F p|) (closedCoordTriangle 0 1) :=
    continuous_abs.comp_continuousOn hF
  obtain ⟨M, hM⟩ :=
    ((isCompact_closedCoordTriangle 0 1).image_of_continuousOn hcont).bddAbove
  refine ⟨M, ?_⟩
  rintro x ⟨p, hp, rfl⟩
  exact hM ⟨p, ⟨hp.1, hp.2.1.le, hp.2.2.le⟩, rfl⟩

/-- The pointwise version of (4.3) used in the logarithmic corrections. -/
theorem eq4_3_pointwise {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {p : ℝ × ℝ} (hp : p ∈ developmentWithInitialEdge 1) :
    |S.theta p.1 p.2| ≤ 5 * (sourceD S).toReal ∧
      |S.zeta p.1 p.2| ≤ 8 * (sourceD S).toReal := by
  have hK := C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
    (by norm_num : (0 : ℝ) < 1)
  have htheta : ContinuousOn (fun q : ℝ × ℝ => S.theta q.1 q.2)
      (closedCoordTriangle 0 1) := (hK ▸ H.theta_c1).continuousOn
  have hzeta : ContinuousOn (fun q : ℝ × ℝ => S.zeta q.1 q.2)
      (closedCoordTriangle 0 1) := (hK ▸ H.zeta_c1).continuousOn
  have hbound := eq4_3 H hr hcenter hboot
  have hThetaBound :
      sSup {x : ℝ | ∃ q ∈ developmentWithInitialEdge 1,
        x = |S.theta q.1 q.2|} ≤ 5 * (sourceD S).toReal := by
    simpa only [sourceThetaAmp] using hbound.1
  have hZetaBound :
      sSup {x : ℝ | ∃ q ∈ developmentWithInitialEdge 1,
        x = |S.zeta q.1 q.2|} ≤ 8 * (sourceD S).toReal := by
    simpa only [sourceZetaAmp] using hbound.2
  constructor
  · exact (le_csSup (bounded_amplitude_on_unit htheta) ⟨p, hp, rfl⟩).trans hThetaBound
  · exact (le_csSup (bounded_amplitude_on_unit hzeta) ⟨p, hp, rfl⟩).trans hZetaBound

/-- The outgoing quadratic correction `f` from (4.9a). -/
noncomputable def sourceLogCorrection (S : Fields) (u v : ℝ) : ℝ :=
  S.theta u v / S.r u v *
    (S.theta u v / S.lam u v - S.zeta u v / S.nu u v)

/-- The incoming quadratic correction `f*` from (4.9b). -/
noncomputable def sourceLogCorrectionStar (S : Fields) (u v : ℝ) : ℝ :=
  S.zeta u v / S.r u v *
    (S.theta u v / S.lam u v - S.zeta u v / S.nu u v)

/-- The outgoing logarithmic residual integrated in (4.12b). -/
noncomputable def sourceOutgoingLogResidual (S : Fields) (u v : ℝ) : ℝ :=
  deriv (fun t => Real.log (S.lam u t)) v -
    (2 * S.m u v / S.r u v) /
      (1 - 2 * S.m u v / S.r u v) * (S.lam u v / S.r u v) +
        sourceLogCorrection S u v

/-- The incoming logarithmic residual integrated in the sign-corrected (4.13b).
The printed `+ f*` is an erratum; the mixed transport gives `- f*`. -/
noncomputable def sourceIncomingLogResidual (S : Fields) (u v : ℝ) : ℝ :=
  deriv (fun t => Real.log (-S.nu t v)) u -
    (2 * S.m u v / S.r u v) /
      (1 - 2 * S.m u v / S.r u v) * (S.nu u v / S.r u v) -
        sourceLogCorrectionStar S u v

/-- The second expression for `f` in (4.9a). -/
theorem eq4_9a (S : Fields) (u v : ℝ)
    (hlam : S.lam u v ≠ 0) (hnu : S.nu u v ≠ 0) :
    sourceLogCorrection S u v =
      S.theta u v / S.r u v *
        (S.alpha u v / S.lam u v - S.beta u v / S.nu u v) := by
  have hbracket :
      S.theta u v / S.lam u v - S.zeta u v / S.nu u v =
        S.alpha u v / S.lam u v - S.beta u v / S.nu u v := by
    unfold Fields.theta Fields.zeta
    field_simp [hlam, hnu]
    ring
  exact congrArg (fun x => S.theta u v / S.r u v * x) hbracket

/-- The second expression for `f*` in (4.9b). -/
theorem eq4_9b (S : Fields) (u v : ℝ)
    (hlam : S.lam u v ≠ 0) (hnu : S.nu u v ≠ 0) :
    sourceLogCorrectionStar S u v =
      S.zeta u v / S.r u v *
        (S.alpha u v / S.lam u v - S.beta u v / S.nu u v) := by
  have hbracket :
      S.theta u v / S.lam u v - S.zeta u v / S.nu u v =
        S.alpha u v / S.lam u v - S.beta u v / S.nu u v := by
    unfold Fields.theta Fields.zeta
    field_simp [hlam, hnu]
    ring
  exact congrArg (fun x => S.zeta u v / S.r u v * x) hbracket

/-- The difference of the two scalar-to-radius quotients has amplitude
at most `39D` under the Section 4 bootstrap. -/
theorem source_log_quotient_difference_bound {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {p : ℝ × ℝ} (hp : p ∈ developmentWithInitialEdge 1) :
    |S.theta p.1 p.2 / S.lam p.1 p.2 -
        S.zeta p.1 p.2 / S.nu p.1 p.2| ≤
      39 * (sourceD S).toReal := by
  let d := (sourceD S).toReal
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hLam : (1 / 3 : ℝ) ≤ S.lam p.1 p.2 := hboot.1 p hp
  have hNu : S.nu p.1 p.2 ≤ -(1 / 3 : ℝ) :=
    hBV.nu_le_neg_lower (by norm_num) hboot.1 hp
  have hLamPos : 0 < S.lam p.1 p.2 := by linarith
  have hNuNeg : S.nu p.1 p.2 < 0 := by linarith
  have hθ := (eq4_3_pointwise H hr hcenter hboot hp).1
  have hζ := (eq4_3_pointwise H hr hcenter hboot hp).2
  have hθdiv : |S.theta p.1 p.2 / S.lam p.1 p.2| ≤ 15 * d := by
    rw [abs_div, abs_of_pos hLamPos]
    apply (div_le_iff₀ hLamPos).2
    have hm := mul_le_mul_of_nonneg_left hLam hd
    dsimp [d] at hθ ⊢
    nlinarith only [hθ, hm]
  have hNuAbs : (1 / 3 : ℝ) ≤ |S.nu p.1 p.2| := by
    rw [abs_of_neg hNuNeg]
    linarith only [hNu]
  have hζdiv : |S.zeta p.1 p.2 / S.nu p.1 p.2| ≤ 24 * d := by
    rw [abs_div]
    apply (div_le_iff₀ (by linarith only [hNuAbs])).2
    have hm := mul_le_mul_of_nonneg_left hNuAbs hd
    dsimp [d] at hζ ⊢
    nlinarith only [hζ, hm]
  calc
    |S.theta p.1 p.2 / S.lam p.1 p.2 -
        S.zeta p.1 p.2 / S.nu p.1 p.2| ≤
        |S.theta p.1 p.2 / S.lam p.1 p.2| +
          |S.zeta p.1 p.2 / S.nu p.1 p.2| := abs_sub _ _
    _ ≤ 39 * d := by linarith only [hθdiv, hζdiv]

/-- Pointwise quadratic control of the outgoing correction `f`. -/
theorem source_log_correction_bound {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u v : ℝ} (hp : (u, v) ∈ developmentWithInitialEdge 1) :
    |sourceLogCorrection S u v| ≤
      39 * (sourceD S).toReal * (|S.theta u v| / S.r u v) := by
  have hrad : 0 < S.r u v := H.solution.radius_pos (u, v) hp
  have hθdiv : 0 ≤ |S.theta u v| / S.r u v :=
    div_nonneg (abs_nonneg _) hrad.le
  have hdiff := source_log_quotient_difference_bound H hr hcenter hboot hp
  rw [sourceLogCorrection, abs_mul, abs_div, abs_of_pos hrad]
  calc
    |S.theta u v| / S.r u v *
        |S.theta u v / S.lam u v - S.zeta u v / S.nu u v| ≤
        |S.theta u v| / S.r u v * (39 * (sourceD S).toReal) :=
      mul_le_mul_of_nonneg_left hdiff hθdiv
    _ = 39 * (sourceD S).toReal * (|S.theta u v| / S.r u v) := by ring

/-- In the prescribed radius gauge the initial logarithmic expansion is
constant, so its tangential derivative vanishes. -/
theorem initial_log_lam_deriv_eq_zero {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    deriv (fun t => Real.log (S.lam 0 t)) v = 0 := by
  have heq : (fun t => Real.log (S.lam 0 t)) =ᶠ[𝓝 v]
      (fun _ : ℝ => Real.log (1 / 2 : ℝ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with t ht
    rw [(source_gauge_data H hr t ht).2]
  exact ((hasDerivAt_const v (Real.log (1 / 2 : ℝ))).congr_of_eventuallyEq heq).deriv

/-- The scalar field on the normalized initial edge is twice the running
average of the prescribed `α` density. -/
theorem initial_phi_eq_alpha_running_mean {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    S.phi 0 v = 2 / v * ∫ t in (0 : ℝ)..v, S.alpha 0 t := by
  let B : ℝ := (v + 1) / 2
  have hB : 0 < B := by dsimp [B]; linarith only [hv.1]
  have hvB : v < B := by dsimp [B]; linarith only [hv.2]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hv.2]
  have hp : ((0 : ℝ), v) ∈ closedCoordTriangle 0 B :=
    ⟨le_rfl, hv.1.le, hvB.le⟩
  have hψ := C1Solution.canonicalScalarRadius_eq_canonicalRadius_mul_phi
    hB hB1 H hp
  rw [C1Solution.canonicalRadius_eq_radius hB hB1 H
    le_rfl hv.1 hvB.le, hr v hv] at hψ
  change (∫ t in (0 : ℝ)..v, S.alpha 0 t) = v / 2 * S.phi 0 v at hψ
  apply (mul_left_cancel₀ (ne_of_gt hv.1))
  calc
    v * S.phi 0 v = 2 * (v / 2 * S.phi 0 v) := by ring
    _ = 2 * ∫ t in (0 : ℝ)..v, S.alpha 0 t := by rw [← hψ]
    _ = v * (2 / v * ∫ t in (0 : ℝ)..v, S.alpha 0 t) := by
      field_simp [hv.1.ne']

/-- The initial outgoing scalar amplitude is the deviation of `α` from
its running mean. -/
theorem initial_theta_eq_alpha_sub_mean {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    S.theta 0 v = S.alpha 0 v -
      (∫ t in (0 : ℝ)..v, S.alpha 0 t) / v := by
  rw [Fields.theta, (source_gauge_data H hr v hv).2,
    initial_phi_eq_alpha_running_mean H hr hv]
  field_simp [hv.1.ne']

/-- Integration by parts expresses the initial scalar amplitude through
the derivative of the prescribed density. -/
theorem initial_theta_eq_weighted_alpha_deriv {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    S.theta 0 v =
      (∫ t in (0 : ℝ)..v, t * deriv (S.alpha 0) t) / v := by
  rw [initial_theta_eq_alpha_sub_mean H hr hv]
  have hparts := integral_mul_deriv_initial (initial_alpha_contDiffOn H) hv
  rw [← hparts]
  field_simp [hv.1.ne']

/-- Pointwise Hardy majorant for the initial outgoing scalar derivative. -/
theorem initial_theta_over_r_le_hardy {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    |S.theta 0 v| / S.r 0 v ≤
      2 * (∫ t in (0 : ℝ)..v, t * |deriv (S.alpha 0) t|) / v ^ 2 := by
  have hInt :
      |∫ t in (0 : ℝ)..v, t * deriv (S.alpha 0) t| ≤
        ∫ t in (0 : ℝ)..v, t * |deriv (S.alpha 0) t| := by
    calc
      |∫ t in (0 : ℝ)..v, t * deriv (S.alpha 0) t| ≤
          ∫ t in (0 : ℝ)..v, |t * deriv (S.alpha 0) t| :=
        intervalIntegral.abs_integral_le_integral_abs hv.1.le
      _ = ∫ t in (0 : ℝ)..v, t * |deriv (S.alpha 0) t| := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with t ht
        have ht' : t ∈ Ioc (0 : ℝ) v := by
          simpa only [uIoc_of_le hv.1.le] using ht
        rw [abs_mul, abs_of_nonneg ht'.1.le]
  rw [initial_theta_eq_weighted_alpha_deriv H hr hv, hr v hv]
  have hv2 : 0 < v ^ 2 := sq_pos_of_pos hv.1
  have heq :
      |(∫ t in (0 : ℝ)..v, t * deriv (S.alpha 0) t) / v| / (v / 2) =
        2 * |∫ t in (0 : ℝ)..v, t * deriv (S.alpha 0) t| / v ^ 2 := by
    rw [abs_div, abs_of_pos hv.1]
    field_simp [hv.1.ne']
  rw [heq]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hInt (by norm_num)) hv2.le

/-- The initial Hardy majorant is bounded by the data variation `D`.
This is the endpoint integral needed to turn the pointwise quadratic
correction estimate into an `O(D²)` residual. -/
theorem initial_hardy_integral_le_sourceD {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    (∫ v in (0 : ℝ)..1,
      (∫ t in (0 : ℝ)..v, t * |deriv (S.alpha 0) t|) / v ^ 2) ≤
        (sourceD S).toReal := by
  have hα := initial_alpha_contDiffOn H
  have hAC : AbsolutelyContinuousOnInterval (S.alpha 0) 0 1 :=
    (show ContDiffOn ℝ 1 (S.alpha 0) (uIcc 0 1) by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hα).absolutelyContinuousOnInterval
  have hAbs : IntervalIntegrable (fun t => |deriv (S.alpha 0) t|)
      volume 0 1 := hAC.intervalIntegrable_deriv.abs
  have hF : IntervalIntegrable (fun t => t * |deriv (S.alpha 0) t|)
      volume 0 1 := by
    exact hAbs.continuousOn_mul continuous_id.continuousOn
  have hW : IntervalIntegrable
      (fun t => (t * |deriv (S.alpha 0) t|) / (t - 0)) volume 0 1 := by
    apply hAbs.congr_uIoo
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by
      simpa only [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    have ht0 : t ≠ 0 := ne_of_gt ht'.1
    simp only [sub_zero]
    field_simp [ht0]
  have hFnonneg : ∀ t ∈ Icc (0 : ℝ) 1,
      0 ≤ t * |deriv (S.alpha 0) t| := by
    intro t ht
    exact mul_nonneg ht.1 (abs_nonneg _)
  have hHardy := intervalIntegral.integral_integral_div_sq_le
    (by norm_num : (0 : ℝ) < 1) hF hW hFnonneg
  have hLeft :
      (∫ v in (0 : ℝ)..1,
        (∫ t in (0 : ℝ)..v, t * |deriv (S.alpha 0) t|) / v ^ 2) =
      ∫ v in (0 : ℝ)..1,
        (∫ t in (0 : ℝ)..v, t * |deriv (S.alpha 0) t|) / (v - 0) ^ 2 := by
    simp only [sub_zero]
  have hRight :
      (∫ t in (0 : ℝ)..1,
        (t * |deriv (S.alpha 0) t|) / (t - 0)) =
      ∫ t in (0 : ℝ)..1, |deriv (S.alpha 0) t| := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    have ht' : t ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    have ht0 : t ≠ 0 := ne_of_gt ht'.1
    simp only [sub_zero]
    field_simp [ht0]
  have hD : (sourceD S).toReal =
      ∫ t in (0 : ℝ)..1, |deriv (S.alpha 0) t| := by
    rw [sourceD, AbsolutelyContinuousOnInterval.eVariationOn_Ioo_eq_integral_abs_deriv
      (by norm_num : (0 : ℝ) ≤ 1) hAC]
    exact ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg
      (by norm_num : (0 : ℝ) ≤ 1) (fun _ _ => abs_nonneg _))
  rw [← hLeft, hRight] at hHardy
  rw [hD]
  exact hHardy

/-- The initial outgoing scalar derivative has an integrable `2D` bound.
The interval starts at the origin, which is excluded from Lemma 4.1's
positive outgoing slices. -/
theorem initial_theta_integral_le_sourceD {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2) :
    (∫ v in (0 : ℝ)..1, |S.theta 0 v| / S.r 0 v) ≤
      2 * (sourceD S).toReal := by
  let G : ℝ → ℝ := fun v =>
    (∫ t in (0 : ℝ)..v, t * |deriv (S.alpha 0) t|) / v ^ 2
  let T : ℝ → ℝ := fun v => 2 * |S.theta 0 v| / v
  have hα := initial_alpha_contDiffOn H
  have hAC : AbsolutelyContinuousOnInterval (S.alpha 0) 0 1 :=
    (show ContDiffOn ℝ 1 (S.alpha 0) (uIcc 0 1) by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hα).absolutelyContinuousOnInterval
  have hAbs : IntervalIntegrable (fun t => |deriv (S.alpha 0) t|)
      volume 0 1 := hAC.intervalIntegrable_deriv.abs
  have hF : IntervalIntegrable (fun t => t * |deriv (S.alpha 0) t|)
      volume 0 1 := hAbs.continuousOn_mul continuous_id.continuousOn
  have hW : IntervalIntegrable
      (fun t => (t * |deriv (S.alpha 0) t|) / (t - 0)) volume 0 1 := by
    apply hAbs.congr_uIoo
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by
      simpa only [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    have ht0 : t ≠ 0 := ne_of_gt ht'.1
    simp only [sub_zero]
    field_simp [ht0]
  have hFnonneg : ∀ t ∈ Icc (0 : ℝ) 1,
      0 ≤ t * |deriv (S.alpha 0) t| := by
    intro t ht
    exact mul_nonneg ht.1 (abs_nonneg _)
  have hGI : IntervalIntegrable G volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).2
    simpa only [G, sub_zero] using intervalIntegral.integrableOn_integral_div_sq
      (by norm_num : (0 : ℝ) < 1) hF hW hFnonneg
  have hThetaCont : ContinuousOn (S.theta 0) (Ioo (0 : ℝ) 1) := by
    have hK := C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
      (by norm_num : (0 : ℝ) < 1)
    have hθ : ContinuousOn (fun p : ℝ × ℝ => S.theta p.1 p.2)
        (closedCoordTriangle 0 1) := (hK ▸ H.theta_c1).continuousOn
    exact hθ.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨le_rfl, hv.1.le, hv.2.le⟩)
  have hTCont : ContinuousOn T (Ioo (0 : ℝ) 1) := by
    dsimp [T]
    apply (continuousOn_const.mul hThetaCont.abs).div
      (continuous_id.continuousOn)
    intro v hv
    exact ne_of_gt hv.1
  have hTMeas : AEStronglyMeasurable T
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact hTCont.aestronglyMeasurable measurableSet_Ioo
  have hpoint (v : ℝ) (hv : v ∈ Ioo (0 : ℝ) 1) : T v ≤ 2 * G v := by
    have h := initial_theta_over_r_le_hardy H hr hv
    rw [hr v hv] at h
    calc
      T v = |S.theta 0 v| / (v / 2) := by
        dsimp [T]
        field_simp [hv.1.ne']
      _ ≤ 2 * (∫ t in (0 : ℝ)..v, t * |deriv (S.alpha 0) t|) / v ^ 2 := h
      _ = 2 * G v := by dsimp [G]; ring
  have hbound : (fun v => ‖T v‖) ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun v => 2 * G v) := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro v hv
    have ht : 0 ≤ T v := by
      dsimp [T]
      exact div_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) hv.1.le
    change ‖T v‖ ≤ 2 * G v
    rw [Real.norm_eq_abs, abs_of_nonneg ht]
    exact hpoint v hv
  have hTI : IntervalIntegrable T volume 0 1 :=
    (hGI.const_mul 2).mono_fun'
      (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hTMeas)
      (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hbound)
  have hGI2 : IntervalIntegrable (fun v => 2 * G v) volume 0 1 :=
    hGI.const_mul 2
  have hmono : (∫ v in (0 : ℝ)..1, T v) ≤
      ∫ v in (0 : ℝ)..1, 2 * G v := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num : (0 : ℝ) ≤ 1) hTI hGI2
    intro v hv
    exact hpoint v hv
  have hTarget : (∫ v in (0 : ℝ)..1, |S.theta 0 v| / S.r 0 v) =
      ∫ v in (0 : ℝ)..1, T v := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with v hne hv
    have hv' : v ∈ Ioo (0 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
      exact ⟨hv.1, lt_of_le_of_ne hv.2 hne⟩
    dsimp [T]
    rw [hr v hv']
    field_simp [hv'.1.ne']
  rw [hTarget]
  calc
    (∫ v in (0 : ℝ)..1, T v) ≤
        ∫ v in (0 : ℝ)..1, 2 * G v := hmono
    _ = 2 * ∫ v in (0 : ℝ)..1, G v := by
      rw [← intervalIntegral.integral_const_mul]
    _ ≤ 2 * (sourceD S).toReal := by
      exact mul_le_mul_of_nonneg_left
        (initial_hardy_integral_le_sourceD H) (by norm_num)

/-- On the initial edge, the source null density is the ordinary tangential
derivative of the scalar field. -/
theorem initial_theta_over_r_eq_abs_phi_deriv {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    |S.theta 0 v| / S.r 0 v = |deriv (S.phi 0) v| := by
  let B : ℝ := (v + 1) / 2
  have hB : 0 < B := by dsimp [B]; linarith only [hv.1]
  have hvB : v < B := by dsimp [B]; linarith only [hv.2]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hv.2]
  have hp : ((0 : ℝ), v) ∈ closedCoordTriangle 0 B :=
    ⟨le_rfl, hv.1.le, hvB.le⟩
  have hphi := (C1Solution.five_fields_contDiffOn hB hB1 H).2.2.1
  have hderiv := (vertical_hasDerivAt_initial_edge hphi
    ⟨hv.1, hvB⟩).deriv
  have htheta := C1Solution.theta_eq_canonicalRadius_mul_phi_vertical_jet
    hB hB1 H hp
  rw [C1Solution.canonicalRadius_eq_radius hB hB1 H
    le_rfl hv.1 hvB.le] at htheta
  rw [← hderiv] at htheta
  have hrad : 0 < S.r 0 v := H.solution.radius_pos (0, v)
    ⟨le_rfl, hv.1, hv.2⟩
  rw [htheta, abs_mul, abs_of_pos hrad]
  field_simp [hrad.ne']

/-- The initial scalar trace has total variation at most `2D`. -/
theorem initial_phi_variation_le_sourceD {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2) :
    (eVariationOn (S.phi 0) (Ioo (0 : ℝ) 1)).toReal ≤
      2 * (sourceD S).toReal := by
  have hK := C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
    (by norm_num : (0 : ℝ) < 1)
  have hφ : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (closedCoordTriangle 0 1) := hK ▸ H.phi_c1
  have hmap : MapsTo (fun t : ℝ => ((0 : ℝ), t)) (Icc 0 1)
      (closedCoordTriangle 0 1) := by
    intro t ht
    exact ⟨le_rfl, ht.1, ht.2⟩
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => ((0 : ℝ), t)) (Icc 0 1) := by
    fun_prop
  have hφedge : ContDiffOn ℝ 1 (S.phi 0) (Icc 0 1) :=
    hφ.comp hpair hmap
  have hAC : AbsolutelyContinuousOnInterval (S.phi 0) 0 1 :=
    (show ContDiffOn ℝ 1 (S.phi 0) (uIcc 0 1) by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        using hφedge).absolutelyContinuousOnInterval
  have hIntegralEq :
      (∫ v in (0 : ℝ)..1, |deriv (S.phi 0) v|) =
      ∫ v in (0 : ℝ)..1, |S.theta 0 v| / S.r 0 v := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with v hne hv
    have hv' : v ∈ Ioo (0 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
      exact ⟨hv.1, lt_of_le_of_ne hv.2 hne⟩
    exact (initial_theta_over_r_eq_abs_phi_deriv H hv').symm
  have hIntNonneg : 0 ≤ ∫ v in (0 : ℝ)..1,
      |deriv (S.phi 0) v| := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro _ _
    exact abs_nonneg _
  rw [AbsolutelyContinuousOnInterval.eVariationOn_Ioo_eq_integral_abs_deriv
    (by norm_num : (0 : ℝ) ≤ 1) hAC, ENNReal.toReal_ofReal hIntNonneg]
  rw [hIntegralEq]
  exact initial_theta_integral_le_sourceD H hr

/-- The outgoing scalar quotient is bounded by `15D` throughout the unit
development. -/
theorem source_theta_div_lam_le_sourceD {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {p : ℝ × ℝ} (hp : p ∈ developmentWithInitialEdge 1) :
    |S.theta p.1 p.2 / S.lam p.1 p.2| ≤
      15 * (sourceD S).toReal := by
  have hLam : (1 / 3 : ℝ) ≤ S.lam p.1 p.2 := hboot.1 p hp
  have hLamPos : 0 < S.lam p.1 p.2 := by linarith only [hLam]
  have hθ := (eq4_3_pointwise H hr hcenter hboot hp).1
  have hD : 0 ≤ (sourceD S).toReal := ENNReal.toReal_nonneg
  rw [abs_div, abs_of_pos hLamPos]
  apply (div_le_iff₀ hLamPos).2
  have hm := mul_le_mul_of_nonneg_left hLam hD
  nlinarith only [hθ, hm]

/-- The initial scalar variation is finite on the open unit interval. -/
private theorem initial_phi_variation_ne_top {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    eVariationOn (S.phi 0) (Ioo (0 : ℝ) 1) ≠ ⊤ := by
  have hK := C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
    (by norm_num : (0 : ℝ) < 1)
  have hφ : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (closedCoordTriangle 0 1) := hK ▸ H.phi_c1
  have hmap : MapsTo (fun t : ℝ => ((0 : ℝ), t)) (Icc 0 1)
      (closedCoordTriangle 0 1) := by
    intro t ht
    exact ⟨le_rfl, ht.1, ht.2⟩
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => ((0 : ℝ), t)) (Icc 0 1) := by
    fun_prop
  have hφedge : ContDiffOn ℝ 1 (S.phi 0) (Icc 0 1) :=
    hφ.comp hpair hmap
  have hAC : AbsolutelyContinuousOnInterval (S.phi 0) 0 1 :=
    (show ContDiffOn ℝ 1 (S.phi 0) (uIcc 0 1) by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        using hφedge).absolutelyContinuousOnInterval
  rw [AbsolutelyContinuousOnInterval.eVariationOn_Ioo_eq_integral_abs_deriv
    (by norm_num : (0 : ℝ) ≤ 1) hAC]
  exact ENNReal.ofReal_ne_top

/-- On every finite initial cutoff, the mass-ratio contribution to the
logarithmic residual is bounded by `30D²`. -/
theorem initial_mass_ratio_cutoff_le_sourceD {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..v,
      (2 * S.m 0 t / S.r 0 t) * S.lam 0 t /
        ((1 - 2 * S.m 0 t / S.r 0 t) * S.r 0 t)) ≤
      30 * (sourceD S).toReal ^ 2 := by
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hp : ((0 : ℝ), v) ∈ developmentWithInitialEdge 1 :=
    ⟨le_rfl, hv.1, hv.2⟩
  have hM : ∀ p ∈ developmentWithInitialEdge 1,
      |S.theta p.1 p.2 / S.lam p.1 p.2| ≤
        15 * (sourceD S).toReal := by
    intro p hp
    exact source_theta_div_lam_le_sourceD H hr hcenter hboot hp
  have hmass := source_mass_ratio_out_majorant hBV hp hM
  have hvar :
      (eVariationOn (S.phi 0) (Ioo (0 : ℝ) v)).toReal ≤
        2 * (sourceD S).toReal := by
    have hsubset : Ioo (0 : ℝ) v ⊆ Ioo (0 : ℝ) 1 := by
      intro t ht
      exact ⟨ht.1, ht.2.trans hv.2⟩
    have hmono := eVariationOn.mono (S.phi 0) hsubset
    exact (ENNReal.toReal_mono (initial_phi_variation_ne_top H) hmono).trans
      (initial_phi_variation_le_sourceD H hr)
  calc
    (∫ t in (0 : ℝ)..v,
      (2 * S.m 0 t / S.r 0 t) * S.lam 0 t /
        ((1 - 2 * S.m 0 t / S.r 0 t) * S.r 0 t)) ≤
        15 * (sourceD S).toReal *
          (eVariationOn (S.phi 0) (Ioo (0 : ℝ) v)).toReal := hmass
    _ ≤ 15 * (sourceD S).toReal * (2 * (sourceD S).toReal) := by
      exact mul_le_mul_of_nonneg_left hvar (by positivity)
    _ = 30 * (sourceD S).toReal ^ 2 := by ring

/-- The initial null density is integrable all the way to the regular
origin. -/
theorem initial_theta_over_r_integrable {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    IntervalIntegrable (fun v => |S.theta 0 v| / S.r 0 v) volume 0 1 := by
  have hK := C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
    (by norm_num : (0 : ℝ) < 1)
  have hφ : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (closedCoordTriangle 0 1) := hK ▸ H.phi_c1
  have hmap : MapsTo (fun t : ℝ => ((0 : ℝ), t)) (Icc 0 1)
      (closedCoordTriangle 0 1) := by
    intro t ht
    exact ⟨le_rfl, ht.1, ht.2⟩
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => ((0 : ℝ), t)) (Icc 0 1) := by
    fun_prop
  have hφedge : ContDiffOn ℝ 1 (S.phi 0) (Icc 0 1) :=
    hφ.comp hpair hmap
  have hAC : AbsolutelyContinuousOnInterval (S.phi 0) 0 1 :=
    (show ContDiffOn ℝ 1 (S.phi 0) (uIcc 0 1) by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        using hφedge).absolutelyContinuousOnInterval
  apply hAC.intervalIntegrable_deriv.abs.congr_uIoo
  intro v hv
  have hv' : v ∈ Ioo (0 : ℝ) 1 := by
    simpa only [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hv
  exact (initial_theta_over_r_eq_abs_phi_deriv H hv').symm

end ChristodoulouBV

end
