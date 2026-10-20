module

public import ChristodoulouBV.AreaEstimates.LogTransportSliceMass
import ChristodoulouBV.AreaEstimates.LogTransportInitialResidual
import Mathlib.Tactic
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Section 4 logarithmic variation on null slices and the regular axis
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

private noncomputable def sliceOutgoingLogMajorant (S : Fields) (v : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |sourceOutgoingLogResidual S 0 v| +
    ∫⁻ u in Ioo 0 v,
      ENNReal.ofReal |(fderiv ℝ (sourcePhiBetaNuMap S) (u, v)).det|

private theorem slice_outgoing_majorant_integral_le {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    (∫⁻ v in Ioo (0 : ℝ) 1, sliceOutgoingLogMajorant S v) ≤
      ENNReal.ofReal (108 * (sourceD S).toReal ^ 2) +
        smoothAnalyticArea (sourcePhiBetaNuMap S)
          (openCoordTriangle 0 1) := by
  let I : ℝ → ℝ≥0∞ := fun v =>
    ENNReal.ofReal |sourceOutgoingLogResidual S 0 v|
  let J : ℝ → ℝ≥0∞ := fun v => ∫⁻ u in Ioo 0 v,
    ENNReal.ofReal |(fderiv ℝ (sourcePhiBetaNuMap S) (u, v)).det|
  have hIOn : IntegrableOn (fun v => |sourceOutgoingLogResidual S 0 v|)
      (Ioo (0 : ℝ) 1) := by
    have h := (initial_log_residual_integrable H hr hcenter hboot).1
    exact h.mono_set Ioo_subset_Ioc_self
  have hI : AEMeasurable I (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (hIOn.aestronglyMeasurable.aemeasurable).ennreal_ofReal
  have hReal : (∫⁻ v in Ioo (0 : ℝ) 1, I v) =
      ENNReal.ofReal
        (∫ v in (0 : ℝ)..1, |sourceOutgoingLogResidual S 0 v|) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
    exact (ofReal_integral_eq_lintegral_ofReal hIOn
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)).symm
  have hT : MeasurableSet (openCoordTriangle 0 1) := by
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior.measurableSet
  have hCarrier :
      {p : ℝ × ℝ | p.1 ∈ Ioo 0 1 ∧ p.2 ∈ Ioo p.1 1} =
        openCoordTriangle 0 1 := by
    ext p
    simp only [openCoordTriangle, mem_ofPred_eq, mem_Ioo]
    constructor
    · rintro ⟨⟨h0, _⟩, ⟨h12, h2⟩⟩
      exact ⟨h0, h12, h2⟩
    · rintro ⟨h0, h12, h2⟩
      exact ⟨⟨h0, h12.trans h2⟩, ⟨h12, h2⟩⟩
  have hJac : (∫⁻ v in Ioo (0 : ℝ) 1, J v) =
      smoothAnalyticArea (sourcePhiBetaNuMap S) (openCoordTriangle 0 1) := by
    let K : ℝ × ℝ → ℝ≥0∞ := fun p =>
      ENNReal.ofReal |(fderiv ℝ (sourcePhiBetaNuMap S) p).det|
    have hK : AEMeasurable K (volume.restrict (openCoordTriangle 0 1)) :=
      (source_log_jacobian_densities_measurable S).1.aemeasurable
    rw [smooth_analytic_area _ hT]
    simpa only [J, K, hCarrier] using
      (lintegral_open_triangle_swap 0 1 K (by
        simpa only [hCarrier] using hK)).symm
  calc
    (∫⁻ v in Ioo (0 : ℝ) 1, sliceOutgoingLogMajorant S v) =
        (∫⁻ v in Ioo (0 : ℝ) 1, I v) +
          (∫⁻ v in Ioo (0 : ℝ) 1, J v) := by
      change (∫⁻ v in Ioo (0 : ℝ) 1, I v + J v) = _
      exact lintegral_add_left' hI J
    _ = ENNReal.ofReal
          (∫ v in (0 : ℝ)..1, |sourceOutgoingLogResidual S 0 v|) +
          smoothAnalyticArea (sourcePhiBetaNuMap S)
            (openCoordTriangle 0 1) := by rw [hReal, hJac]
    _ ≤ ENNReal.ofReal (108 * (sourceD S).toReal ^ 2) +
          smoothAnalyticArea (sourcePhiBetaNuMap S)
            (openCoordTriangle 0 1) :=
      add_le_add
        (ENNReal.ofReal_le_ofReal
          (initial_log_residual H hr hcenter hboot)) le_rfl

/-- Equation (4.12c): outgoing log-`λ` variation on all normalized null
slices. The universal coefficients of `D²` and `DX` are `108` and `54`. -/
theorem eq4_12c {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    (⨆ u ∈ Ioo (0 : ℝ) 1,
      eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1)) ≤
      ENNReal.ofReal (108 * (sourceD S).toReal ^ 2) +
        ENNReal.ofReal (54 * (sourceD S).toReal) * sourceX S +
          smoothAnalyticArea (sourcePhiBetaNuMap S)
            (openCoordTriangle 0 1) := by
  apply iSup_le
  intro u
  apply iSup_le
  intro hu
  have hRes := (eq4_12b_corrected H hr hcenter hboot hu).2
  have hMass := outgoing_mass_lintegral_le H hr hcenter hboot hu
  have hCorr := outgoing_correction_lintegral_le H hr hcenter hboot hu
  have hd : 0 ≤ (sourceD S).toReal := ENNReal.toReal_nonneg
  have hCoeff :
      ENNReal.ofReal (15 * (sourceD S).toReal) +
        ENNReal.ofReal (39 * (sourceD S).toReal) =
          ENNReal.ofReal (54 * (sourceD S).toReal) := by
    rw [← ENNReal.ofReal_add
      (by nlinarith only [hd]) (by nlinarith only [hd])]
    congr 1
    ring
  calc
    eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1) ≤
        (∫⁻ v in Ioo u 1,
          ENNReal.ofReal |sourceOutgoingLogResidual S u v|) +
          (∫⁻ v in Ioo u 1,
            ENNReal.ofReal (IsBVSolution.nuCoeff S u v)) +
            (∫⁻ v in Ioo u 1,
              ENNReal.ofReal |sourceLogCorrection S u v|) :=
      outgoing_log_variation_le_components H hr hcenter hboot hu
    _ ≤ (ENNReal.ofReal (108 * (sourceD S).toReal ^ 2) +
          smoothAnalyticArea (sourcePhiBetaNuMap S)
            (openCoordTriangle 0 1)) +
          ENNReal.ofReal (15 * (sourceD S).toReal) * sourceX S +
          ENNReal.ofReal (39 * (sourceD S).toReal) * sourceX S := by
      exact add_le_add (add_le_add hRes hMass) hCorr
    _ = _ := by
      calc
        _ = (ENNReal.ofReal (108 * (sourceD S).toReal ^ 2) +
              smoothAnalyticArea (sourcePhiBetaNuMap S) (openCoordTriangle 0 1)) +
              (ENNReal.ofReal (15 * (sourceD S).toReal) +
                ENNReal.ofReal (39 * (sourceD S).toReal)) * sourceX S := by
          rw [add_mul]
          ac_rfl
        _ = _ := by rw [hCoeff]; ac_rfl

/-- Sign-corrected equation (4.13c): incoming log-`|ν|` variation. The
`− f*` residual enters only through its absolute value; the universal
coefficient of `DY` is `63`. -/
theorem eq4_13c {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    (⨆ v ∈ Ioo (0 : ℝ) 1,
      eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo 0 v)) ≤
      ENNReal.ofReal (63 * (sourceD S).toReal) * sourceY S +
        eVariationOn (fun u => Real.log (-S.nu u u)) (Ioo 0 1) +
          smoothAnalyticArea (sourcePhiAlphaLamMap S)
            (openCoordTriangle 0 1) := by
  apply iSup_le
  intro v
  apply iSup_le
  intro hv
  have hRes := (eq4_13b_corrected H hr hcenter hboot hv).2
  have hMass := incoming_mass_lintegral_le H hr hcenter hboot hv
  have hCorr := incoming_correction_lintegral_le H hr hcenter hboot hv
  have hd : 0 ≤ (sourceD S).toReal := ENNReal.toReal_nonneg
  have hCoeff :
      ENNReal.ofReal (24 * (sourceD S).toReal) +
        ENNReal.ofReal (39 * (sourceD S).toReal) =
          ENNReal.ofReal (63 * (sourceD S).toReal) := by
    rw [← ENNReal.ofReal_add
      (by nlinarith only [hd]) (by nlinarith only [hd])]
    congr 1
    ring
  calc
    eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo 0 v) ≤
        (∫⁻ u in Ioo 0 v,
          ENNReal.ofReal |sourceIncomingLogResidual S u v|) +
          (∫⁻ u in Ioo 0 v,
            ENNReal.ofReal (-IsBVSolution.incomingCoeff S u v)) +
            (∫⁻ u in Ioo 0 v,
              ENNReal.ofReal |sourceLogCorrectionStar S u v|) :=
      incoming_log_variation_le_components H hr hcenter hboot hv
    _ ≤ (eVariationOn (fun u => Real.log (-S.nu u u)) (Ioo 0 1) +
          smoothAnalyticArea (sourcePhiAlphaLamMap S)
            (openCoordTriangle 0 1)) +
          ENNReal.ofReal (24 * (sourceD S).toReal) * sourceY S +
          ENNReal.ofReal (39 * (sourceD S).toReal) * sourceY S := by
      exact add_le_add (add_le_add hRes hMass) hCorr
    _ = _ := by
      calc
        _ = (eVariationOn (fun u => Real.log (-S.nu u u)) (Ioo 0 1) +
              smoothAnalyticArea (sourcePhiAlphaLamMap S) (openCoordTriangle 0 1)) +
              (ENNReal.ofReal (24 * (sourceD S).toReal) +
                ENNReal.ofReal (39 * (sourceD S).toReal)) * sourceY S := by
          rw [add_mul]
          ac_rfl
        _ = _ := by rw [hCoeff]; ac_rfl

private theorem outgoing_log_diagonal_deriv {B : ℝ} (_hB : 0 < B)
    {S : Fields} (hlog : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => Real.log (S.lam p.1 p.2))
      (closedCoordTriangle 0 B))
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) B) :
    deriv (fun t => Real.log (S.lam t t)) u =
      (fderivWithin ℝ (fun p : ℝ × ℝ => Real.log (S.lam p.1 p.2))
        (closedCoordTriangle 0 B) (u, u)) (1, 0) +
      (fderivWithin ℝ (fun p : ℝ × ℝ => Real.log (S.lam p.1 p.2))
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

private theorem outgoing_closed_residual_axis {B : ℝ}
    (hB : 0 < B) (hB1 : B < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) B) :
    sourceOutgoingLogResidualClosed B S (u, u) =
      deriv (fun t => Real.log (S.lam t t)) u := by
  let K := closedCoordTriangle 0 B
  have hpK : (u, u) ∈ K := ⟨hu.1.le, le_rfl, hu.2.le⟩
  have hUnique : UniqueDiffWithinAt ℝ K (u, u) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB) (u, u) hpK
  have hlam := (C1Solution.five_fields_contDiffOn hB hB1 H).1
  have hlamDiff : DifferentiableWithinAt ℝ
      (fun p : ℝ × ℝ => S.lam p.1 p.2) K (u, u) :=
    hlam.differentiableOn (by norm_num) (u, u) hpK
  obtain ⟨c, hc, hcl⟩ := C1Solution.exists_lam_lower_bound hB hB1 H
  have hlamNe : S.lam u u ≠ 0 := ne_of_gt (hc.trans_le (hcl (u, u) hpK))
  have hlog : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => Real.log (S.lam p.1 p.2)) K :=
    hlam.log (fun p hp => ne_of_gt (hc.trans_le (hcl p hp)))
  have hlamU := (C1Solution.four_mixed_axis_jets hB hB1 H
    ⟨hu.1.le, hu.2.le⟩).1
  have hlogU :
      (fderivWithin ℝ (fun p : ℝ × ℝ => Real.log (S.lam p.1 p.2))
        K (u, u)) (1, 0) = 0 := by
    rw [fderivWithin.log hlamDiff hlamNe hUnique]
    simp only [smul_apply]
    rw [hlamU]
    simp
  have hNuNe : S.nu u u ≠ 0 := ne_of_lt
    (C1Solution.nu_neg_closed_triangle hB hB1 H hpK)
  have hQuot :
      S.alpha u u / S.lam u u - S.beta u u / S.nu u u = 0 := by
    rw [C1Solution.alpha_eq_lam_mul_phi_axis hB hB1 H
      ⟨hu.1.le, hu.2.le⟩,
      C1Solution.beta_eq_nu_mul_phi_axis hB hB1 H
      ⟨hu.1.le, hu.2.le⟩]
    field_simp [hlamNe, hNuNe]
    ring
  have hDiag := outgoing_log_diagonal_deriv hB hlog hu
  rw [hlogU, zero_add] at hDiag
  rw [sourceOutgoingLogResidualClosed,
    C1Solution.canonicalMixedCoefficient_axis, hQuot]
  simp only [zero_div, mul_zero, sub_zero, add_zero]
  exact hDiag.symm

private theorem axis_log_deriv_le_outgoing_majorant {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    ENNReal.ofReal |deriv (fun t => Real.log (S.lam t t)) u| ≤
      sliceOutgoingLogMajorant S u := by
  let B : ℝ := (u + 1) / 2
  let K := closedCoordTriangle (0 : ℝ) B
  let R : ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal |sourceOutgoingLogResidualClosed B S (x, u)|
  have hB : 0 < B := by dsimp [B]; linarith only [hu.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hu.2]
  have huB : u < B := by dsimp [B]; linarith only [hu.2]
  have hmap : MapsTo (fun x : ℝ => (x, u)) (Icc 0 u) K := by
    intro x hx
    exact ⟨hx.1, hx.2, huB.le⟩
  have hpath : ContinuousOn (fun x : ℝ => (x, u)) (Icc 0 u) := by
    fun_prop
  have hRcont : ContinuousOn R (Icc 0 u) := by
    have hclosed := (closed_log_residual_data hB hB1 H).1.comp hpath hmap
    exact ENNReal.continuous_ofReal.comp_continuousOn hclosed.abs
  have hleft : Tendsto (fun x : ℝ => x) (𝓝[<] u) (𝓝[Icc 0 u] u) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left inf_le_left,
      mem_of_superset (Ioo_mem_nhdsLT hu.1)
        (fun x hx => ⟨hx.1.le, hx.2.le⟩)⟩
  have hlim : Tendsto R (𝓝[<] u) (𝓝 (R u)) :=
    (hRcont.continuousWithinAt ⟨hu.1.le, le_rfl⟩).tendsto.comp hleft
  have hbound : ∀ᶠ x in 𝓝[<] u,
      R x ≤ sliceOutgoingLogMajorant S u := by
    filter_upwards [Ioo_mem_nhdsLT hu.1] with x hx
    have hp : (x, u) ∈ openCoordTriangle 0 1 :=
      ⟨hx.1, hx.2, hu.2⟩
    have hEq : R x =
        ENNReal.ofReal |sourceOutgoingLogResidual S x u| := by
      change ENNReal.ofReal |sourceOutgoingLogResidualClosed B S (x, u)| = _
      rw [sourceOutgoingLogResidualClosed_eq hB hB1 H
        hx.1.le hx.2 huB]
    rw [hEq]
    exact (eq4_12a H hr hcenter hboot hp).trans (by
      simp only [sliceOutgoingLogMajorant]
      exact add_le_add le_rfl
        (lintegral_mono_set (Ioo_subset_Ioo_right hx.2.le)))
  have haxis := le_of_tendsto hlim hbound
  simpa only [R, outgoing_closed_residual_axis hB hB1 H
    ⟨hu.1, huB⟩] using haxis

/-- Equation (4.14): regular-axis log-`λ` variation is controlled by the
true initial logarithmic residual and the analytic `(φ, β/ν)` area. The
universal coefficient of `D²` is `108`. -/
theorem eq4_14 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    eVariationOn (fun t => Real.log (S.lam t t)) (Ioo 0 1) ≤
      ENNReal.ofReal (108 * (sourceD S).toReal ^ 2) +
        smoothAnalyticArea (sourcePhiBetaNuMap S)
          (openCoordTriangle 0 1) := by
  rw [variation_Ioo_unit_eq_iSup_cutoff _ (by norm_num : (0 : ℝ) < 1)]
  apply iSup_le
  intro b
  apply iSup_le
  intro hb
  let B : ℝ := (b + 1) / 2
  let K := closedCoordTriangle (0 : ℝ) B
  have hB : 0 < B := by dsimp [B]; linarith only [hb.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hb.2]
  have hbB : b < B := by dsimp [B]; linarith only [hb.2]
  have hmap : MapsTo (fun t : ℝ => (t, t)) (Icc 0 b) K := by
    intro t ht
    exact ⟨ht.1, le_rfl, ht.2.trans hbB.le⟩
  have hpath : ContDiffOn ℝ 1 (fun t : ℝ => (t, t)) (Icc 0 b) := by
    fun_prop
  have hlam := (C1Solution.five_fields_contDiffOn hB hB1 H).1
  obtain ⟨c, hc, hcl⟩ := C1Solution.exists_lam_lower_bound hB hB1 H
  have hlog : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => Real.log (S.lam p.1 p.2)) K :=
    hlam.log (fun p hp => ne_of_gt (hc.trans_le (hcl p hp)))
  have hslice : ContDiffOn ℝ 1
      (fun t => Real.log (S.lam t t)) (Icc 0 b) :=
    hlog.comp hpath hmap
  have hAC : AbsolutelyContinuousOnInterval
      (fun t => Real.log (S.lam t t)) 0 b :=
    (show ContDiffOn ℝ 1 (fun t => Real.log (S.lam t t))
      (uIcc 0 b) by
        simpa only [uIcc_of_le hb.1.le] using hslice).absolutelyContinuousOnInterval
  calc
    eVariationOn (fun t => Real.log (S.lam t t)) (Ioo 0 b) =
        ∫⁻ t in Ioo 0 b,
          ENNReal.ofReal |deriv (fun x => Real.log (S.lam x x)) t| :=
      (null_lintegral_eq_scalar_variation hb.1.le hAC
        (fun _ _ => rfl)).symm
    _ ≤ ∫⁻ t in Ioo 0 b, sliceOutgoingLogMajorant S t := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact axis_log_deriv_le_outgoing_majorant H hr hcenter hboot
        ⟨ht.1, ht.2.trans hb.2⟩
    _ ≤ ∫⁻ t in Ioo 0 1, sliceOutgoingLogMajorant S t :=
      lintegral_mono_set (fun t ht => ⟨ht.1, ht.2.trans hb.2⟩)
    _ ≤ _ := slice_outgoing_majorant_integral_le H hr hcenter hboot

end ChristodoulouBV

end
