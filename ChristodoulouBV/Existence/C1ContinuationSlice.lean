module

public import ChristodoulouBV.Existence.C1Endpoint
public import ChristodoulouBV.AreaEstimates.LogTransportSliceMass
import all ChristodoulouBV.AreaEstimates.SmallDataQuotientVariation
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Slice estimates for C¹ continuation

The integral corrections are controlled by variation on the same outgoing
slice. Keeping this dependence is necessary for the terminal contraction.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

/-- The outgoing mass coefficient is controlled by variation on the same slice.
This controls the mass term in the outgoing logarithmic estimate. -/
theorem s6_outgoing_mass_lintegral_le {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ t in Ioo u 1, ENNReal.ofReal (IsBVSolution.nuCoeff S u t)) ≤
      ENNReal.ofReal (15 * (sourceD S).toReal) *
        eVariationOn (S.phi u) (Ioo u 1) := by
  let M : ℝ := 15 * (sourceD S).toReal
  have hMnonneg : 0 ≤ M := by dsimp [M]; positivity
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have hbound : ∀ p ∈ developmentWithInitialEdge 1,
      |S.theta p.1 p.2 / S.lam p.1 p.2| ≤ M := by
    intro p hp
    exact source_theta_div_lam_le_sourceD H hr hcenter hboot hp
  apply lintegral_Ioo_unit_le_of_cutoffs hu.2
  intro b hb
  have hU : (u, b) ∈ developmentWithInitialEdge 1 :=
    ⟨hu.1.le, hb.1, hb.2⟩
  have hboundRay : ∀ t ∈ Ioc u b,
      |S.theta u t / S.lam u t| ≤ M := by
    intro t ht
    exact hbound (u, t)
      (hBV.solution.development.outgoing_mem hU ht.1 ht.2)
  have hIoc : IntegrableOn (IsBVSolution.nuCoeff S u) (Ioc u b) :=
    hBV.nu_coeff_integrable_axis hU hboundRay
  have hInt : IntegrableOn (IsBVSolution.nuCoeff S u) (Ioo u b) :=
    hIoc.mono_set Ioo_subset_Ioc_self
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo u b)]
      IsBVSolution.nuCoeff S u := by
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    exact IsBVSolution.nu_coeff_nonneg hBV.solution.development hBV
      (hBV.solution.development.outgoing_mem hU ht.1 ht.2.le)
  have hCast :
      (∫⁻ t in Ioo u b, ENNReal.ofReal (IsBVSolution.nuCoeff S u t)) =
        ENNReal.ofReal (∫ t in u..b, IsBVSolution.nuCoeff S u t) := by
    rw [intervalIntegral.integral_of_le hb.1.le, integral_Ioc_eq_integral_Ioo]
    exact (ofReal_integral_eq_lintegral_ofReal hInt hnonneg).symm
  have hVar : eVariationOn (S.phi u) (Ioc u b) ≤
      eVariationOn (S.phi u) (Ioo u 1) := by
    rw [hBV.outgoing_scalar_variation_Ioc_eq_Ioo hU]
    exact eVariationOn.mono (S.phi u) (fun t ht => ⟨ht.1, ht.2.trans hb.2⟩)
  have hReal := hBV.eq3_1a_nuCoeff hU hboundRay
  have hENN := ENNReal.ofReal_le_ofReal hReal
  rw [ENNReal.ofReal_mul hMnonneg] at hENN
  rw [hCast]
  exact hENN.trans (mul_le_mul_of_nonneg_left
    (ENNReal.ofReal_toReal_le.trans hVar) bot_le)

/-- The outgoing correction is controlled by variation on the same slice.
This controls the quadratic term in the outgoing logarithmic estimate. -/
theorem s6_outgoing_correction_lintegral_le {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ v in Ioo u 1, ENNReal.ofReal |sourceLogCorrection S u v|) ≤
      ENNReal.ofReal (39 * (sourceD S).toReal) * eVariationOn (S.phi u) (Ioo u 1) := by
  let M : ℝ := 39 * (sourceD S).toReal
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hpoint (v : ℝ) (hv : v ∈ Ioo u 1) :
      ENNReal.ofReal |sourceLogCorrection S u v| ≤
        ENNReal.ofReal M *
          ENNReal.ofReal (|S.theta u v| / S.r u v) := by
    have hp : (u, v) ∈ developmentWithInitialEdge 1 :=
      ⟨hu.1.le, hv.1, hv.2⟩
    have h := ENNReal.ofReal_le_ofReal
      (source_log_correction_bound H hr hcenter hboot hp)
    rwa [ENNReal.ofReal_mul hM] at h
  calc
    (∫⁻ v in Ioo u 1, ENNReal.ofReal |sourceLogCorrection S u v|) ≤
        ∫⁻ v in Ioo u 1,
          ENNReal.ofReal M * ENNReal.ofReal (|S.theta u v| / S.r u v) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      exact hpoint v hv
    _ = ENNReal.ofReal M *
          (∫⁻ v in Ioo u 1,
            ENNReal.ofReal (|S.theta u v| / S.r u v)) := by
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal M * eVariationOn (S.phi u) (Ioo u 1) := by
      rw [source_outgoing_phi_variation_eq_weight H hu]

/-- Both outgoing integral corrections are bounded by the outgoing scalar
quotient variation, with universal coefficients. -/
theorem s6_f_mu {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ t in Ioo u 1, ENNReal.ofReal (IsBVSolution.nuCoeff S u t)) ≤
        ENNReal.ofReal (15 * (sourceD S).toReal) *
          eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u 1) ∧
    (∫⁻ v in Ioo u 1, ENNReal.ofReal |sourceLogCorrection S u v|) ≤
        ENNReal.ofReal (39 * (sourceD S).toReal) *
          eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u 1) := by
  have hphi : eVariationOn (S.phi u) (Ioo u 1) ≤
      eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u 1) := by
    rw [source_outgoing_phi_variation_eq_weight H hu]
    exact (lemma4_1 H).1 u hu
  exact ⟨(s6_outgoing_mass_lintegral_le H hr hcenter hboot hu).trans (by gcongr),
    (s6_outgoing_correction_lintegral_le H hr hcenter hboot hu).trans (by gcongr)⟩

private theorem quotient_variation_le_slice_residual {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u 1) ≤
      3 * (∫⁻ v in Ioo u 1, ENNReal.ofReal |sourceOutgoingAlphaResidual S u v|) +
        36 * sourceD S *
          eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1) := by
  have hfields := unit_field_contDiffOn H
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc u 1)
      (closedCoordTriangle 0 1) := fun t ht => ⟨hu.1.le, ht.1, ht.2⟩
  have hpath : ContDiffOn ℝ 1 (fun t : ℝ => (u, t)) (Icc u 1) := by fun_prop
  have hAlpha : ContDiffOn ℝ 1 (S.alpha u) (Icc u 1) :=
    hfields.2.2.2.1.comp hpath hmap
  have hLam : ContDiffOn ℝ 1 (S.lam u) (Icc u 1) :=
    hfields.1.comp hpath hmap
  have hAC (f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (Icc u 1)) :
      AbsolutelyContinuousOnInterval f u 1 :=
    (show ContDiffOn ℝ 1 f (uIcc u 1) by
      simpa only [uIcc_of_le hu.2.le] using hf).absolutelyContinuousOnInterval
  have hP (t : ℝ) (ht : t ∈ Ioo u 1) :
      |S.phi u t| ≤ 6 * (sourceD S).toReal :=
    (abs_phi_closed_le_sourceP H (p := (u, t)) ⟨hu.1.le, ht.1.le, ht.2.le⟩).trans
      (lemma4_2 H hr hcenter hboot).2.2
  have hAlphaVar := variation_le_residual_add hu.2.le
    (hAC _ hAlpha) (hAC _ hLam) (by positivity) hP
  change eVariationOn (S.alpha u) (Ioo u 1) ≤
    (∫⁻ v in Ioo u 1, ENNReal.ofReal |sourceOutgoingAlphaResidual S u v|) +
      ENNReal.ofReal (6 * (sourceD S).toReal) *
        eVariationOn (S.lam u) (Ioo u 1) at hAlphaVar
  have hDof : ENNReal.ofReal (sourceD S).toReal = sourceD S :=
    ENNReal.ofReal_toReal (sourceD_ne_top_unit H)
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6),
    ENNReal.ofReal_ofNat, hDof] at hAlphaVar
  have hNum : ∀ v ∈ Ioo u 1, ‖S.alpha u v‖ₑ ≤ 2 * sourceD S :=
    fun v hv => (s4_alpha_beta_enorm_le_sourceD H hr hcenter hboot).1
      (u, v) ⟨hu.1.le, hv.1, hv.2⟩
  have hDen : ∀ v ∈ Ioo u 1, (1 / 3 : ℝ) ≤ S.lam u v :=
    fun v hv => hboot.1 (u, v) ⟨hu.1.le, hv.1, hv.2⟩
  have hLamVar : eVariationOn (S.lam u) (Ioo u 1) ≤
      eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1) := by
    apply s4_variation_le_log_of_pos_le_one
    · intro v hv
      exact H.solution.lam_pos (u, v) ⟨hu.1.le, hv.1, hv.2⟩
    · intro v hv
      exact (Uniqueness.lam_le_half_of_initial_gauge H hr hu.1.le hv.1 hv.2).trans
        (by norm_num)
  calc
    _ ≤ 9 * (2 * sourceD S) * eVariationOn (S.lam u) (Ioo u 1) +
        3 * eVariationOn (S.alpha u) (Ioo u 1) := quotient_variation_le hNum hDen
    _ ≤ 9 * (2 * sourceD S) * eVariationOn (S.lam u) (Ioo u 1) +
        3 * ((∫⁻ v in Ioo u 1, ENNReal.ofReal |sourceOutgoingAlphaResidual S u v|) +
          (6 * sourceD S) * eVariationOn (S.lam u) (Ioo u 1)) := by gcongr
    _ = 3 * (∫⁻ v in Ioo u 1, ENNReal.ofReal |sourceOutgoingAlphaResidual S u v|) +
        36 * sourceD S * eVariationOn (S.lam u) (Ioo u 1) := by ring
    _ ≤ _ := by gcongr

/-- The two outgoing variations are controlled by the residuals on that
same slice. The constant is universal and independent of scalar offsets. -/
theorem s6_outgoing_variation_le_residuals_unit {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    (hD : sourceD S ≤ s4Epsilon0) (hZ : sourceZ S ≤ s4Epsilon0)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u 1) +
      eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1) ≤
        6 * ((∫⁻ v in Ioo u 1, ENNReal.ofReal |sourceOutgoingAlphaResidual S u v|) +
          (∫⁻ v in Ioo u 1, ENNReal.ofReal |sourceOutgoingLogResidual S u v|)) := by
  let Q := eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u 1)
  let L := eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1)
  let A := ∫⁻ v in Ioo u 1, ENNReal.ofReal |sourceOutgoingAlphaResidual S u v|
  let B := ∫⁻ v in Ioo u 1, ENNReal.ofReal |sourceOutgoingLogResidual S u v|
  have hDfinite := sourceD_ne_top_unit H
  have hDof : ENNReal.ofReal (sourceD S).toReal = sourceD S :=
    ENNReal.ofReal_toReal hDfinite
  have hLog : L ≤ B + 54 * sourceD S * Q := by
    obtain ⟨hM, hC⟩ := s6_f_mu H hr hcenter hboot hu
    have h := outgoing_log_variation_le_components H hr hcenter hboot hu
    calc
      L ≤ B + (ENNReal.ofReal (15 * (sourceD S).toReal) * Q) +
          (ENNReal.ofReal (39 * (sourceD S).toReal) * Q) :=
        h.trans (add_le_add (add_le_add le_rfl hM) hC)
      _ = B + 54 * sourceD S * Q := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 15),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 39), hDof]
        norm_num only [ENNReal.ofReal_ofNat]
        ring
  have hQuot : Q ≤ 3 * A + 36 * sourceD S * L :=
    quotient_variation_le_slice_residual H hr hcenter hboot hu
  have h54 : (54 : ℝ≥0∞) * sourceD S ≤ 1 / 2 := by
    calc
      54 * sourceD S ≤ 54 * s4Epsilon0 := by gcongr
      _ ≤ 1 / 2 := by
        apply (ENNReal.toReal_le_toReal (by unfold s4Epsilon0; finiteness) (by finiteness)).mp
        norm_num [s4Epsilon0, ENNReal.toReal_mul, ENNReal.toReal_div]
  have h36 : (36 : ℝ≥0∞) * sourceD S ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right (by norm_num : (36 : ℝ≥0∞) ≤ 54) bot_le).trans h54
  have hQ : Q ≤ 3 * A + (1 / 2) * L := hQuot.trans (by gcongr)
  have hL : L ≤ B + (1 / 2) * Q := hLog.trans (by gcongr)
  have hTV := (e1_centered_three_term_tv_unit H hr hcenter hboot hD hZ).1
    u ⟨hu.1.le, hu.2⟩
  have hQfinite : Q ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((le_add_right (le_add_right (le_refl Q))).trans hTV)
  have hLfinite : L ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((le_add_left (le_refl L)).trans hTV)
  by_cases hAB : A + B = ∞
  · change Q + L ≤ 6 * (A + B)
    simp only [hAB, ENNReal.mul_top (by norm_num : (6 : ℝ≥0∞) ≠ 0), le_top]
  have hAf : A ≠ ∞ := ne_top_of_le_ne_top hAB (le_add_right le_rfl)
  have hBf : B ≠ ∞ := ne_top_of_le_ne_top hAB (le_add_left le_rfl)
  have hQr := (ENNReal.toReal_le_toReal hQfinite (by finiteness)).mpr hQ
  have hLr := (ENNReal.toReal_le_toReal hLfinite (by finiteness)).mpr hL
  rw [ENNReal.toReal_add (a := 3 * A) (b := 1 / 2 * L)
    (by finiteness) (by finiteness)] at hQr
  rw [ENNReal.toReal_add hBf (b := 1 / 2 * Q) (by finiteness)] at hLr
  norm_num only [ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, ENNReal.toReal_one] at hQr hLr
  change Q + L ≤ 6 * (A + B)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_add hQfinite hLfinite, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_add hAf hBf]
  nlinarith only [hQr, hLr, ENNReal.toReal_nonneg (a := B)]

end ChristodoulouBV

end
