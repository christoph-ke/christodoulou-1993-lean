module

public import ChristodoulouBV.AreaEstimates.LogTransportSliceCore
import Mathlib.Tactic

/-!
# Mass and quadratic correction integrals on null slices
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

/-- The outgoing mass coefficient contributes at most `15D X`. -/
theorem outgoing_mass_lintegral_le {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ t in Ioo u 1, ENNReal.ofReal (IsBVSolution.nuCoeff S u t)) ≤
      ENNReal.ofReal (15 * (sourceD S).toReal) * sourceX S := by
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
  have hVar : eVariationOn (S.phi u) (Ioc u b) ≤ sourceX S := by
    rw [hBV.outgoing_scalar_variation_Ioc_eq_Ioo hU]
    calc
      eVariationOn (S.phi u) (Ioo u b) ≤
          eVariationOn (S.phi u) (Ioo u 1) :=
        eVariationOn.mono (S.phi u) (fun t ht => ⟨ht.1, ht.2.trans hb.2⟩)
      _ = ∫⁻ t in Ioo u 1,
          ENNReal.ofReal (|S.theta u t| / S.r u t) :=
        source_outgoing_phi_variation_eq_weight H hu
      _ ≤ sourceX S := le_iSup_of_le u (le_iSup_of_le hu le_rfl)
  have hReal := hBV.eq3_1a_nuCoeff hU hboundRay
  have hENN := ENNReal.ofReal_le_ofReal hReal
  rw [ENNReal.ofReal_mul hMnonneg] at hENN
  rw [hCast]
  exact hENN.trans (mul_le_mul_of_nonneg_left
    (ENNReal.ofReal_toReal_le.trans hVar) bot_le)

/-- The incoming signed mass coefficient contributes at most `24D Y`. -/
theorem incoming_mass_lintegral_le {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ u in Ioo 0 v,
      ENNReal.ofReal (-IsBVSolution.incomingCoeff S u v)) ≤
      ENNReal.ofReal (24 * (sourceD S).toReal) * sourceY S := by
  let M : ℝ := 24 * (sourceD S).toReal
  have hMnonneg : 0 ≤ M := by dsimp [M]; positivity
  have hBV : IsBVSolution (developmentWithInitialEdge 1) S :=
    IsC1Solution.isBVSolution_development (by norm_num) H
  have haccess : ∀ u ∈ Ico 0 v, (u, v) ∈ developmentWithInitialEdge 1 := by
    intro u hu
    exact ⟨hu.1, hu.2, hv.2⟩
  have hbound : ∀ u ∈ Ico 0 v, |S.zeta u v / S.nu u v| ≤ M := by
    intro u hu
    have hp := haccess u hu
    have hzeta := (eq4_3_pointwise H hr hcenter hboot hp).2
    have hnu : S.nu u v ≤ -(1 / 3 : ℝ) :=
      hBV.nu_le_neg_lower (by norm_num) hboot.1 hp
    have hnuNeg : S.nu u v < 0 := by linarith
    have hnuAbs : (1 / 3 : ℝ) ≤ |S.nu u v| := by
      rw [abs_of_neg hnuNeg]
      linarith only [hnu]
    have hD : 0 ≤ (sourceD S).toReal := ENNReal.toReal_nonneg
    rw [abs_div]
    apply (div_le_iff₀ (by linarith only [hnuAbs])).2
    have hm := mul_le_mul_of_nonneg_left hnuAbs hD
    dsimp [M]
    nlinarith only [hzeta, hm]
  have hIoc : IntegrableOn (fun u => IsBVSolution.incomingCoeff S u v)
      (Ioc 0 v) := hBV.incomingCoeff_integrable_axis hv.1 haccess hbound
  have hInt : IntegrableOn (fun u => -IsBVSolution.incomingCoeff S u v)
      (Ioo 0 v) := hIoc.neg.mono_set Ioo_subset_Ioc_self
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo 0 v)]
      (fun u => -IsBVSolution.incomingCoeff S u v) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro u hu
    exact neg_nonneg.mpr (hBV.incomingCoeff_nonpos (haccess u ⟨hu.1.le, hu.2⟩))
  have hCast :
      (∫⁻ u in Ioo 0 v,
        ENNReal.ofReal (-IsBVSolution.incomingCoeff S u v)) =
        ENNReal.ofReal (-(∫ u in (0 : ℝ)..v,
          IsBVSolution.incomingCoeff S u v)) := by
    rw [← intervalIntegral.integral_neg,
      intervalIntegral.integral_of_le hv.1.le, integral_Ioc_eq_integral_Ioo]
    exact (ofReal_integral_eq_lintegral_ofReal hInt hnonneg).symm
  have hVar : eVariationOn (fun u => S.phi u v) (Ico 0 v) ≤ sourceY S := by
    rw [hBV.incoming_scalar_variation_Ico_eq_Ioo hv.1 haccess]
    calc
      eVariationOn (fun u => S.phi u v) (Ioo 0 v) =
          ∫⁻ u in Ioo 0 v, ENNReal.ofReal (|S.zeta u v| / S.r u v) :=
        source_incoming_phi_variation_eq_weight H hv
      _ ≤ sourceY S := le_iSup_of_le v (le_iSup_of_le hv le_rfl)
  have hReal := hBV.eq3_1b hv.1 haccess hbound
  change -(∫ u in (0 : ℝ)..v, IsBVSolution.incomingCoeff S u v) ≤
    M * (eVariationOn (fun u => S.phi u v) (Ico 0 v)).toReal at hReal
  have hENN := ENNReal.ofReal_le_ofReal hReal
  rw [ENNReal.ofReal_mul hMnonneg] at hENN
  rw [hCast]
  exact hENN.trans (mul_le_mul_of_nonneg_left
    (ENNReal.ofReal_toReal_le.trans hVar) bot_le)

/-- The outgoing quadratic correction contributes at most `39D X`. -/
theorem outgoing_correction_lintegral_le {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ v in Ioo u 1, ENNReal.ofReal |sourceLogCorrection S u v|) ≤
      ENNReal.ofReal (39 * (sourceD S).toReal) * sourceX S := by
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
    _ ≤ ENNReal.ofReal M * sourceX S := by
      exact mul_le_mul_of_nonneg_left
        (le_iSup_of_le u (le_iSup_of_le hu le_rfl)) bot_le

/-- The incoming quadratic correction contributes at most `39D Y`. -/
theorem incoming_correction_lintegral_le {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ u in Ioo 0 v, ENNReal.ofReal |sourceLogCorrectionStar S u v|) ≤
      ENNReal.ofReal (39 * (sourceD S).toReal) * sourceY S := by
  let M : ℝ := 39 * (sourceD S).toReal
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hpoint (u : ℝ) (hu : u ∈ Ioo 0 v) :
      ENNReal.ofReal |sourceLogCorrectionStar S u v| ≤
        ENNReal.ofReal M *
          ENNReal.ofReal (|S.zeta u v| / S.r u v) := by
    have hp : (u, v) ∈ developmentWithInitialEdge 1 :=
      ⟨hu.1.le, hu.2, hv.2⟩
    have h := ENNReal.ofReal_le_ofReal
      (source_log_correction_star_bound H hr hcenter hboot hp)
    rwa [ENNReal.ofReal_mul hM] at h
  calc
    (∫⁻ u in Ioo 0 v, ENNReal.ofReal |sourceLogCorrectionStar S u v|) ≤
        ∫⁻ u in Ioo 0 v,
          ENNReal.ofReal M * ENNReal.ofReal (|S.zeta u v| / S.r u v) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact hpoint u hu
    _ = ENNReal.ofReal M *
          (∫⁻ u in Ioo 0 v,
            ENNReal.ofReal (|S.zeta u v| / S.r u v)) := by
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal M * sourceY S := by
      exact mul_le_mul_of_nonneg_left
        (le_iSup_of_le v (le_iSup_of_le hv le_rfl)) bot_le


end ChristodoulouBV

end
