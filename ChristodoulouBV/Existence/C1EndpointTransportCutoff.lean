module

public import ChristodoulouBV.Existence.C1EndpointResidualScale
public import ChristodoulouBV.Existence.C1EndpointDilation
public import ChristodoulouBV.Existence.C1EndpointShiftArea
public import ChristodoulouBV.AreaEstimates.LogTransportIntegral
public import ChristodoulouBV.AreaEstimates.FieldTransportOutgoing
public import ChristodoulouBV.Existence.E1ShiftTVScale
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Outgoing transport estimates on finite endpoint cutoffs

The Section 4 unit estimates are transferred to physical null coordinates.
The estimates keep the shrinking Jacobian area term.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace ChristodoulouBV

/-- The exact Section 4 bound for the complete outgoing logarithmic residual
on a finite cutoff, with the initial residual and shrinking wedge area. -/
theorem s6_finite_cutoff_log_residual_bound
    {alpha₀ : ℝ → ℝ} {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v ∈ Ioo (0 : ℝ) b,
      S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {a u : ℝ} (ha : 0 < a) (haB : a < B)
    (hu : u ∈ Ioo (0 : ℝ) a) :
    (∫⁻ v in Ioo u a,
      ENNReal.ofReal |sourceOutgoingLogResidual S u v|) ≤
      (∫⁻ v in Ioo u a,
        ENNReal.ofReal |sourceOutgoingLogResidual S 0 v|) +
        smoothAnalyticArea (sourcePhiBetaNuMap S)
          (Ioo (0 : ℝ) u ×ˢ Ioo u a) := by
  let T := Uniqueness.rescaledFields S 0 a
  obtain ⟨Q, HQ, hcenter, hrQ, hInv, _, _, _, _⟩ :=
    s6_centered_finite_cutoff_area_bounds hB hBb H hdata hD ha haB
  have hbootT :=
    (s6_no_first_exit_finite hB hBb H hdata hD a ha haB).1
  have hbootQ : s4_bootstrap Q := by
    rw [← hInv] at hbootT
    simpa only [s4_bootstrap, scalarShift] using hbootT
  have hT : IsC1Solution (developmentWithInitialEdge 1) T :=
    (s6_scale ha (haB.trans hBb) H hdata).1
  have huUnit : u / a ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hu.1 ha, (div_lt_one ha).mpr hu.2⟩
  have hQ := (eq4_12b_corrected HQ hrQ hcenter hbootQ huUnit).1
  let E := Ioo (0 : ℝ) (u / a) ×ˢ Ioo (u / a) 1
  have hEopen : IsOpen E := isOpen_Ioo.prod isOpen_Ioo
  have hEsub : E ⊆ openCoordTriangle 0 1 := by
    intro p hp
    simp only [openCoordTriangle, mem_ofPred_eq]
    exact ⟨hp.1.1, hp.1.2.trans hp.2.1, hp.2.2⟩
  have hLamQ : ∀ p ∈ E, Q.lam p.1 p.2 ≠ 0 := by
    intro p hp
    exact ne_of_gt (HQ.solution.lam_pos p
      ⟨hp.1.1.le, hp.1.2.trans hp.2.1, hp.2.2⟩)
  have hNuQ : ∀ p ∈ E, Q.nu p.1 p.2 ≠ 0 := by
    intro p hp
    exact ne_of_lt (lt_of_le_of_lt
      (sourceNu_le_neg_third HQ hbootQ (hEsub hp)) (by norm_num))
  have hAreaShift :=
    (s6_scalar_shift_four_areas Q
      ((Uniqueness.rescaledFields S 0 a).phi 0 0) hEopen hLamQ hNuQ).2.1
  change scalarShift Q ((Uniqueness.rescaledFields S 0 a).phi 0 0) = T at hInv
  rw [hInv] at hAreaShift
  have hAreaScale :=
    (s6_rescaled_outgoing_wedge_areas S ha hu.1 hu.2 hT hbootT).2
  have hArea : smoothAnalyticArea (sourcePhiBetaNuMap Q) E =
      smoothAnalyticArea (sourcePhiBetaNuMap S)
        (Ioo (0 : ℝ) u ×ˢ Ioo u a) := by
    rw [← hAreaShift]
    exact hAreaScale.symm
  have hR (w : ℝ) (hw : w ∈ Ioo (u / a) 1) :
      sourceOutgoingLogResidual Q (u / a) w =
        a * sourceOutgoingLogResidual S u (a * w) := by
    have haw : a * w ∈ Ioo u b := by
      constructor
      · have hw' := mul_lt_mul_of_pos_left hw.1 ha
        simpa only [mul_div_cancel₀ _ ha.ne'] using hw'
      · calc
          a * w < a := by simpa only [mul_one] using
            (mul_lt_mul_of_pos_left hw.2 ha)
          _ < b := haB.trans hBb
    have hp : (u, a * w) ∈ developmentWithInitialEdge b :=
      ⟨hu.1.le, haw.1, haw.2⟩
    have hr : S.r u (a * w) ≠ 0 :=
      ne_of_gt (H.solution.radius_pos _ hp)
    have hr' : S.r (a * (u / a)) (a * w) ≠ 0 := by
      simpa only [mul_div_cancel₀ _ ha.ne'] using hr
    calc
      sourceOutgoingLogResidual Q (u / a) w =
          sourceOutgoingLogResidual T (u / a) w := by
        rw [← hInv, sourceOutgoingLogResidual_scalarShift]
      _ = a * sourceOutgoingLogResidual S u (a * w) := by
        simpa only [T, mul_div_cancel₀ _ ha.ne'] using
          (sourceOutgoingLogResidual_rescaled S (u := u / a) (v := w) ha hr')
  have hI (w : ℝ) (hw : w ∈ Ioo (u / a) 1) :
      sourceOutgoingLogResidual Q 0 w =
        a * sourceOutgoingLogResidual S 0 (a * w) := by
    have haw : a * w ∈ Ioo (0 : ℝ) b := by
      constructor
      · exact mul_pos ha (huUnit.1.trans hw.1)
      · calc
          a * w < a := by simpa only [mul_one] using
            (mul_lt_mul_of_pos_left hw.2 ha)
          _ < b := haB.trans hBb
    have hr : S.r 0 (a * w) ≠ 0 :=
      ne_of_gt (H.solution.radius_pos (0, a * w) ⟨le_rfl, haw.1, haw.2⟩)
    calc
      sourceOutgoingLogResidual Q 0 w =
          sourceOutgoingLogResidual T 0 w := by
        rw [← hInv, sourceOutgoingLogResidual_scalarShift]
      _ = a * sourceOutgoingLogResidual S 0 (a * w) := by
        exact sourceOutgoingLogResidual_rescaled_initial S ha hr
  have hLinR :
      (∫⁻ w in Ioo (u / a) 1,
        ENNReal.ofReal |sourceOutgoingLogResidual Q (u / a) w|) =
      (∫⁻ w in Ioo u a,
        ENNReal.ofReal |sourceOutgoingLogResidual S u w|) := by
    calc
      _ = ∫⁻ w in Ioo (u / a) 1,
          ENNReal.ofReal a *
            ENNReal.ofReal |sourceOutgoingLogResidual S u (a * w)| := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
        rw [hR w hw, abs_mul, abs_of_pos ha,
          ENNReal.ofReal_mul ha.le]
      _ = _ := s6_lintegral_dilation
        (fun t => ENNReal.ofReal |sourceOutgoingLogResidual S u t|)
        (u := u) ha
  have hLinI :
      (∫⁻ w in Ioo (u / a) 1,
        ENNReal.ofReal |sourceOutgoingLogResidual Q 0 w|) =
      (∫⁻ w in Ioo u a,
        ENNReal.ofReal |sourceOutgoingLogResidual S 0 w|) := by
    calc
      _ = ∫⁻ w in Ioo (u / a) 1,
          ENNReal.ofReal a *
            ENNReal.ofReal |sourceOutgoingLogResidual S 0 (a * w)| := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
        rw [hI w hw, abs_mul, abs_of_pos ha,
          ENNReal.ofReal_mul ha.le]
      _ = _ := s6_lintegral_dilation
        (fun t => ENNReal.ofReal |sourceOutgoingLogResidual S 0 t|)
        (u := u) ha
  rw [hLinR, hLinI, hArea] at hQ
  exact hQ

/-- The exact Section 4 alpha-lambda residual bound on a physical finite
cutoff, with its initial variation and shrinking Jacobian wedge. -/
theorem s6_finite_cutoff_alpha_residual_bound
    {alpha₀ : ℝ → ℝ} {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v ∈ Ioo (0 : ℝ) b,
      S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {a u : ℝ} (ha : 0 < a) (haB : a < B)
    (hu : u ∈ Ioo (0 : ℝ) a) :
    (∫⁻ v in Ioo u a,
      ENNReal.ofReal |sourceOutgoingAlphaResidual S u v|) ≤
      eVariationOn (S.alpha 0) (Ioo u a) +
        smoothAnalyticArea (sourceLamPhiMap S)
          (Ioo (0 : ℝ) u ×ˢ Ioo u a) := by
  let T := Uniqueness.rescaledFields S 0 a
  obtain ⟨Q, HQ, hcenter, hrQ, hInv, _, _, _, _⟩ :=
    s6_centered_finite_cutoff_area_bounds hB hBb H hdata hD ha haB
  have hbootT :=
    (s6_no_first_exit_finite hB hBb H hdata hD a ha haB).1
  have hbootQ : s4_bootstrap Q := by
    rw [← hInv] at hbootT
    simpa only [s4_bootstrap, scalarShift] using hbootT
  have hT : IsC1Solution (developmentWithInitialEdge 1) T :=
    (s6_scale ha (haB.trans hBb) H hdata).1
  have huUnit : u / a ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hu.1 ha, (div_lt_one ha).mpr hu.2⟩
  have hQ := (eq4_4b HQ hrQ hcenter hbootQ huUnit).1
  let E := Ioo (0 : ℝ) (u / a) ×ˢ Ioo (u / a) 1
  have hEopen : IsOpen E := isOpen_Ioo.prod isOpen_Ioo
  have hEsub : E ⊆ openCoordTriangle 0 1 := by
    intro p hp
    simp only [openCoordTriangle, mem_ofPred_eq]
    exact ⟨hp.1.1, hp.1.2.trans hp.2.1, hp.2.2⟩
  have hLamQ : ∀ p ∈ E, Q.lam p.1 p.2 ≠ 0 := by
    intro p hp
    exact ne_of_gt (HQ.solution.lam_pos p
      ⟨hp.1.1.le, hp.1.2.trans hp.2.1, hp.2.2⟩)
  have hNuQ : ∀ p ∈ E, Q.nu p.1 p.2 ≠ 0 := by
    intro p hp
    exact ne_of_lt (lt_of_le_of_lt
      (sourceNu_le_neg_third HQ hbootQ (hEsub hp)) (by norm_num))
  have hAreaShift :=
    (s6_scalar_shift_four_areas Q
      ((Uniqueness.rescaledFields S 0 a).phi 0 0) hEopen hLamQ hNuQ).2.2.1
  change scalarShift Q ((Uniqueness.rescaledFields S 0 a).phi 0 0) = T at hInv
  rw [hInv] at hAreaShift
  have hAreaScale :=
    (s6_rescaled_outgoing_wedge_areas S ha hu.1 hu.2 hT hbootT).1
  have hArea : smoothAnalyticArea (sourceLamPhiMap Q) E =
      smoothAnalyticArea (sourceLamPhiMap S)
        (Ioo (0 : ℝ) u ×ˢ Ioo u a) := by
    rw [← hAreaShift]
    exact hAreaScale.symm
  have hVarShift : eVariationOn (Q.alpha 0) (Ioo (u / a) 1) =
      eVariationOn (T.alpha 0) (Ioo (u / a) 1) := by
    have hEq : EqOn (T.alpha 0)
        (fun w => Q.alpha 0 w +
          (Uniqueness.rescaledFields S 0 a).phi 0 0 / 2)
        (Ioo (u / a) 1) := by
      intro w hw
      have hw' : w ∈ Ioo (0 : ℝ) 1 := ⟨huUnit.1.trans hw.1, hw.2⟩
      rw [← hInv]
      change Q.alpha 0 w +
          (Uniqueness.rescaledFields S 0 a).phi 0 0 * Q.lam 0 w = _
      rw [initial_lam_eq_of_gauge HQ hrQ hw']
      ring
    rw [eVariationOn.congr hEq, eVariationOn_add_const_real]
  have hVarScale : eVariationOn (T.alpha 0) (Ioo (u / a) 1) =
      eVariationOn (S.alpha 0) (Ioo u a) := by
    simpa only [T, Uniqueness.rescaledFields,
      Uniqueness.affineCoordinate, mul_zero, zero_add,
      mul_div_cancel₀ _ ha.ne', mul_one] using
      (e1_variation_scale_Ioo (S.alpha 0)
        (a := u / a) (b := 1) ha)
  have hVar : eVariationOn (Q.alpha 0) (Ioo (u / a) 1) =
      eVariationOn (S.alpha 0) (Ioo u a) :=
    hVarShift.trans hVarScale
  obtain ⟨hLamK, _, _, hAlphaK, _⟩ := unit_field_contDiffOn HQ
  have hR (w : ℝ) (hw : w ∈ Ioo (u / a) 1) :
      sourceOutgoingAlphaResidual Q (u / a) w =
        a * sourceOutgoingAlphaResidual S u (a * w) := by
    have hdiffQAlpha : DifferentiableAt ℝ (Q.alpha (u / a)) w := by
      have hp := s4_differentiableAt_of_contDiffOn
        hAlphaK huUnit.1 hw.1 hw.2
      have hpath : DifferentiableAt ℝ
          (fun t : ℝ => ((u / a), t)) w := by fun_prop
      simpa only [Function.comp_def] using hp.comp w hpath
    have hdiffQLam : DifferentiableAt ℝ (Q.lam (u / a)) w := by
      have hp := s4_differentiableAt_of_contDiffOn
        hLamK huUnit.1 hw.1 hw.2
      have hpath : DifferentiableAt ℝ
          (fun t : ℝ => ((u / a), t)) w := by fun_prop
      simpa only [Function.comp_def] using hp.comp w hpath
    calc
      sourceOutgoingAlphaResidual Q (u / a) w =
          sourceOutgoingAlphaResidual T (u / a) w := by
        rw [← hInv]
        exact (sourceOutgoingAlphaResidual_scalarShift Q _ _ _
          hdiffQAlpha hdiffQLam).symm
      _ = a * sourceOutgoingAlphaResidual S u (a * w) := by
        simpa only [T, mul_div_cancel₀ _ ha.ne'] using
          (sourceOutgoingAlphaResidual_rescaled S (u := u / a)
            (v := w) ha)
  have hLinR :
      (∫⁻ w in Ioo (u / a) 1,
        ENNReal.ofReal |sourceOutgoingAlphaResidual Q (u / a) w|) =
      (∫⁻ w in Ioo u a,
        ENNReal.ofReal |sourceOutgoingAlphaResidual S u w|) := by
    calc
      _ = ∫⁻ w in Ioo (u / a) 1,
          ENNReal.ofReal a *
            ENNReal.ofReal |sourceOutgoingAlphaResidual S u (a * w)| := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
        rw [hR w hw, abs_mul, abs_of_pos ha,
          ENNReal.ofReal_mul ha.le]
      _ = _ := s6_lintegral_dilation
        (fun t => ENNReal.ofReal |sourceOutgoingAlphaResidual S u t|)
        (u := u) ha
  have hQ' :
      (∫⁻ w in Ioo (u / a) 1,
        ENNReal.ofReal |sourceOutgoingAlphaResidual Q (u / a) w|) ≤
      eVariationOn (Q.alpha 0) (Ioo (u / a) 1) +
        smoothAnalyticArea (sourceLamPhiMap Q) E := by
    simpa only [sourceOutgoingAlphaResidual, E] using hQ
  rw [hLinR, hVar, hArea] at hQ'
  exact hQ'

end ChristodoulouBV

end
