module

public import ChristodoulouBV.Existence.C1ContinuationSlice
import Mathlib.Tactic
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# The outgoing contraction in physical coordinates

Scalar centering and coordinate dilation preserve the slice contraction.
Only finite family members are used; no endpoint solution is assumed.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem unit_outgoing_slice_contDiff {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    ContDiffOn ℝ 1 (S.alpha u) (Icc u 1) ∧
      ContDiffOn ℝ 1 (S.lam u) (Icc u 1) := by
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc u 1)
      (closedCoordTriangle 0 1) := fun t ht => ⟨hu.1.le, ht.1, ht.2⟩
  have hpath : ContDiffOn ℝ 1 (fun t : ℝ => (u, t)) (Icc u 1) := by fun_prop
  exact ⟨(unit_field_contDiffOn H).2.2.2.1.comp hpath hmap,
    (unit_field_contDiffOn H).1.comp hpath hmap⟩

/-- The outgoing contraction holds for arbitrary scalar offsets. -/
theorem s6_outgoing_variation_le_residuals {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hboot : s4_bootstrap S)
    (hD : sourceD S ≤ s4Epsilon0) (hZ : sourceZ S ≤ s4Epsilon0)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u 1) +
      eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1) ≤
        6 * ((∫⁻ v in Ioo u 1, ENNReal.ofReal |sourceOutgoingAlphaResidual S u v|) +
          (∫⁻ v in Ioo u 1, ENNReal.ofReal |sourceOutgoingLogResidual S u v|)) := by
  let c := -S.phi 0 0
  let T := scalarShift S c
  have HT : IsC1Solution (developmentWithInitialEdge 1) T := H.scalarShift c
  have hrT : ∀ v ∈ Ioo (0 : ℝ) 1, T.r 0 v = v / 2 := hr
  have hcenter : T.phi 0 0 = 0 := by simp only [T, c, scalarShift, add_neg_cancel]
  have hbootT : s4_bootstrap T := hboot
  have hDT : sourceD T = sourceD S :=
    sourceD_scalarShift H hr c (by norm_num)
  have hZT : sourceZ T = sourceZ S := by
    simp only [T, sourceZ, sourceX_scalarShift, sourceY_scalarShift]
  have h := s6_outgoing_variation_le_residuals_unit HT hrT hcenter hbootT
    (hDT ▸ hD) (hZT ▸ hZ) hu
  have hq : EqOn (fun v => T.alpha u v / T.lam u v)
      (fun v => S.alpha u v / S.lam u v + c) (Ioo u 1) := by
    intro v hv
    exact scalarShift_alpha_div_lam S c u v
      (H.solution.lam_pos (u, v) ⟨hu.1.le, hv.1, hv.2⟩).ne'
  have hqv : eVariationOn (fun v => T.alpha u v / T.lam u v) (Ioo u 1) =
      eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u 1) := by
    rw [eVariationOn.congr hq, eVariationOn_add_const_real]
  have hA : (∫⁻ v in Ioo u 1, ENNReal.ofReal |sourceOutgoingAlphaResidual T u v|) =
      ∫⁻ v in Ioo u 1, ENNReal.ofReal |sourceOutgoingAlphaResidual S u v| := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    obtain ⟨hAlpha, hLam⟩ := unit_outgoing_slice_contDiff H hu
    have hdiff (f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (Icc u 1)) :
        DifferentiableAt ℝ f v :=
      (hf.differentiableOn (by norm_num) v ⟨hv.1.le, hv.2.le⟩).differentiableAt
        (Icc_mem_nhds hv.1 hv.2)
    rw [sourceOutgoingAlphaResidual_scalarShift S c u v
      (hdiff _ hAlpha) (hdiff _ hLam)]
  have hB : (∫⁻ v in Ioo u 1, ENNReal.ofReal |sourceOutgoingLogResidual T u v|) =
      ∫⁻ v in Ioo u 1, ENNReal.ofReal |sourceOutgoingLogResidual S u v| := by
    simp only [T, sourceOutgoingLogResidual_scalarShift]
  rw [hqv, hA, hB] at h
  exact h

/-- On a finite physical cutoff the outgoing quotient and logarithmic
variations are bounded by the two residual integrals, with coefficient six. -/
theorem s6_finite_cutoff_variation_le_residuals
    {alpha₀ : ℝ → ℝ} {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v ∈ Ioo (0 : ℝ) b,
      S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen)
    {a u : ℝ} (ha : 0 < a) (haB : a < B) (hu : u ∈ Ioo (0 : ℝ) a) :
    eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u a) +
      eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u a) ≤
        6 * ((∫⁻ v in Ioo u a, ENNReal.ofReal |sourceOutgoingAlphaResidual S u v|) +
          (∫⁻ v in Ioo u a, ENNReal.ofReal |sourceOutgoingLogResidual S u v|)) := by
  let T := Uniqueness.rescaledFields S 0 a
  obtain ⟨HT, htrace, hDT⟩ := s6_scale ha (haB.trans hBb) H hdata
  obtain ⟨hboot, hZ⟩ := s6_no_first_exit_finite hB hBb H hdata hD a ha haB
  have huUnit : u / a ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hu.1 ha, (div_lt_one ha).mpr hu.2⟩
  have h := s6_outgoing_variation_le_residuals HT
    (fun v hv => (htrace v hv).1) hboot
    (hDT.trans (hD.le.trans epsilonChosen_le_s4)) hZ huUnit
  have hq : eVariationOn (fun v => T.alpha (u / a) v / T.lam (u / a) v)
      (Ioo (u / a) 1) =
        eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u a) := by
    simpa only [T, Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
      zero_add, mul_div_cancel₀ _ ha.ne', mul_one] using
      (e1_variation_scale_Ioo (fun v => S.alpha u v / S.lam u v)
        (a := u / a) (b := 1) ha)
  have hl : eVariationOn (fun v => Real.log (T.lam (u / a) v))
      (Ioo (u / a) 1) =
        eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u a) := by
    simpa only [T, Uniqueness.rescaledFields, Uniqueness.affineCoordinate,
      zero_add, mul_div_cancel₀ _ ha.ne', mul_one] using
      (e1_variation_scale_Ioo (fun v => Real.log (S.lam u v))
        (a := u / a) (b := 1) ha)
  have hA : (∫⁻ v in Ioo (u / a) 1,
      ENNReal.ofReal |sourceOutgoingAlphaResidual T (u / a) v|) =
      ∫⁻ v in Ioo u a, ENNReal.ofReal |sourceOutgoingAlphaResidual S u v| := by
    calc
      _ = ∫⁻ v in Ioo (u / a) 1,
          ENNReal.ofReal a * ENNReal.ofReal |sourceOutgoingAlphaResidual S u (a * v)| := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
        rw [sourceOutgoingAlphaResidual_rescaled S ha,
          mul_div_cancel₀ _ ha.ne', abs_mul, abs_of_pos ha, ENNReal.ofReal_mul ha.le]
      _ = _ := s6_lintegral_dilation
        (fun t => ENNReal.ofReal |sourceOutgoingAlphaResidual S u t|) (u := u) ha
  have hLog : (∫⁻ v in Ioo (u / a) 1,
      ENNReal.ofReal |sourceOutgoingLogResidual T (u / a) v|) =
      ∫⁻ v in Ioo u a, ENNReal.ofReal |sourceOutgoingLogResidual S u v| := by
    calc
      _ = ∫⁻ v in Ioo (u / a) 1,
          ENNReal.ofReal a * ENNReal.ofReal |sourceOutgoingLogResidual S u (a * v)| := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
        have haw : a * v ∈ Ioo u b := by
          constructor
          · simpa only [mul_div_cancel₀ _ ha.ne'] using mul_lt_mul_of_pos_left hv.1 ha
          · have hawlt : a * v < a := by
              simpa only [mul_one] using mul_lt_mul_of_pos_left hv.2 ha
            exact hawlt.trans (haB.trans hBb)
        have hr : S.r (a * (u / a)) (a * v) ≠ 0 := by
          rw [mul_div_cancel₀ _ ha.ne']
          exact (H.solution.radius_pos (u, a * v) ⟨hu.1.le, haw.1, haw.2⟩).ne'
        rw [sourceOutgoingLogResidual_rescaled S ha hr,
          mul_div_cancel₀ _ ha.ne', abs_mul, abs_of_pos ha, ENNReal.ofReal_mul ha.le]
      _ = _ := s6_lintegral_dilation
        (fun t => ENNReal.ofReal |sourceOutgoingLogResidual S u t|) (u := u) ha
  rw [hq, hl, hA, hLog] at h
  exact h

end ChristodoulouBV

end
