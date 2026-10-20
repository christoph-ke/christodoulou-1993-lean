module

public import ChristodoulouBV.AreaEstimates.BasicEstimatesAmplitude
import all ChristodoulouBV.AreaEstimates.BasicEstimatesAmplitude
public import ChristodoulouBV.C1Solution.Rescaling
public import ChristodoulouBV.C1Solution.FrozenBridge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import all ChristodoulouBV.Uniqueness.RescalingBasic
import Mathlib.Tactic

/-!
# Unit-triangle scope of the amplitude estimates

The extraction library is phrased on a closed triangle strictly inside a
larger C¹ development. A positive dilation converts any smaller unit cutoff
of a C¹ solution on the closed unit triangle to that form. The bounds are
uniform in the cutoff and therefore hold on the source's unit domain.
-/

public section

open Set MeasureTheory
open scoped Topology Interval ENNReal

namespace ChristodoulouBV

open Uniqueness

private theorem unit_alpha_contDiffOn {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.alpha p.1 p.2)
      (closedCoordTriangle 0 1) := by
  have hK := C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
    (by norm_num : (0 : ℝ) < 1)
  have hθ : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.theta p.1 p.2)
      (closedCoordTriangle 0 1) := hK ▸ H.theta_c1
  have hlam : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.lam p.1 p.2)
      (closedCoordTriangle 0 1) := hK ▸ H.lam_c1
  have hphi : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2)
      (closedCoordTriangle 0 1) := hK ▸ H.phi_c1
  have heq : (fun p : ℝ × ℝ => S.alpha p.1 p.2) =
      (fun p => S.theta p.1 p.2 + S.lam p.1 p.2 * S.phi p.1 p.2) := by
    funext p
    simp only [Fields.theta]
    ring
  rw [heq]
  exact hθ.add (hlam.mul hphi)

/-- The source initial variation is finite under its exact C¹ premise on
the closure of the unit development. -/
theorem sourceD_ne_top_unit {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    sourceD S ≠ ⊤ := by
  let K := closedCoordTriangle 0 1
  have hmap : MapsTo (fun t : ℝ => ((0 : ℝ), t)) (Icc 0 1) K := by
    intro t ht
    simpa [K, closedCoordTriangle] using
      (show (0 : ℝ) ≤ 0 ∧ 0 ≤ t ∧ t ≤ 1 from
        ⟨le_refl (0 : ℝ), ht.1, ht.2⟩)
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => ((0 : ℝ), t)) (Icc 0 1) := by
    fun_prop
  have hα : ContDiffOn ℝ 1 (S.alpha 0) (Icc 0 1) :=
    (unit_alpha_contDiffOn H).comp hpair hmap
  have hAC : AbsolutelyContinuousOnInterval (S.alpha 0) 0 1 :=
    (show ContDiffOn ℝ 1 (S.alpha 0) (uIcc 0 1) by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hα).absolutelyContinuousOnInterval
  rw [sourceD, AbsolutelyContinuousOnInterval.eVariationOn_Ioo_eq_integral_abs_deriv
    (by norm_num : (0 : ℝ) ≤ 1) hAC]
  exact ENNReal.ofReal_ne_top

private theorem scaled_sourceD_le {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    (S : Fields) :
    sourceD (rescaledFields S 0 h) ≤ sourceD S := by
  have hvar := eVariationOn_affine_le (f := S.alpha 0)
    (s := Ioo (0 : ℝ) 1) (t := Ioo (0 : ℝ) 1)
    (a := 0) (h := h) hh (by
      intro v hv
      simpa only [affineCoordinate, zero_add] using
        (show h * v ∈ Ioo (0 : ℝ) 1 from
          ⟨mul_pos hh hv.1,
            (mul_lt_mul_of_pos_left hv.2 hh).trans (by simpa using hh1)⟩))
  simpa only [sourceD, rescaledFields, affineCoordinate, zero_add, mul_zero]
    using hvar

private theorem scaled_bootstrap {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    {S : Fields} (hboot : s4_bootstrap S) :
    s4_bootstrap (rescaledFields S 0 h) := by
  have hmap : ∀ p ∈ developmentWithInitialEdge 1,
      (h * p.1, h * p.2) ∈ developmentWithInitialEdge 1 := by
    intro p hp
    exact ⟨mul_nonneg hh.le hp.1,
      mul_lt_mul_of_pos_left hp.2.1 hh,
      (mul_lt_mul_of_pos_left hp.2.2 hh).trans (by simpa using hh1)⟩
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    simpa only [rescaledFields, affineCoordinate, zero_add] using
      hboot.1 (h * p.1, h * p.2) (hmap p hp)
  · intro p hp
    simpa only [rescaledFields, affineCoordinate, zero_add] using
      hboot.2.1 (h * p.1, h * p.2) (hmap p hp)
  · intro p hp
    have hratio := rescaled_mass_ratio S (a := 0) hh p.1 p.2
    simpa only [affineCoordinate, zero_add, hratio] using
      hboot.2.2 (h * p.1, h * p.2) (hmap p hp)

private theorem scaled_gauge {h : ℝ} (hh : 0 < h)
    {S : Fields} (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2) :
    ∀ v ∈ Ioo (0 : ℝ) (1 / h),
      (rescaledFields S 0 h).r 0 v = v / 2 := by
  intro v hv
  have hhv : h * v < 1 := by
    simpa only [mul_comm] using (lt_div_iff₀ hh).mp hv.2
  have harg : h * v ∈ Ioo (0 : ℝ) 1 :=
    ⟨mul_pos hh hv.1, hhv⟩
  simp only [rescaledFields, affineCoordinate, mul_zero, zero_add]
  rw [hr _ harg]
  field_simp [hh.ne']

private theorem scaled_real_bounds {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    sourceA (rescaledFields S 0 h) ≤ 2 * (sourceD S).toReal ∧
    sourceB (rescaledFields S 0 h) ≤ 4 * (sourceD S).toReal ∧
    sourceP (rescaledFields S 0 h) ≤ 6 * (sourceD S).toReal ∧
    sourceThetaAmp (rescaledFields S 0 h) ≤ 5 * (sourceD S).toReal ∧
    sourceZetaAmp (rescaledFields S 0 h) ≤ 8 * (sourceD S).toReal := by
  have hb : 1 < 1 / h := by
    apply (lt_div_iff₀ hh).mpr
    simpa only [one_mul] using hh1
  have Hh := C1Solution.rescaled_development_isC1Solution H hh
  have hrh := scaled_gauge hh hr
  have hcenterh : (rescaledFields S 0 h).phi 0 0 = 0 := by
    simpa only [rescaledFields, affineCoordinate, mul_zero, zero_add] using hcenter
  have hbooth := scaled_bootstrap hh hh1 hboot
  have hD := ENNReal.toReal_mono (sourceD_ne_top_unit H)
    (scaled_sourceD_le hh hh1 S)
  have hAmp := lemma4_2_real hb Hh hrh hcenterh hbooth
  have hTheta := eq4_3_real hb Hh hrh hcenterh hbooth
  rcases hAmp with ⟨hA, hB, hP⟩
  rcases hTheta with ⟨hT, hZ⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith only [hA, hB, hP, hT, hZ, hD]

private theorem unit_amp_bddAbove {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle 0 1)) :
    BddAbove {x : ℝ | ∃ p ∈ developmentWithInitialEdge 1, x = |f p|} := by
  have hcont : ContinuousOn (fun p => |f p|) (closedCoordTriangle 0 1) :=
    continuous_abs.comp_continuousOn hf
  obtain ⟨M, hM⟩ :=
    ((isCompact_closedCoordTriangle 0 1).image_of_continuousOn hcont).bddAbove
  refine ⟨M, ?_⟩
  rintro x ⟨p, hp, rfl⟩
  apply hM
  exact ⟨p, ⟨hp.1, hp.2.1.le, hp.2.2.le⟩, rfl⟩

private theorem unit_pointwise_amplitudes
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {p : ℝ × ℝ} (hp : p ∈ developmentWithInitialEdge 1) :
    |S.alpha p.1 p.2| ≤ 2 * (sourceD S).toReal ∧
    |S.beta p.1 p.2| ≤ 4 * (sourceD S).toReal ∧
    |S.phi p.1 p.2| ≤ 6 * (sourceD S).toReal ∧
    |S.theta p.1 p.2| ≤ 5 * (sourceD S).toReal ∧
    |S.zeta p.1 p.2| ≤ 8 * (sourceD S).toReal := by
  let h : ℝ := (p.2 + 1) / 2
  have hh : 0 < h := by dsimp [h]; linarith only [hp.1, hp.2.1]
  have hh1 : h < 1 := by dsimp [h]; linarith only [hp.2.2]
  have hph : p.2 < h := by dsimp [h]; linarith only [hp.2.2]
  let T := rescaledFields S 0 h
  have hb : 1 < 1 / h := by
    apply (lt_div_iff₀ hh).mpr
    simpa only [one_mul] using hh1
  have Hh : IsC1Solution (developmentWithInitialEdge (1 / h)) T :=
    C1Solution.rescaled_development_isC1Solution H hh
  have hp' : (p.1 / h, p.2 / h) ∈ developmentWithInitialEdge 1 := by
    exact ⟨div_nonneg hp.1 hh.le,
      (div_lt_div_iff_of_pos_right hh).mpr hp.2.1,
      (div_lt_iff₀ hh).mpr (by simpa only [one_mul] using hph)⟩
  have hfields :
      T.alpha (p.1 / h) (p.2 / h) = S.alpha p.1 p.2 ∧
      T.beta (p.1 / h) (p.2 / h) = S.beta p.1 p.2 ∧
      T.phi (p.1 / h) (p.2 / h) = S.phi p.1 p.2 ∧
      T.theta (p.1 / h) (p.2 / h) = S.theta p.1 p.2 ∧
      T.zeta (p.1 / h) (p.2 / h) = S.zeta p.1 p.2 := by
    simp only [T, rescaledFields, Fields.theta, Fields.zeta,
      affineCoordinate, zero_add]
    field_simp [hh.ne']
    simp
  have hC1 := C1Solution.five_fields_contDiffOn (by norm_num) hb Hh
  have hα : |T.alpha (p.1 / h) (p.2 / h)| ≤ sourceA T :=
    le_csSup (unit_amp_bddAbove
      (C1Solution.alpha_contDiffOn (by norm_num) hb Hh).continuousOn)
      ⟨(p.1 / h, p.2 / h), hp', rfl⟩
  have hβ : |T.beta (p.1 / h) (p.2 / h)| ≤ sourceB T :=
    le_csSup (unit_amp_bddAbove
      (C1Solution.beta_contDiffOn (by norm_num) hb Hh).continuousOn)
      ⟨(p.1 / h, p.2 / h), hp', rfl⟩
  have hφ : |T.phi (p.1 / h) (p.2 / h)| ≤ sourceP T :=
    le_csSup (unit_amp_bddAbove hC1.2.2.1.continuousOn)
      ⟨(p.1 / h, p.2 / h), hp', rfl⟩
  have hθ : |T.theta (p.1 / h) (p.2 / h)| ≤ sourceThetaAmp T :=
    le_csSup (unit_amp_bddAbove hC1.2.2.2.1.continuousOn)
      ⟨(p.1 / h, p.2 / h), hp', rfl⟩
  have hζ : |T.zeta (p.1 / h) (p.2 / h)| ≤ sourceZetaAmp T :=
    le_csSup (unit_amp_bddAbove hC1.2.2.2.2.continuousOn)
      ⟨(p.1 / h, p.2 / h), hp', rfl⟩
  obtain ⟨hA, hB, hP, hTheta, hZeta⟩ :=
    scaled_real_bounds hh hh1 H hr hcenter hboot
  rcases hfields with ⟨heqA, heqB, heqP, heqT, heqZ⟩
  rw [heqA] at hα
  rw [heqB] at hβ
  rw [heqP] at hφ
  rw [heqT] at hθ
  rw [heqZ] at hζ
  exact ⟨hα.trans hA, hβ.trans hB, hφ.trans hP,
    hθ.trans hTheta, hζ.trans hZeta⟩

private theorem unit_sSup_le {f : ℝ × ℝ → ℝ} {M : ℝ}
    (hpoint : ∀ p ∈ developmentWithInitialEdge 1, |f p| ≤ M) :
    sSup {x : ℝ | ∃ p ∈ developmentWithInitialEdge 1, x = |f p|} ≤ M := by
  apply csSup_le (by
    exact ⟨|f (0, (1 / 2 : ℝ))|,
      ⟨(0, (1 / 2 : ℝ)), by
        change 0 ≤ (0 : ℝ) ∧ 0 < 1 / 2 ∧ 1 / 2 < 1
        norm_num, rfl⟩⟩)
  rintro x ⟨p, hp, rfl⟩
  exact hpoint p hp

private theorem scaled_sourceA_le {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    sourceA (rescaledFields S 0 h) ≤ sourceA S := by
  have hSb := unit_amp_bddAbove (unit_alpha_contDiffOn H).continuousOn
  apply unit_sSup_le
  intro p hp
  have hmap : (h * p.1, h * p.2) ∈ developmentWithInitialEdge 1 :=
    ⟨mul_nonneg hh.le hp.1, mul_lt_mul_of_pos_left hp.2.1 hh,
      (mul_lt_mul_of_pos_left hp.2.2 hh).trans (by simpa using hh1)⟩
  have hval : |S.alpha (h * p.1) (h * p.2)| ≤ sourceA S :=
    le_csSup hSb ⟨(h * p.1, h * p.2), hmap, rfl⟩
  simpa only [rescaledFields, affineCoordinate, zero_add] using hval

/-- Equation (4.1) under the source's C¹ premise on the closed unit
triangle. -/
theorem eq4_1_unit {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    sourceP S ≤ 3 * sourceA S := by
  apply unit_sSup_le
  intro p hp
  let h : ℝ := (p.2 + 1) / 2
  have hh : 0 < h := by dsimp [h]; linarith only [hp.1, hp.2.1]
  have hh1 : h < 1 := by dsimp [h]; linarith only [hp.2.2]
  have hph : p.2 < h := by dsimp [h]; linarith only [hp.2.2]
  let T := rescaledFields S 0 h
  have hb : 1 < 1 / h := by
    apply (lt_div_iff₀ hh).mpr
    simpa only [one_mul] using hh1
  have Hh : IsC1Solution (developmentWithInitialEdge (1 / h)) T :=
    C1Solution.rescaled_development_isC1Solution H hh
  have hp' : (p.1 / h, p.2 / h) ∈ developmentWithInitialEdge 1 :=
    ⟨div_nonneg hp.1 hh.le,
      (div_lt_div_iff_of_pos_right hh).mpr hp.2.1,
      (div_lt_iff₀ hh).mpr (by simpa only [one_mul] using hph)⟩
  have hC1 := C1Solution.five_fields_contDiffOn (by norm_num) hb Hh
  have hP : |T.phi (p.1 / h) (p.2 / h)| ≤ sourceP T :=
    le_csSup (unit_amp_bddAbove hC1.2.2.1.continuousOn)
      ⟨(p.1 / h, p.2 / h), hp', rfl⟩
  have hval : T.phi (p.1 / h) (p.2 / h) = S.phi p.1 p.2 := by
    simp only [T, rescaledFields, affineCoordinate, zero_add]
    field_simp [hh.ne']
  rw [hval] at hP
  have hcenterh : T.phi 0 0 = 0 := by
    simpa only [T, rescaledFields, affineCoordinate, mul_zero, zero_add]
      using hcenter
  have hPA := eq4_1_larger hb Hh (scaled_gauge hh hr) hcenterh
    (scaled_bootstrap hh hh1 hboot)
  have hAS := scaled_sourceA_le hh hh1 H
  linarith only [hP, hPA, hAS]

/-- Lemma 4.2 with its exact C¹ solution premise on the closed unit
triangle. `D` is finite by `sourceD_ne_top_unit`. -/
theorem lemma4_2_unit {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    sourceA S ≤ 2 * (sourceD S).toReal ∧
      sourceB S ≤ 4 * (sourceD S).toReal ∧
        sourceP S ≤ 6 * (sourceD S).toReal := by
  refine ⟨?_, ?_, ?_⟩
  · exact unit_sSup_le (fun p hp =>
      (unit_pointwise_amplitudes H hr hcenter hboot hp).1)
  · exact unit_sSup_le (fun p hp =>
      (unit_pointwise_amplitudes H hr hcenter hboot hp).2.1)
  · exact unit_sSup_le (fun p hp =>
      (unit_pointwise_amplitudes H hr hcenter hboot hp).2.2.1)

/-- Equation (4.2a) under the exact unit-triangle C¹ premise. -/
theorem eq4_2a_unit {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    sourceA S ≤ 2 * (sourceD S).toReal :=
  (lemma4_2_unit H hr hcenter hboot).1

/-- Equation (4.2b) under the exact unit-triangle C¹ premise. -/
theorem eq4_2b_unit {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    sourceB S ≤ 2 * sourceA S ∧
      2 * sourceA S ≤ 4 * (sourceD S).toReal := by
  have hBA : sourceB S ≤ 2 * sourceA S := by
    apply unit_sSup_le
    intro p hp
    let h : ℝ := (p.2 + 1) / 2
    have hh : 0 < h := by dsimp [h]; linarith only [hp.1, hp.2.1]
    have hh1 : h < 1 := by dsimp [h]; linarith only [hp.2.2]
    have hph : p.2 < h := by dsimp [h]; linarith only [hp.2.2]
    let T := rescaledFields S 0 h
    have hb : 1 < 1 / h := by
      apply (lt_div_iff₀ hh).mpr
      simpa only [one_mul] using hh1
    have Hh : IsC1Solution (developmentWithInitialEdge (1 / h)) T :=
      C1Solution.rescaled_development_isC1Solution H hh
    have hp' : (p.1 / h, p.2 / h) ∈ developmentWithInitialEdge 1 :=
      ⟨div_nonneg hp.1 hh.le,
        (div_lt_div_iff_of_pos_right hh).mpr hp.2.1,
        (div_lt_iff₀ hh).mpr (by simpa only [one_mul] using hph)⟩
    have hB : |T.beta (p.1 / h) (p.2 / h)| ≤ sourceB T :=
      le_csSup (unit_amp_bddAbove
        (C1Solution.beta_contDiffOn (by norm_num) hb Hh).continuousOn)
        ⟨(p.1 / h, p.2 / h), hp', rfl⟩
    have hval : T.beta (p.1 / h) (p.2 / h) = S.beta p.1 p.2 := by
      simp only [T, rescaledFields, affineCoordinate, zero_add]
      field_simp [hh.ne']
    rw [hval] at hB
    have hcenterh : T.phi 0 0 = 0 := by
      simpa only [T, rescaledFields, affineCoordinate, mul_zero, zero_add]
        using hcenter
    have hB2A := (eq4_2b_real hb Hh (scaled_gauge hh hr) hcenterh
      (scaled_bootstrap hh hh1 hboot)).1
    have hAS := scaled_sourceA_le hh hh1 H
    linarith only [hB, hB2A, hAS]
  exact ⟨hBA, by
    have hA := eq4_2a_unit H hr hcenter hboot
    linarith only [hA]⟩

/-- Equation (4.3) with its exact C¹ solution premise on the closed unit
triangle. The numerical constants are universal. -/
theorem eq4_3_unit {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    sourceThetaAmp S ≤ 5 * (sourceD S).toReal ∧
      sourceZetaAmp S ≤ 8 * (sourceD S).toReal := by
  constructor
  · exact unit_sSup_le (fun p hp =>
      (unit_pointwise_amplitudes H hr hcenter hboot hp).2.2.2.1)
  · exact unit_sSup_le (fun p hp =>
      (unit_pointwise_amplitudes H hr hcenter hboot hp).2.2.2.2)

/-- Equation (4.1) on the source's closed unit triangle. -/
theorem eq4_1 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    sourceP S ≤ 3 * sourceA S :=
  eq4_1_unit H hr hcenter hboot

/-- Equation (4.2a) on the source's closed unit triangle. -/
theorem eq4_2a {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    sourceA S ≤ 2 * (sourceD S).toReal :=
  eq4_2a_unit H hr hcenter hboot

/-- Equation (4.2b) on the source's closed unit triangle. -/
theorem eq4_2b {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    sourceB S ≤ 2 * sourceA S ∧
      2 * sourceA S ≤ 4 * (sourceD S).toReal :=
  eq4_2b_unit H hr hcenter hboot

/-- Lemma 4.2 on the source's closed unit triangle. -/
theorem lemma4_2 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    sourceA S ≤ 2 * (sourceD S).toReal ∧
      sourceB S ≤ 4 * (sourceD S).toReal ∧
        sourceP S ≤ 6 * (sourceD S).toReal :=
  lemma4_2_unit H hr hcenter hboot

/-- Equation (4.3) on the source's closed unit triangle, with universal
numerical constants. -/
theorem eq4_3 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    sourceThetaAmp S ≤ 5 * (sourceD S).toReal ∧
      sourceZetaAmp S ≤ 8 * (sourceD S).toReal :=
  eq4_3_unit H hr hcenter hboot

end ChristodoulouBV

end
