module

public import ChristodoulouBV.AreaEstimates.FieldTransportIncomingIntegral
import ChristodoulouBV.AreaEstimates.FieldTransportAxis
import ChristodoulouBV.AreaEstimates.BasicEstimatesVariationCore
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Tactic

/-!
# Variation bounds from field transport residuals

The residual inequalities become total-variation inequalities by absolute
continuity of the characteristic traces.
-/

public section

open Set MeasureTheory Filter
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

/-- The elementary total-variation estimate for a derivative residual
`f' − g' φ`, allowing infinite variation. -/
theorem variation_le_residual_add {a b P : ℝ} (hab : a ≤ b)
    {f g phi : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hP : 0 ≤ P) (hphi : ∀ t ∈ Ioo a b, |phi t| ≤ P) :
    eVariationOn f (Ioo a b) ≤
      (∫⁻ t in Ioo a b,
        ENNReal.ofReal |deriv f t - deriv g t * phi t|) +
      ENNReal.ofReal P * eVariationOn g (Ioo a b) := by
  let C : ℝ≥0∞ := ENNReal.ofReal P
  let A : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal |deriv f t|
  let R : ℝ → ℝ≥0∞ := fun t =>
    ENNReal.ofReal |deriv f t - deriv g t * phi t|
  let G : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal |deriv g t|
  have hpoint (t : ℝ) (ht : t ∈ Ioo a b) : A t ≤ R t + C * G t := by
    have hreal : |deriv f t| ≤
        |deriv f t - deriv g t * phi t| + P * |deriv g t| := by
      calc
        |deriv f t| =
            |(deriv f t - deriv g t * phi t) + deriv g t * phi t| := by
          congr 1
          ring
        _ ≤ |deriv f t - deriv g t * phi t| +
            |deriv g t * phi t| := abs_add_le _ _
        _ = |deriv f t - deriv g t * phi t| +
            |deriv g t| * |phi t| := by rw [abs_mul]
        _ ≤ |deriv f t - deriv g t * phi t| +
            |deriv g t| * P := by gcongr; exact hphi t ht
        _ = _ := by ring
    have h := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_add (abs_nonneg _)
      (mul_nonneg hP (abs_nonneg _)), ENNReal.ofReal_mul hP] at h
    exact h
  have hGmeas : AEMeasurable G (volume.restrict (Ioo a b)) :=
    (measurable_deriv g).abs.ennreal_ofReal.aemeasurable
  have hCGmeas : AEMeasurable (fun t => C * G t)
      (volume.restrict (Ioo a b)) :=
    aemeasurable_const.mul hGmeas
  have hVarF := (null_lintegral_eq_scalar_variation hab hf
    (fun _ _ => rfl)).symm
  have hVarG := (null_lintegral_eq_scalar_variation hab hg
    (fun _ _ => rfl)).symm
  calc
    eVariationOn f (Ioo a b) = ∫⁻ t in Ioo a b, A t := hVarF
    _ ≤ ∫⁻ t in Ioo a b, R t + C * G t := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hpoint t ht
    _ = (∫⁻ t in Ioo a b, R t) +
        ∫⁻ t in Ioo a b, C * G t := by
      rw [lintegral_add_right' _ hCGmeas]
    _ = (∫⁻ t in Ioo a b, R t) +
        C * (∫⁻ t in Ioo a b, G t) := by
      rw [lintegral_const_mul'' C hGmeas]
    _ = _ := by rw [← hVarG]

/-- Equation (4.4c): uniform outgoing variation of `α` in terms of the
initial variation, outgoing `λ` variation, and analytic area. -/
theorem eq4_4c {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    (⨆ u ∈ Ioo (0 : ℝ) 1,
      eVariationOn (S.alpha u) (Ioo u 1)) ≤
      sourceD S + ENNReal.ofReal (sourceP S) *
        (⨆ u ∈ Ioo (0 : ℝ) 1,
          eVariationOn (S.lam u) (Ioo u 1)) +
      smoothAnalyticArea (sourceLamPhiMap S) (openCoordTriangle 0 1) := by
  have hPnn : 0 ≤ sourceP S :=
    (abs_nonneg (S.phi (1 / 2) (1 / 2))).trans
      (abs_phi_axis_le_sourceP H (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1))
  obtain ⟨hlam, _, _, halpha, _⟩ := unit_field_contDiffOn H
  apply iSup_le
  intro u
  apply iSup_le
  intro hu
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc u 1)
      (closedCoordTriangle 0 1) := by
    intro t ht
    exact ⟨hu.1.le, ht.1, ht.2⟩
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => (u, t)) (Icc u 1) := by
    fun_prop
  have hAlpha : ContDiffOn ℝ 1 (S.alpha u) (Icc u 1) :=
    halpha.comp hpair hmap
  have hLam : ContDiffOn ℝ 1 (S.lam u) (Icc u 1) :=
    hlam.comp hpair hmap
  have hAC (f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (Icc u 1)) :
      AbsolutelyContinuousOnInterval f u 1 :=
    (show ContDiffOn ℝ 1 f (uIcc u 1) by
      simpa only [uIcc_of_le hu.2.le] using hf).absolutelyContinuousOnInterval
  have hPhi (t : ℝ) (ht : t ∈ Ioo u 1) :
      |S.phi u t| ≤ sourceP S :=
    abs_phi_closed_le_sourceP H (p := (u, t))
      ⟨hu.1.le, ht.1.le, ht.2.le⟩
  have hvar := variation_le_residual_add hu.2.le
    (hAC _ hAlpha) (hAC _ hLam) hPnn hPhi
  have hres := (eq4_4b H hr hcenter hboot hu).2
  have hsup : eVariationOn (S.lam u) (Ioo u 1) ≤
      ⨆ w ∈ Ioo (0 : ℝ) 1, eVariationOn (S.lam w) (Ioo w 1) :=
    le_iSup_of_le u (le_iSup_of_le hu le_rfl)
  calc
    eVariationOn (S.alpha u) (Ioo u 1) ≤
        (∫⁻ t in Ioo u 1,
          ENNReal.ofReal |deriv (S.alpha u) t -
            deriv (S.lam u) t * S.phi u t|) +
          ENNReal.ofReal (sourceP S) *
            eVariationOn (S.lam u) (Ioo u 1) := hvar
    _ ≤ sourceD S + smoothAnalyticArea (sourceLamPhiMap S)
          (openCoordTriangle 0 1) +
        ENNReal.ofReal (sourceP S) * eVariationOn (S.lam u) (Ioo u 1) :=
      add_le_add_left hres _
    _ ≤ sourceD S + smoothAnalyticArea (sourceLamPhiMap S)
          (openCoordTriangle 0 1) +
        ENNReal.ofReal (sourceP S) *
          (⨆ w ∈ Ioo (0 : ℝ) 1,
            eVariationOn (S.lam w) (Ioo w 1)) := by
      gcongr
    _ = _ := by ac_rfl

/-- Equation (4.5c): uniform incoming variation of `β` with its axis
variation, incoming `ν` variation, and analytic area. -/
theorem eq4_5c {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    (⨆ v ∈ Ioo (0 : ℝ) 1,
      eVariationOn (fun t => S.beta t v) (Ioo 0 v)) ≤
      eVariationOn (fun t => S.beta t t) (Ioo 0 1) +
      ENNReal.ofReal (sourceP S) *
        (eVariationOn (fun t => S.nu t t) (Ioo 0 1) +
          (⨆ v ∈ Ioo (0 : ℝ) 1,
            eVariationOn (fun t => S.nu t v) (Ioo 0 v))) +
      smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 1) := by
  have hPnn : 0 ≤ sourceP S :=
    (abs_nonneg (S.phi (1 / 2) (1 / 2))).trans
      (abs_phi_axis_le_sourceP H (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1))
  obtain ⟨_, hnu, _, _, hbeta⟩ := unit_field_contDiffOn H
  apply iSup_le
  intro v
  apply iSup_le
  intro hv
  have hmap : MapsTo (fun t : ℝ => (t, v)) (Icc 0 v)
      (closedCoordTriangle 0 1) := by
    intro t ht
    exact ⟨ht.1, ht.2, hv.2.le⟩
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => (t, v)) (Icc 0 v) := by
    fun_prop
  have hBeta : ContDiffOn ℝ 1 (fun t => S.beta t v) (Icc 0 v) :=
    hbeta.comp hpair hmap
  have hNu : ContDiffOn ℝ 1 (fun t => S.nu t v) (Icc 0 v) :=
    hnu.comp hpair hmap
  have hAC (f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (Icc 0 v)) :
      AbsolutelyContinuousOnInterval f 0 v :=
    (show ContDiffOn ℝ 1 f (uIcc 0 v) by
      simpa only [uIcc_of_le hv.1.le] using hf).absolutelyContinuousOnInterval
  have hPhi (t : ℝ) (ht : t ∈ Ioo 0 v) :
      |S.phi t v| ≤ sourceP S :=
    abs_phi_closed_le_sourceP H (p := (t, v))
      ⟨ht.1.le, ht.2.le, hv.2.le⟩
  have hvar := variation_le_residual_add hv.1.le
    (hAC _ hBeta) (hAC _ hNu) hPnn hPhi
  have hres := (eq4_5b H hr hcenter hboot hv).2
  have hsup : eVariationOn (fun t => S.nu t v) (Ioo 0 v) ≤
      ⨆ w ∈ Ioo (0 : ℝ) 1,
        eVariationOn (fun t => S.nu t w) (Ioo 0 w) :=
    le_iSup_of_le v (le_iSup_of_le hv le_rfl)
  calc
    eVariationOn (fun t => S.beta t v) (Ioo 0 v) ≤
        (∫⁻ t in Ioo 0 v,
          ENNReal.ofReal |deriv (fun x => S.beta x v) t -
            deriv (fun x => S.nu x v) t * S.phi t v|) +
          ENNReal.ofReal (sourceP S) *
            eVariationOn (fun t => S.nu t v) (Ioo 0 v) := hvar
    _ ≤ eVariationOn (fun t => S.beta t t) (Ioo 0 1) +
        ENNReal.ofReal (sourceP S) *
          eVariationOn (fun t => S.nu t t) (Ioo 0 1) +
        smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 1) +
        ENNReal.ofReal (sourceP S) *
          eVariationOn (fun t => S.nu t v) (Ioo 0 v) :=
      add_le_add_left hres _
    _ ≤ eVariationOn (fun t => S.beta t t) (Ioo 0 1) +
        ENNReal.ofReal (sourceP S) *
          eVariationOn (fun t => S.nu t t) (Ioo 0 1) +
        smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 1) +
        ENNReal.ofReal (sourceP S) *
          (⨆ w ∈ Ioo (0 : ℝ) 1,
            eVariationOn (fun t => S.nu t w) (Ioo 0 w)) := by
      gcongr
    _ = _ := by rw [mul_add]; ac_rfl

end ChristodoulouBV

end
