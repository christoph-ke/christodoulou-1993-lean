module

public import ChristodoulouBV.AreaEstimates.ScalarAreaWeighted
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Tactic

/-!
# Measurable scalar residual envelopes

The fields are only prescribed on the development. These cut-off envelopes
agree with the source majorants on the unit interval and are measurable on
the whole real line, as required for Tonelli.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace ChristodoulouBV

private theorem jacobian_density_measurable (F : ℝ × ℝ → ℝ × ℝ) :
    Measurable (fun p => ENNReal.ofReal |(fderiv ℝ F p).det|) :=
  ((ContinuousLinearMap.continuous_det.measurable.comp
    (measurable_fderiv ℝ F)).abs).ennreal_ofReal

/-- The outgoing majorant, extended by zero outside the unit interval using
a globally measurable Jacobian integrand. -/
noncomputable def sourceAlphaMajorantMeasurable (S : Fields) (v : ℝ) : ℝ≥0∞ :=
  (Ioo (0 : ℝ) 1).indicator
    (fun v => ENNReal.ofReal |deriv (S.alpha 0) v| +
      ∫⁻ u,
        (openCoordTriangle 0 1).indicator
          (fun p => ENNReal.ofReal
            |(fderiv ℝ (sourceLamPhiMap S) p).det|) (u, v)) v

/-- The incoming envelope uses the axis variation terms in (4.17c), so no
global measurability of the scalar trace outside the development is needed. -/
noncomputable def sourceBetaMajorantMeasurable (S : Fields) (u : ℝ) : ℝ≥0∞ :=
  (Ioo (0 : ℝ) 1).indicator
    (fun u => ENNReal.ofReal |deriv (fun t => S.beta t t) u| +
      ENNReal.ofReal (6 * (sourceD S).toReal) *
        ENNReal.ofReal |deriv (fun t => S.nu t t) u| +
      ∫⁻ v,
        (openCoordTriangle 0 1).indicator
          (fun p => ENNReal.ofReal
            |(fderiv ℝ (sourceNuPhiMap S) p).det|) (u, v)) u

/-- The cut-off outgoing majorant is globally measurable. -/
theorem sourceAlphaMajorantMeasurable_measurable (S : Fields) :
    Measurable (sourceAlphaMajorantMeasurable S) := by
  let T := openCoordTriangle 0 1
  let J : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal |(fderiv ℝ (sourceLamPhiMap S) p).det|
  have hT : MeasurableSet T := by
    change MeasurableSet (openCoordTriangle 0 1)
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior.measurableSet
  have hJ : Measurable J := jacobian_density_measurable _
  have hinner : Measurable (fun v => ∫⁻ u, T.indicator J (u, v)) :=
    (hJ.indicator hT).lintegral_prod_left'
  have hI : Measurable (fun v => ENNReal.ofReal |deriv (S.alpha 0) v|) :=
    (measurable_deriv (S.alpha 0)).abs.ennreal_ofReal
  exact (hI.add hinner).indicator measurableSet_Ioo

/-- The cut-off incoming envelope is globally measurable. -/
theorem sourceBetaMajorantMeasurable_measurable (S : Fields) :
    Measurable (sourceBetaMajorantMeasurable S) := by
  let T := openCoordTriangle 0 1
  let J : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal |(fderiv ℝ (sourceNuPhiMap S) p).det|
  have hT : MeasurableSet T := by
    change MeasurableSet (openCoordTriangle 0 1)
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior.measurableSet
  have hJ : Measurable J := jacobian_density_measurable _
  have hinner : Measurable (fun u => ∫⁻ v, T.indicator J (u, v)) :=
    (hJ.indicator hT).lintegral_prod_right'
  have hB : Measurable
      (fun u => ENNReal.ofReal |deriv (fun t => S.beta t t) u|) :=
    (measurable_deriv (fun t => S.beta t t)).abs.ennreal_ofReal
  have hN : Measurable
      (fun u => ENNReal.ofReal |deriv (fun t => S.nu t t) u|) :=
    (measurable_deriv (fun t => S.nu t t)).abs.ennreal_ofReal
  exact ((hB.add (measurable_const.mul hN)).add hinner).indicator
    measurableSet_Ioo

private theorem outgoing_indicator_fiber {S : Fields} {v : ℝ}
    (hv : v ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ u,
      (openCoordTriangle 0 1).indicator
        (fun p => ENNReal.ofReal
          |(fderiv ℝ (sourceLamPhiMap S) p).det|) (u, v)) =
      ∫⁻ u in Ioo 0 v,
        ENNReal.ofReal |(fderiv ℝ (sourceLamPhiMap S) (u, v)).det| := by
  have hfiber : (fun u => (openCoordTriangle 0 1).indicator
      (fun p => ENNReal.ofReal
        |(fderiv ℝ (sourceLamPhiMap S) p).det|) (u, v)) =
      (Ioo 0 v).indicator (fun u =>
        ENNReal.ofReal |(fderiv ℝ (sourceLamPhiMap S) (u, v)).det|) := by
    funext u
    by_cases hu : u ∈ Ioo (0 : ℝ) v
    · have hT : (u, v) ∈ openCoordTriangle 0 1 := ⟨hu.1, hu.2, hv.2⟩
      simp only [indicator_of_mem hT, indicator_of_mem hu]
    · have hT : (u, v) ∉ openCoordTriangle 0 1 := by
        intro hp
        exact hu ⟨hp.1, hp.2.1⟩
      simp only [indicator_of_notMem hT, indicator_of_notMem hu]
  rw [hfiber, lintegral_indicator measurableSet_Ioo]

private theorem incoming_indicator_fiber {S : Fields} {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ v,
      (openCoordTriangle 0 1).indicator
        (fun p => ENNReal.ofReal
          |(fderiv ℝ (sourceNuPhiMap S) p).det|) (u, v)) =
      ∫⁻ v in Ioo u 1,
        ENNReal.ofReal |(fderiv ℝ (sourceNuPhiMap S) (u, v)).det| := by
  have hfiber : (fun v => (openCoordTriangle 0 1).indicator
      (fun p => ENNReal.ofReal
        |(fderiv ℝ (sourceNuPhiMap S) p).det|) (u, v)) =
      (Ioo u 1).indicator (fun v =>
        ENNReal.ofReal |(fderiv ℝ (sourceNuPhiMap S) (u, v)).det|) := by
    funext v
    by_cases hv : v ∈ Ioo u 1
    · have hT : (u, v) ∈ openCoordTriangle 0 1 := ⟨hu.1, hv.1, hv.2⟩
      simp only [indicator_of_mem hT, indicator_of_mem hv]
    · have hT : (u, v) ∉ openCoordTriangle 0 1 := by
        intro hp
        exact hv ⟨hp.2.1, hp.2.2⟩
      simp only [indicator_of_notMem hT, indicator_of_notMem hv]
  rw [hfiber, lintegral_indicator measurableSet_Ioo]

/-- On the source interval, the measurable outgoing envelope is exactly `F`. -/
theorem sourceAlphaMajorantMeasurable_eq {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    sourceAlphaMajorantMeasurable S v = sourceAlphaMajorant S v := by
  simp only [sourceAlphaMajorantMeasurable, indicator_of_mem hv,
    sourceAlphaMajorant, initial_lam_deriv_eq_zero H hr hv,
    zero_mul, sub_zero, outgoing_indicator_fiber hv]

/-- On the source interval, the measurable incoming envelope dominates `F*`. -/
theorem sourceBetaMajorant_le_measurable {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    sourceBetaMajorant S u ≤ sourceBetaMajorantMeasurable S u := by
  have hP : sourceP S ≤ 6 * (sourceD S).toReal :=
    (lemma4_2 H hr hcenter hboot).2.2
  have hreal : |deriv (fun t => S.beta t t) u -
      deriv (fun t => S.nu t t) u * S.phi u u| ≤
      |deriv (fun t => S.beta t t) u| +
        |deriv (fun t => S.nu t t) u| * |S.phi u u| := by
    rw [← abs_mul]
    exact abs_sub _ _
  have hcast := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (abs_nonneg _)
    (mul_nonneg (abs_nonneg _) (abs_nonneg _)),
    ENNReal.ofReal_mul (abs_nonneg _)] at hcast
  have hphi : ENNReal.ofReal |S.phi u u| ≤
      ENNReal.ofReal (6 * (sourceD S).toReal) :=
    ENNReal.ofReal_le_ofReal ((abs_phi_axis_le_sourceP H hu).trans hP)
  have hfirst : ENNReal.ofReal
      |deriv (fun t => S.beta t t) u -
        deriv (fun t => S.nu t t) u * S.phi u u| ≤
      ENNReal.ofReal |deriv (fun t => S.beta t t) u| +
        ENNReal.ofReal (6 * (sourceD S).toReal) *
          ENNReal.ofReal |deriv (fun t => S.nu t t) u| := by
    calc
      _ ≤ ENNReal.ofReal |deriv (fun t => S.beta t t) u| +
          ENNReal.ofReal |deriv (fun t => S.nu t t) u| *
            ENNReal.ofReal |S.phi u u| := hcast
      _ ≤ ENNReal.ofReal |deriv (fun t => S.beta t t) u| +
          ENNReal.ofReal |deriv (fun t => S.nu t t) u| *
            ENNReal.ofReal (6 * (sourceD S).toReal) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hphi bot_le) _
      _ = _ := by ac_rfl
  rw [sourceBetaMajorant, sourceBetaMajorantMeasurable,
    indicator_of_mem hu, incoming_indicator_fiber hu]
  exact add_le_add hfirst le_rfl

/-- The measurable outgoing envelope has the (4.15c) integral bound. -/
theorem sourceAlphaMajorantMeasurable_integral_le {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    (∫⁻ v in Ioo (0 : ℝ) 1, sourceAlphaMajorantMeasurable S v) ≤
      sourceD S + smoothAnalyticArea (sourceLamPhiMap S)
        (openCoordTriangle 0 1) := by
  have heq : (∫⁻ v in Ioo (0 : ℝ) 1, sourceAlphaMajorantMeasurable S v) =
      ∫⁻ v in Ioo (0 : ℝ) 1, sourceAlphaMajorant S v := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact sourceAlphaMajorantMeasurable_eq H hr hv
  rw [heq]
  exact eq4_15c H hr hcenter hboot

/-- The measurable incoming envelope integrates to its two axis variations
and the `(ν, φ)` analytic area. -/
theorem sourceBetaMajorantMeasurable_integral {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    (∫⁻ u in Ioo (0 : ℝ) 1, sourceBetaMajorantMeasurable S u) =
      eVariationOn (fun t => S.beta t t) (Ioo 0 1) +
      ENNReal.ofReal (6 * (sourceD S).toReal) *
        eVariationOn (fun t => S.nu t t) (Ioo 0 1) +
      smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 1) := by
  let Ib : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal |deriv (fun t => S.beta t t) u|
  let In : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal |deriv (fun t => S.nu t t) u|
  let J : ℝ → ℝ≥0∞ := fun u => ∫⁻ v in Ioo u 1,
    ENNReal.ofReal |(fderiv ℝ (sourceNuPhiMap S) (u, v)).det|
  let C : ℝ≥0∞ := ENNReal.ofReal (6 * (sourceD S).toReal)
  have hIb : AEMeasurable Ib (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ((measurable_deriv (fun t => S.beta t t)).abs.ennreal_ofReal).aemeasurable
  have hIn : AEMeasurable In (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ((measurable_deriv (fun t => S.nu t t)).abs.ennreal_ofReal).aemeasurable
  have hsum : AEMeasurable (fun u => Ib u + C * In u)
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    hIb.add (aemeasurable_const.mul hIn)
  have hvar := unit_axis_variation_eq_lintegral H
  have harea := (triangle_jacobian_integral
    (sourceNuPhiMap_contDiffOn H)).2
  calc
    (∫⁻ u in Ioo (0 : ℝ) 1, sourceBetaMajorantMeasurable S u) =
        ∫⁻ u in Ioo (0 : ℝ) 1, Ib u + C * In u + J u := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      simp only [sourceBetaMajorantMeasurable, indicator_of_mem hu,
        incoming_indicator_fiber hu, Ib, In, J, C]
    _ = (∫⁻ u in Ioo (0 : ℝ) 1, Ib u) +
        C * (∫⁻ u in Ioo (0 : ℝ) 1, In u) +
          ∫⁻ u in Ioo (0 : ℝ) 1, J u := by
      rw [lintegral_add_left' hsum J,
        lintegral_add_left' hIb (fun u => C * In u),
        lintegral_const_mul'' _ hIn]
    _ = _ := by
      rw [hvar.2.1, hvar.2.2.2, harea]

end ChristodoulouBV

end
