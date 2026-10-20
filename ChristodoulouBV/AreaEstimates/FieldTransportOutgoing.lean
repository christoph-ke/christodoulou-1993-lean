module

public import ChristodoulouBV.AreaEstimates.FieldTransportDerivatives
public import ChristodoulouBV.AreaEstimates.BasicEstimatesUnit
public import ChristodoulouBV.AreaEstimates.AnalyticArea
import ChristodoulouBV.AreaEstimates.BasicEstimatesVariationCore
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Tactic

/-!
# Integrated outgoing field transport

This file integrates the residual identity (4.4a) over an outgoing ray.
-/

public section

open Set MeasureTheory Filter
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

/-- The initial variation `D` is the null integral of the absolute initial
`α` derivative. -/
theorem sourceD_eq_lintegral_initial_alpha {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    sourceD S = ∫⁻ v in Ioo 0 1, ENNReal.ofReal |deriv (S.alpha 0) v| := by
  let K := closedCoordTriangle 0 1
  have hmap : MapsTo (fun t : ℝ => ((0 : ℝ), t)) (Icc 0 1) K := by
    intro t ht
    simpa [K, closedCoordTriangle] using
      (show (0 : ℝ) ≤ 0 ∧ 0 ≤ t ∧ t ≤ 1 from ⟨le_refl _, ht.1, ht.2⟩)
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => ((0 : ℝ), t)) (Icc 0 1) := by
    fun_prop
  have hα : ContDiffOn ℝ 1 (S.alpha 0) (Icc 0 1) :=
    (show ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.alpha p.1 p.2) K by
      -- The unit closure argument is already packaged in the C¹ extraction.
      have hK := C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
        (by norm_num : (0 : ℝ) < 1)
      have htheta : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.theta p.1 p.2) K :=
        by simpa only [K, hK] using H.theta_c1
      have hlam : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.lam p.1 p.2) K :=
        by simpa only [K, hK] using H.lam_c1
      have hphi : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2) K :=
        by simpa only [K, hK] using H.phi_c1
      have heq : (fun p : ℝ × ℝ => S.alpha p.1 p.2) =
          (fun p => S.theta p.1 p.2 + S.lam p.1 p.2 * S.phi p.1 p.2) := by
        funext p; simp only [Fields.theta]; ring
      rw [heq]
      exact htheta.add (hlam.mul hphi)).comp hpair hmap
  have hAC : AbsolutelyContinuousOnInterval (S.alpha 0) 0 1 :=
    (show ContDiffOn ℝ 1 (S.alpha 0) (uIcc 0 1) by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hα).absolutelyContinuousOnInterval
  simpa only [sourceD] using (null_lintegral_eq_scalar_variation
    (by norm_num : (0 : ℝ) ≤ 1) hAC (fun _ _ => rfl)).symm

/-- Variation of the initial `α` trace on a terminal subinterval is its
absolute derivative integral. -/
theorem initial_alpha_variation_eq_lintegral {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    eVariationOn (S.alpha 0) (Ioo u 1) =
      ∫⁻ v in Ioo u 1, ENNReal.ofReal |deriv (S.alpha 0) v| := by
  let K := closedCoordTriangle 0 1
  have hmap : MapsTo (fun t : ℝ => ((0 : ℝ), t)) (Icc u 1) K := by
    intro t ht
    simpa [K, closedCoordTriangle] using
      (show (0 : ℝ) ≤ 0 ∧ 0 ≤ t ∧ t ≤ 1 from
        ⟨le_refl _, hu.1.le.trans ht.1, ht.2⟩)
  have hpair : ContDiffOn ℝ 1 (fun t : ℝ => ((0 : ℝ), t)) (Icc u 1) := by
    fun_prop
  have hK := C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
    (by norm_num : (0 : ℝ) < 1)
  have htheta : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.theta p.1 p.2) K :=
    by simpa only [K, hK] using H.theta_c1
  have hlam : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.lam p.1 p.2) K :=
    by simpa only [K, hK] using H.lam_c1
  have hphi : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.phi p.1 p.2) K :=
    by simpa only [K, hK] using H.phi_c1
  have heq : (fun p : ℝ × ℝ => S.alpha p.1 p.2) =
      (fun p => S.theta p.1 p.2 + S.lam p.1 p.2 * S.phi p.1 p.2) := by
    funext p; simp only [Fields.theta]; ring
  have hAlphaK : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => S.alpha p.1 p.2) K := by
    rw [heq]
    exact htheta.add (hlam.mul hphi)
  have hα : ContDiffOn ℝ 1 (S.alpha 0) (Icc u 1) :=
    hAlphaK.comp hpair hmap
  have hAC : AbsolutelyContinuousOnInterval (S.alpha 0) u 1 :=
    (show ContDiffOn ℝ 1 (S.alpha 0) (uIcc u 1) by
      simpa only [uIcc_of_le hu.2.le] using hα).absolutelyContinuousOnInterval
  exact (null_lintegral_eq_scalar_variation hu.2.le hAC
    (fun _ _ => rfl)).symm

/-- The outgoing gauge makes the initial `λ` derivative vanish on the open
initial edge. -/
theorem initial_lam_deriv_eq_zero {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    deriv (S.lam 0) v = 0 := by
  have hEq : (S.lam 0) =ᶠ[𝓝 v] (fun _ => (1 / 2 : ℝ)) := by
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with t ht
    exact (source_gauge_data H hr t ht).2
  exact ((hasDerivAt_const v (1 / 2 : ℝ)).congr_of_eventuallyEq
    hEq).deriv

/-- Equation (4.4b), with both the preceding rectangle and the full analytic
area of the unit triangle displayed. -/
theorem eq4_4b {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ v in Ioo u 1,
      ENNReal.ofReal |deriv (S.alpha u) v - deriv (S.lam u) v * S.phi u v|) ≤
        eVariationOn (S.alpha 0) (Ioo u 1) +
          smoothAnalyticArea (sourceLamPhiMap S)
          (Ioo 0 u ×ˢ Ioo u 1) ∧
    (∫⁻ v in Ioo u 1,
      ENNReal.ofReal |deriv (S.alpha u) v - deriv (S.lam u) v * S.phi u v|) ≤
        sourceD S + smoothAnalyticArea (sourceLamPhiMap S)
          (openCoordTriangle 0 1) := by
  let A := Ioo (0 : ℝ) u
  let B := Ioo u 1
  let F := sourceLamPhiMap S
  let J : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal |(fderiv ℝ F p).det|
  let R : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal
    |deriv (S.alpha u) v - deriv (S.lam u) v * S.phi u v|
  let I : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal |deriv (S.alpha 0) v|
  have hrect : A ×ˢ B ⊆ openCoordTriangle 0 1 := by
    intro p hp
    change p.1 ∈ A ∧ p.2 ∈ B at hp
    exact ⟨hp.1.1, hp.1.2.trans hp.2.1, hp.2.2⟩
  have hopen : IsOpen (A ×ˢ B) := isOpen_Ioo.prod isOpen_Ioo
  have hmap : ContDiffOn ℝ 1 F (A ×ˢ B) :=
    (sourceLamPhiMap_contDiffOn H).mono (fun p hp =>
      ⟨hp.1.1.le, (hp.1.2.trans hp.2.1).le, hp.2.2.le⟩)
  have hJ : AEMeasurable J ((volume.restrict A).prod (volume.restrict B)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]
    exact jacobianDensity_aemeasurable_of_contDiffOn hopen hmap
  have hI : AEMeasurable I (volume.restrict B) :=
    ((measurable_deriv (S.alpha 0)).abs.ennreal_ofReal).aemeasurable
  have hpoint (v : ℝ) (hv : v ∈ B) :
      R v ≤ I v + ∫⁻ x in A, J (x, v) := by
    have hv' : v ∈ Ioo (0 : ℝ) 1 := ⟨hu.1.trans hv.1, hv.2⟩
    have h0 := initial_lam_deriv_eq_zero H hr hv'
    have hbound := eq4_4a H hr hcenter hboot hu.1 hv.1 hv.2
    simpa only [R, I, J, F, A, h0, zero_mul, sub_zero] using hbound
  have hraw := lintegral_residual_le_initial_add_rectangle
    A B R I J measurableSet_Ioo hI hJ hpoint
  have hD : (∫⁻ v in B, I v) =
      eVariationOn (S.alpha 0) (Ioo u 1) :=
    (initial_alpha_variation_eq_lintegral H hu).symm
  have harea : (∫⁻ p in A ×ˢ B, J p) =
      smoothAnalyticArea F (A ×ˢ B) :=
    (smooth_analytic_area F hopen.measurableSet).symm
  have hfirst : (∫⁻ v in B, R v) ≤
      eVariationOn (S.alpha 0) (Ioo u 1) +
        smoothAnalyticArea F (A ×ˢ B) := by
    simpa only [hD, harea] using hraw
  constructor
  · exact hfirst
  · have hvariation : eVariationOn (S.alpha 0) (Ioo u 1) ≤ sourceD S := by
      apply eVariationOn.mono
      intro v hv
      exact ⟨hu.1.trans hv.1, hv.2⟩
    exact hfirst.trans (add_le_add hvariation (measure_mono hrect))

end ChristodoulouBV

end
