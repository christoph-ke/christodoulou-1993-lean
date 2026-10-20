module

public import ChristodoulouBV.AreaEstimates.FieldTransportAxis
import all ChristodoulouBV.AreaEstimates.FieldTransportAxis
import ChristodoulouBV.AreaEstimates.FieldTransportIntegral
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Tactic

/-!
# Integrated incoming field transport

The β residual is integrated over an incoming ray. Tonelli identifies the
iterated Jacobian integral with analytic area of the preceding triangle.
-/

public section

open Set MeasureTheory Filter
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

/-- Equation (4.5b), with the corrected absolute scalar factor on the axis. -/
theorem eq4_5b {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ u in Ioo 0 v,
      ENNReal.ofReal |deriv (fun x => S.beta x v) u -
        deriv (fun x => S.nu x v) u * S.phi u v|) ≤
      eVariationOn (fun t => S.beta t t) (Ioo 0 1) +
      axisScalarSup S *
        eVariationOn (fun t => S.nu t t) (Ioo 0 1) +
      smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 v) ∧
    (∫⁻ u in Ioo 0 v,
      ENNReal.ofReal |deriv (fun x => S.beta x v) u -
        deriv (fun x => S.nu x v) u * S.phi u v|) ≤
      eVariationOn (fun t => S.beta t t) (Ioo 0 1) +
      ENNReal.ofReal (sourceP S) *
        eVariationOn (fun t => S.nu t t) (Ioo 0 1) +
      smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 1) := by
  let A := Ioo (0 : ℝ) v
  let E := openCoordTriangle 0 v
  let F := sourceNuPhiMap S
  let J : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal |(fderiv ℝ F p).det|
  let R : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal
    |deriv (fun x => S.beta x v) u - deriv (fun x => S.nu x v) u * S.phi u v|
  let Ib : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal |deriv (fun x => S.beta x x) u|
  let In : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal |deriv (fun x => S.nu x x) u|
  let I : ℝ → ℝ≥0∞ := fun u => Ib u + axisScalarSup S * In u
  have hopen : IsOpen E := by
    change IsOpen (openCoordTriangle 0 v)
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior
  have hEsub : E ⊆ closedCoordTriangle 0 1 := by
    intro p hp
    exact ⟨hp.1.le, hp.2.1.le, hp.2.2.le.trans hv.2.le⟩
  have hmap : ContDiffOn ℝ 1 F E :=
    (sourceNuPhiMap_contDiffOn H).mono hEsub
  have hJ : AEMeasurable J (volume.restrict E) :=
    jacobianDensity_aemeasurable_of_contDiffOn hopen hmap
  have hIb : Measurable Ib :=
    (measurable_deriv (fun x => S.beta x x)).abs.ennreal_ofReal
  have hIn : Measurable In :=
    (measurable_deriv (fun x => S.nu x x)).abs.ennreal_ofReal
  have hI : AEMeasurable I (volume.restrict A) :=
    (hIb.add (measurable_const.mul hIn)).aemeasurable
  have hpoint (u : ℝ) (hu : u ∈ A) :
      R u ≤ I u + ∫⁻ y in Ioo u v, J (u, y) := by
    have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans hv.2⟩
    have hreal : |deriv (fun x => S.beta x x) u -
        deriv (fun x => S.nu x x) u * S.phi u u| ≤
        |deriv (fun x => S.beta x x) u| +
          |deriv (fun x => S.nu x x) u| * |S.phi u u| := by
      rw [← abs_mul]
      exact abs_sub _ _
    have hPhiSup : ENNReal.ofReal |S.phi u u| ≤ axisScalarSup S := by
      rw [axisScalarSup]
      exact le_iSup_of_le u (le_iSup_of_le hu' le_rfl)
    have hcast : ENNReal.ofReal
        |deriv (fun x => S.beta x x) u -
          deriv (fun x => S.nu x x) u * S.phi u u| ≤ I u := by
      have h := ENNReal.ofReal_le_ofReal hreal
      rw [ENNReal.ofReal_add (abs_nonneg _)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)),
        ENNReal.ofReal_mul (abs_nonneg _)] at h
      calc
        _ ≤ Ib u + In u * ENNReal.ofReal |S.phi u u| := h
        _ ≤ Ib u + In u * axisScalarSup S := by gcongr
        _ = I u := by
          simp only [I]
          ac_rfl
    have hbound := eq4_5a H hr hcenter hboot hu.1 hu.2 hv.2
    exact hbound.trans (add_le_add_left hcast _)
  have hraw : (∫⁻ u in A, R u) ≤
      (∫⁻ u in A, I u) + ∫⁻ p in E, J p := by
    calc
      (∫⁻ u in A, R u) ≤
          ∫⁻ u in A, I u + ∫⁻ y in Ioo u v, J (u, y) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        exact hpoint u hu
      _ = (∫⁻ u in A, I u) +
          ∫⁻ u in A, ∫⁻ y in Ioo u v, J (u, y) := by
        rw [lintegral_add_left' hI]
      _ = (∫⁻ u in A, I u) + ∫⁻ p in E, J p := by
        congr 1
        have hset : E = {p : ℝ × ℝ | p.1 ∈ Ioo 0 v ∧ p.2 ∈ Ioo p.1 v} := by
          ext p
          simp only [E, openCoordTriangle, mem_ofPred_eq, mem_Ioo]
          constructor
          · rintro ⟨h0, h12, h2v⟩
            exact ⟨⟨h0, h12.trans h2v⟩, ⟨h12, h2v⟩⟩
          · rintro ⟨⟨h0, _⟩, ⟨h12, h2v⟩⟩
            exact ⟨h0, h12, h2v⟩
        exact (lintegral_open_triangle 0 v J (by
          simpa only [← hset] using hJ)).symm.trans (by rw [← hset])
  have hIbBound : (∫⁻ u in A, Ib u) ≤
      eVariationOn (fun t => S.beta t t) (Ioo 0 1) := by
    rw [(unit_axis_variation_eq_lintegral H).2.2.2]
    exact lintegral_mono_set (fun u hu => ⟨hu.1, hu.2.trans hv.2⟩)
  have hInBound : (∫⁻ u in A, In u) ≤
      eVariationOn (fun t => S.nu t t) (Ioo 0 1) := by
    rw [(unit_axis_variation_eq_lintegral H).2.1]
    exact lintegral_mono_set (fun u hu => ⟨hu.1, hu.2.trans hv.2⟩)
  have hIBound : (∫⁻ u in A, I u) ≤
      eVariationOn (fun t => S.beta t t) (Ioo 0 1) +
        axisScalarSup S *
          eVariationOn (fun t => S.nu t t) (Ioo 0 1) := by
    change (∫⁻ u in A, Ib u + axisScalarSup S * In u) ≤ _
    rw [lintegral_add_left' hIb.aemeasurable]
    rw [lintegral_const_mul'' _ hIn.aemeasurable]
    exact add_le_add hIbBound (mul_le_mul_of_nonneg_left hInBound bot_le)
  have harea : (∫⁻ p in E, J p) = smoothAnalyticArea F E :=
    (smooth_analytic_area F hopen.measurableSet).symm
  have hfirst : (∫⁻ u in A, R u) ≤
      eVariationOn (fun t => S.beta t t) (Ioo 0 1) +
        axisScalarSup S *
          eVariationOn (fun t => S.nu t t) (Ioo 0 1) +
        smoothAnalyticArea F E := by
    rw [harea] at hraw
    exact hraw.trans (add_le_add_left hIBound _)
  constructor
  · exact hfirst
  · have hsub : E ⊆ openCoordTriangle 0 1 := by
      intro p hp
      exact ⟨hp.1, hp.2.1, hp.2.2.trans hv.2⟩
    have hcoeff := axisScalarSup_le_sourceP H
    calc
      (∫⁻ u in A, R u) ≤
          eVariationOn (fun t => S.beta t t) (Ioo 0 1) +
            axisScalarSup S *
              eVariationOn (fun t => S.nu t t) (Ioo 0 1) +
            smoothAnalyticArea F E := hfirst
      _ ≤ eVariationOn (fun t => S.beta t t) (Ioo 0 1) +
          ENNReal.ofReal (sourceP S) *
            eVariationOn (fun t => S.nu t t) (Ioo 0 1) +
          smoothAnalyticArea F (openCoordTriangle 0 1) := by
        gcongr

end ChristodoulouBV

end
