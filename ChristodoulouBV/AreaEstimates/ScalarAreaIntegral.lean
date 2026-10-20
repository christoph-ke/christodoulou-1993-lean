module

public import ChristodoulouBV.AreaEstimates.ScalarAreaMajorants
import all ChristodoulouBV.AreaEstimates.FieldTransportAxis
import all ChristodoulouBV.AreaEstimates.BasicEstimatesUnit
import ChristodoulouBV.AreaEstimates.FieldTransportIntegral
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Tactic

/-!
# Integrals of the scalar residual majorants

Tonelli turns the iterated absolute Jacobian terms in `F` and `F*` into
the analytic areas of the open unit triangle.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace ChristodoulouBV

private theorem open_triangle_carrier :
    {p : ℝ × ℝ | p.1 ∈ Ioo 0 1 ∧ p.2 ∈ Ioo p.1 1} =
      openCoordTriangle 0 1 := by
  ext p
  simp only [openCoordTriangle, mem_ofPred_eq, mem_Ioo]
  constructor
  · rintro ⟨⟨h0, _⟩, ⟨huv, hv⟩⟩
    exact ⟨h0, huv, hv⟩
  · rintro ⟨h0, huv, hv⟩
    exact ⟨⟨h0, huv.trans hv⟩, ⟨huv, hv⟩⟩

/-- Tonelli identifies both iterated triangle Jacobian integrals with the
smooth analytic area. -/
theorem triangle_jacobian_integral
    {F : ℝ × ℝ → ℝ × ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 1)) :
    (∫⁻ v in Ioo (0 : ℝ) 1, ∫⁻ u in Ioo 0 v,
      ENNReal.ofReal |(fderiv ℝ F (u, v)).det|) =
      smoothAnalyticArea F (openCoordTriangle 0 1) ∧
    (∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo u 1,
      ENNReal.ofReal |(fderiv ℝ F (u, v)).det|) =
      smoothAnalyticArea F (openCoordTriangle 0 1) := by
  let T := openCoordTriangle 0 1
  have hopen : IsOpen T := by
    change IsOpen (openCoordTriangle 0 1)
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior
  have hJ : AEMeasurable
      (fun p => ENNReal.ofReal |(fderiv ℝ F p).det|)
      (volume.restrict T) :=
    jacobianDensity_aemeasurable_of_contDiffOn hopen
      (hF.mono (fun p hp => ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩))
  have hA := smooth_analytic_area F hopen.measurableSet
  constructor
  · rw [hA]
    exact (lintegral_open_triangle_swap 0 1 _
      (by simpa only [open_triangle_carrier, T] using hJ)).symm.trans
        (by rw [open_triangle_carrier])
  · rw [hA]
    exact (lintegral_open_triangle 0 1 _
      (by simpa only [open_triangle_carrier, T] using hJ)).symm.trans
        (by rw [open_triangle_carrier])

/-- Equation (4.15c): the outgoing majorant has integral at most initial
variation plus the `(λ, φ)` analytic area. -/
theorem eq4_15c {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (_hcenter : S.phi 0 0 = 0) (_hboot : s4_bootstrap S) :
    (∫⁻ v in Ioo (0 : ℝ) 1, sourceAlphaMajorant S v) ≤
      sourceD S + smoothAnalyticArea (sourceLamPhiMap S)
        (openCoordTriangle 0 1) := by
  let I : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal |deriv (S.alpha 0) v|
  let J : ℝ → ℝ≥0∞ := fun v => ∫⁻ u in Ioo 0 v,
    ENNReal.ofReal |(fderiv ℝ (sourceLamPhiMap S) (u, v)).det|
  have hI : AEMeasurable I (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ((measurable_deriv (S.alpha 0)).abs.ennreal_ofReal).aemeasurable
  have heq : EqOn (sourceAlphaMajorant S) (fun v => I v + J v)
      (Ioo (0 : ℝ) 1) := by
    intro v hv
    simp only [sourceAlphaMajorant, I, J,
      initial_lam_deriv_eq_zero H hr hv, zero_mul, sub_zero]
  calc
    (∫⁻ v in Ioo (0 : ℝ) 1, sourceAlphaMajorant S v) =
        ∫⁻ v in Ioo (0 : ℝ) 1, I v + J v := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
          exact heq hv
    _ = (∫⁻ v in Ioo (0 : ℝ) 1, I v) +
          ∫⁻ v in Ioo (0 : ℝ) 1, J v :=
      lintegral_add_left' hI J
    _ = sourceD S + smoothAnalyticArea (sourceLamPhiMap S)
          (openCoordTriangle 0 1) := by
      rw [sourceD_eq_lintegral_initial_alpha H]
      exact congrArg₂ (· + ·) rfl
        (triangle_jacobian_integral (sourceLamPhiMap_contDiffOn H)).1
    _ ≤ _ := le_rfl

/-- Equation (4.17c): the incoming majorant is controlled by the two axis
variations and the `(ν, φ)` analytic area. Lemma 4.2 supplies the universal
coefficient `6` on `D`. -/
theorem eq4_17c {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    (∫⁻ u in Ioo (0 : ℝ) 1, sourceBetaMajorant S u) ≤
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
  have hP : sourceP S ≤ 6 * (sourceD S).toReal :=
    (lemma4_2 H hr hcenter hboot).2.2
  have hpoint (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
      sourceBetaMajorant S u ≤ Ib u + C * In u + J u := by
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
    have hphi : ENNReal.ofReal |S.phi u u| ≤ C := by
      exact ENNReal.ofReal_le_ofReal
        ((abs_phi_axis_le_sourceP H hu).trans hP)
    have hfirst : ENNReal.ofReal
        |deriv (fun t => S.beta t t) u -
          deriv (fun t => S.nu t t) u * S.phi u u| ≤
        Ib u + C * In u := by
      calc
        _ ≤ Ib u + In u * ENNReal.ofReal |S.phi u u| := hcast
        _ ≤ Ib u + In u * C := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_left hphi (show (0 : ℝ≥0∞) ≤ In u from bot_le))
            (Ib u)
        _ = Ib u + C * In u := by rw [mul_comm]
    change ENNReal.ofReal
        |deriv (fun t => S.beta t t) u -
          deriv (fun t => S.nu t t) u * S.phi u u| + J u ≤
        Ib u + C * In u + J u
    exact add_le_add hfirst le_rfl
  have hvar := unit_axis_variation_eq_lintegral H
  calc
    (∫⁻ u in Ioo (0 : ℝ) 1, sourceBetaMajorant S u) ≤
        ∫⁻ u in Ioo (0 : ℝ) 1, Ib u + C * In u + J u := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact hpoint u hu
    _ = (∫⁻ u in Ioo (0 : ℝ) 1, Ib u) +
        C * (∫⁻ u in Ioo (0 : ℝ) 1, In u) +
          ∫⁻ u in Ioo (0 : ℝ) 1, J u := by
      have hsum : AEMeasurable (fun u => Ib u + C * In u)
          (volume.restrict (Ioo (0 : ℝ) 1)) :=
        hIb.add (aemeasurable_const.mul hIn)
      have hsplit := lintegral_add_left' hsum J
      have hsplit1 := lintegral_add_left' hIb (fun u => C * In u)
      rw [hsplit, hsplit1, lintegral_const_mul'' _ hIn]
    _ = eVariationOn (fun t => S.beta t t) (Ioo 0 1) +
        C * eVariationOn (fun t => S.nu t t) (Ioo 0 1) +
          smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 1) := by
      rw [hvar.2.1, hvar.2.2.2,
        (triangle_jacobian_integral (sourceNuPhiMap_contDiffOn H)).2]
    _ ≤ _ := le_rfl

end ChristodoulouBV

end
