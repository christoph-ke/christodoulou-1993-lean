module

public import ChristodoulouBV.AreaEstimates.OutgoingAreaRhoEndpoint
public import ChristodoulouBV.AreaEstimates.OutgoingAreaIntegral
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# The full rho area estimate

Tonelli integrates the fixed-fiber Hardy inequality. The exact factor
`1/2` is the derivative of the reciprocal squared radius.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace ChristodoulouBV

private theorem outgoing_rho_triangle_carrier :
    {p : ℝ × ℝ | p.1 ∈ Ioo 0 1 ∧ p.2 ∈ Ioo p.1 1} =
      openCoordTriangle 0 1 := by
  ext p
  simp only [openCoordTriangle, mem_ofPred_eq, mem_Ioo]
  constructor
  · rintro ⟨⟨h0, _⟩, ⟨huv, hv⟩⟩
    exact ⟨h0, huv, hv⟩
  · rintro ⟨h0, huv, hv⟩
    exact ⟨⟨h0, huv.trans hv⟩, ⟨huv, hv⟩⟩

/-- Equation (4.23): the rho density has at most half the
`(φ, β/ν)` analytic Jacobian area. -/
theorem eq4_23 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    (∫⁻ p in openCoordTriangle 0 1, sourceRhoDensity S p) ≤
      (1 / 2 : ℝ≥0∞) *
        smoothAnalyticArea (sourcePhiBetaNuMap S)
          (openCoordTriangle 0 1) := by
  let T := openCoordTriangle 0 1
  let K := sourceRhoDensity S
  let J : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal |(fderiv ℝ (sourcePhiBetaNuMap S) p).det|
  have hT : MeasurableSet T := by
    change MeasurableSet (openCoordTriangle 0 1)
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior.measurableSet
  have hK : AEMeasurable K (volume.restrict T) :=
    sourceRhoDensity_aemeasurable H
  have hJ : AEMeasurable J (volume.restrict T) :=
    (source_log_jacobian_densities_measurable S).1.aemeasurable
  have hTonelliK : (∫⁻ p in T, K p) =
      ∫⁻ v in Ioo (0 : ℝ) 1, ∫⁻ u in Ioo 0 v, K (u, v) := by
    simpa only [outgoing_rho_triangle_carrier, T] using
      lintegral_open_triangle_swap 0 1 K (by
        simpa only [outgoing_rho_triangle_carrier, T] using hK)
  have hTonelliJ : (∫⁻ p in T, J p) =
      ∫⁻ v in Ioo (0 : ℝ) 1, ∫⁻ u in Ioo 0 v, J (u, v) := by
    simpa only [outgoing_rho_triangle_carrier, T] using
      lintegral_open_triangle_swap 0 1 J (by
        simpa only [outgoing_rho_triangle_carrier, T] using hJ)
  have hRaw : 2 * (∫⁻ p in T, K p) ≤ ∫⁻ p in T, J p := by
    rw [hTonelliK, hTonelliJ]
    calc
      2 * (∫⁻ v in Ioo (0 : ℝ) 1,
          ∫⁻ u in Ioo 0 v, K (u, v)) =
          ∫⁻ v in Ioo (0 : ℝ) 1,
            2 * (∫⁻ u in Ioo 0 v, K (u, v)) := by
        rw [lintegral_const_mul' _ _ (by norm_num)]
      _ ≤ ∫⁻ v in Ioo (0 : ℝ) 1,
          ∫⁻ u in Ioo 0 v, J (u, v) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
        exact sourceRho_fiber_lintegral_bound H hr hcenter hboot hv
  have hArea : smoothAnalyticArea (sourcePhiBetaNuMap S) T =
      ∫⁻ p in T, J p := smooth_analytic_area _ hT
  have hhalf : (1 / 2 : ℝ≥0∞) * 2 = 1 := by
    rw [one_div]
    rw [mul_comm]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  rw [hArea]
  calc
    (∫⁻ p in T, K p) = (1 / 2 : ℝ≥0∞) *
        (2 * ∫⁻ p in T, K p) := by
      rw [← mul_assoc, hhalf, one_mul]
    _ ≤ (1 / 2 : ℝ≥0∞) * (∫⁻ p in T, J p) :=
      mul_le_mul_of_nonneg_left hRaw bot_le

end ChristodoulouBV

end
