module

public import ChristodoulouBV.AreaEstimates.ScalarAreaJacobian
import ChristodoulouBV.AreaEstimates.FieldTransportIntegral
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Weighted triangular area estimate

This Tonelli lemma is the common measure-theoretic step in (4.16) and (4.18).
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace ChristodoulouBV

private theorem triangle_carrier_eq :
    {p : ℝ × ℝ | p.1 ∈ Ioo 0 1 ∧ p.2 ∈ Ioo p.1 1} =
      openCoordTriangle 0 1 := by
  ext p
  simp only [openCoordTriangle, mem_ofPred_eq, mem_Ioo]
  constructor
  · rintro ⟨⟨h0, _⟩, ⟨huv, hv⟩⟩
    exact ⟨h0, huv, hv⟩
  · rintro ⟨h0, huv, hv⟩
    exact ⟨⟨h0, huv.trans hv⟩, ⟨huv, hv⟩⟩

/-- An abstract weighted Jacobian estimate on the strict unit triangle. -/
theorem scalar_area_weighted_bound
    (W J K : ℝ × ℝ → ℝ≥0∞) (F : ℝ → ℝ≥0∞)
    (c d Y D A : ℝ≥0∞)
    (hW : AEMeasurable W
      (volume.restrict (openCoordTriangle 0 1)))
    (hF : Measurable F)
    (hK : AEMeasurable K
      (volume.restrict (openCoordTriangle 0 1)))
    (hWs : ∀ v ∈ Ioo (0 : ℝ) 1,
      AEMeasurable (fun u => W (u, v))
        (volume.restrict (Ioo 0 v)))
    (hmajor : ∀ v ∈ Ioo (0 : ℝ) 1,
      (∫⁻ u in Ioo 0 v, W (u, v)) ≤ Y)
    (hpoint : ∀ p ∈ openCoordTriangle 0 1,
      J p ≤ c * (W p * F p.2) + d * K p)
    (hFintegral : (∫⁻ v in Ioo (0 : ℝ) 1, F v) ≤ D + A)
    (hKintegral : (∫⁻ p in openCoordTriangle 0 1, K p) = A) :
    (∫⁻ p in openCoordTriangle 0 1, J p) ≤
      c * (Y * (D + A)) + d * A := by
  let T := openCoordTriangle 0 1
  have hFsnd : AEMeasurable (fun p : ℝ × ℝ => F p.2)
      (volume.restrict T) :=
    (hF.comp measurable_snd).aemeasurable
  have hWF : AEMeasurable (fun p : ℝ × ℝ => W p * F p.2)
      (volume.restrict T) := hW.mul hFsnd
  have hCW : AEMeasurable (fun p : ℝ × ℝ => c * (W p * F p.2))
      (volume.restrict T) := aemeasurable_const.mul hWF
  have hTonelli : (∫⁻ p in T, W p * F p.2) =
      ∫⁻ v in Ioo (0 : ℝ) 1, ∫⁻ u in Ioo 0 v, W (u, v) * F v := by
    simpa only [triangle_carrier_eq, T] using
      (lintegral_open_triangle_swap 0 1 _
        (by simpa only [triangle_carrier_eq, T] using hWF))
  have hWFbound : (∫⁻ p in T, W p * F p.2) ≤
      Y * (D + A) := by
    calc
      (∫⁻ p in T, W p * F p.2) =
          ∫⁻ v in Ioo (0 : ℝ) 1,
            (∫⁻ u in Ioo 0 v, W (u, v)) * F v := by
        rw [hTonelli]
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
        exact lintegral_mul_const'' _ (hWs v hv)
      _ ≤ ∫⁻ v in Ioo (0 : ℝ) 1, Y * F v := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
        exact mul_le_mul_of_nonneg_right (hmajor v hv) bot_le
      _ = Y * (∫⁻ v in Ioo (0 : ℝ) 1, F v) :=
        lintegral_const_mul'' _ hF.aemeasurable
      _ ≤ Y * (D + A) :=
        mul_le_mul_of_nonneg_left hFintegral bot_le
  calc
    (∫⁻ p in T, J p) ≤
        ∫⁻ p in T, c * (W p * F p.2) + d * K p := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (by
        change MeasurableSet (openCoordTriangle 0 1)
        rw [← interior_closedCoordTriangle]
        exact isOpen_interior.measurableSet)] with p hp
      exact hpoint p hp
    _ = c * (∫⁻ p in T, W p * F p.2) +
        d * (∫⁻ p in T, K p) := by
      rw [lintegral_add_left' hCW (fun p => d * K p),
        lintegral_const_mul'' _ hWF,
        lintegral_const_mul'' _ hK]
    _ ≤ c * (Y * (D + A)) + d * A := by
      rw [hKintegral]
      exact add_le_add (mul_le_mul_of_nonneg_left hWFbound bot_le) le_rfl

/-- The same weighted estimate with outgoing segments as the inner fibers. -/
theorem scalar_area_weighted_bound_outgoing
    (W J K : ℝ × ℝ → ℝ≥0∞) (F : ℝ → ℝ≥0∞)
    (c d X D A : ℝ≥0∞)
    (hW : AEMeasurable W
      (volume.restrict (openCoordTriangle 0 1)))
    (hF : Measurable F)
    (hK : AEMeasurable K
      (volume.restrict (openCoordTriangle 0 1)))
    (hWs : ∀ u ∈ Ioo (0 : ℝ) 1,
      AEMeasurable (fun v => W (u, v))
        (volume.restrict (Ioo u 1)))
    (hmajor : ∀ u ∈ Ioo (0 : ℝ) 1,
      (∫⁻ v in Ioo u 1, W (u, v)) ≤ X)
    (hpoint : ∀ p ∈ openCoordTriangle 0 1,
      J p ≤ c * (W p * F p.1) + d * K p)
    (hFintegral : (∫⁻ u in Ioo (0 : ℝ) 1, F u) ≤ D + A)
    (hKintegral : (∫⁻ p in openCoordTriangle 0 1, K p) = A) :
    (∫⁻ p in openCoordTriangle 0 1, J p) ≤
      c * (X * (D + A)) + d * A := by
  let T := openCoordTriangle 0 1
  have hFfst : AEMeasurable (fun p : ℝ × ℝ => F p.1)
      (volume.restrict T) :=
    (hF.comp measurable_fst).aemeasurable
  have hWF : AEMeasurable (fun p : ℝ × ℝ => W p * F p.1)
      (volume.restrict T) := hW.mul hFfst
  have hCW : AEMeasurable (fun p : ℝ × ℝ => c * (W p * F p.1))
      (volume.restrict T) := aemeasurable_const.mul hWF
  have hTonelli : (∫⁻ p in T, W p * F p.1) =
      ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo u 1, W (u, v) * F u := by
    simpa only [triangle_carrier_eq, T] using
      (lintegral_open_triangle 0 1 _
        (by simpa only [triangle_carrier_eq, T] using hWF))
  have hWFbound : (∫⁻ p in T, W p * F p.1) ≤
      X * (D + A) := by
    calc
      (∫⁻ p in T, W p * F p.1) =
          ∫⁻ u in Ioo (0 : ℝ) 1,
            (∫⁻ v in Ioo u 1, W (u, v)) * F u := by
        rw [hTonelli]
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        exact lintegral_mul_const'' _ (hWs u hu)
      _ ≤ ∫⁻ u in Ioo (0 : ℝ) 1, X * F u := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        exact mul_le_mul_of_nonneg_right (hmajor u hu) bot_le
      _ = X * (∫⁻ u in Ioo (0 : ℝ) 1, F u) :=
        lintegral_const_mul'' _ hF.aemeasurable
      _ ≤ X * (D + A) :=
        mul_le_mul_of_nonneg_left hFintegral bot_le
  calc
    (∫⁻ p in T, J p) ≤
        ∫⁻ p in T, c * (W p * F p.1) + d * K p := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (by
        change MeasurableSet (openCoordTriangle 0 1)
        rw [← interior_closedCoordTriangle]
        exact isOpen_interior.measurableSet)] with p hp
      exact hpoint p hp
    _ = c * (∫⁻ p in T, W p * F p.1) +
        d * (∫⁻ p in T, K p) := by
      rw [lintegral_add_left' hCW (fun p => d * K p),
        lintegral_const_mul'' _ hWF,
        lintegral_const_mul'' _ hK]
    _ ≤ c * (X * (D + A)) + d * A := by
      rw [hKintegral]
      exact add_le_add (mul_le_mul_of_nonneg_left hWFbound bot_le) le_rfl

end ChristodoulouBV

end
