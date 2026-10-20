module

public import ChristodoulouBV.AreaEstimates.OutgoingAreaPointwise
public import ChristodoulouBV.AreaEstimates.ScalarAreaWeighted
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Triangular weighting with a separate rho area

These Tonelli inequalities separate the logarithmic majorant area from the
remaining rho density. The rho multiplier is finite, so its lower integral
does not require a separate global measurability assumption.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace ChristodoulouBV

private theorem outgoing_area_triangle_carrier :
    {p : ℝ × ℝ | p.1 ∈ Ioo 0 1 ∧ p.2 ∈ Ioo p.1 1} =
      openCoordTriangle 0 1 := by
  ext p
  simp only [openCoordTriangle, mem_ofPred_eq, mem_Ioo]
  constructor
  · rintro ⟨⟨h0, _⟩, ⟨huv, hv⟩⟩
    exact ⟨h0, huv, hv⟩
  · rintro ⟨h0, huv, hv⟩
    exact ⟨⟨h0, huv.trans hv⟩, ⟨huv, hv⟩⟩

/-- The weighted area estimate with incoming characteristic fibers and an
independent remainder area. -/
theorem outgoing_area_weighted_incoming
    (W J K : ℝ × ℝ → ℝ≥0∞) (F : ℝ → ℝ≥0∞)
    (c d Y M R : ℝ≥0∞)
    (hW : AEMeasurable W
      (volume.restrict (openCoordTriangle 0 1)))
    (hF : AEMeasurable F (volume.restrict (Ioo (0 : ℝ) 1)))
    (hd : d ≠ ∞)
    (hWs : ∀ v ∈ Ioo (0 : ℝ) 1,
      AEMeasurable (fun u => W (u, v)) (volume.restrict (Ioo 0 v)))
    (hmajor : ∀ v ∈ Ioo (0 : ℝ) 1,
      (∫⁻ u in Ioo 0 v, W (u, v)) ≤ Y)
    (hpoint : ∀ p ∈ openCoordTriangle 0 1,
      J p ≤ c * (W p * F p.2) + d * K p)
    (hFintegral : (∫⁻ v in Ioo (0 : ℝ) 1, F v) ≤ M)
    (hKintegral : (∫⁻ p in openCoordTriangle 0 1, K p) = R) :
    (∫⁻ p in openCoordTriangle 0 1, J p) ≤ c * (Y * M) + d * R := by
  let T := openCoordTriangle 0 1
  have hTsub : T ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
    intro p hp
    exact ⟨⟨hp.1, hp.2.1.trans hp.2.2⟩,
      ⟨hp.1.trans hp.2.1, hp.2.2⟩⟩
  have hmeasure : volume.restrict T ≤
      (volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]
    exact Measure.restrict_mono hTsub le_rfl
  have hFsnd : AEMeasurable (fun p : ℝ × ℝ => F p.2)
      (volume.restrict T) :=
    (AEMeasurable.comp_snd hF).mono_measure hmeasure
  have hWF : AEMeasurable (fun p : ℝ × ℝ => W p * F p.2)
      (volume.restrict T) := hW.mul hFsnd
  have hCW : AEMeasurable (fun p : ℝ × ℝ => c * (W p * F p.2))
      (volume.restrict T) := aemeasurable_const.mul hWF
  have hTonelli : (∫⁻ p in T, W p * F p.2) =
      ∫⁻ v in Ioo (0 : ℝ) 1, ∫⁻ u in Ioo 0 v, W (u, v) * F v := by
    simpa only [outgoing_area_triangle_carrier, T] using
      (lintegral_open_triangle_swap 0 1 _
        (by simpa only [outgoing_area_triangle_carrier, T] using hWF))
  have hWFbound : (∫⁻ p in T, W p * F p.2) ≤ Y * M := by
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
        lintegral_const_mul'' _ hF
      _ ≤ Y * M := mul_le_mul_of_nonneg_left hFintegral bot_le
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
        lintegral_const_mul' _ _ hd]
    _ ≤ c * (Y * M) + d * R := by
      rw [hKintegral]
      exact add_le_add (mul_le_mul_of_nonneg_left hWFbound bot_le) le_rfl

/-- The matching weighted estimate with outgoing characteristic fibers. -/
theorem outgoing_area_weighted_outgoing
    (W J K : ℝ × ℝ → ℝ≥0∞) (F : ℝ → ℝ≥0∞)
    (c d X M R : ℝ≥0∞)
    (hW : AEMeasurable W
      (volume.restrict (openCoordTriangle 0 1)))
    (hF : AEMeasurable F (volume.restrict (Ioo (0 : ℝ) 1)))
    (hd : d ≠ ∞)
    (hWs : ∀ u ∈ Ioo (0 : ℝ) 1,
      AEMeasurable (fun v => W (u, v)) (volume.restrict (Ioo u 1)))
    (hmajor : ∀ u ∈ Ioo (0 : ℝ) 1,
      (∫⁻ v in Ioo u 1, W (u, v)) ≤ X)
    (hpoint : ∀ p ∈ openCoordTriangle 0 1,
      J p ≤ c * (W p * F p.1) + d * K p)
    (hFintegral : (∫⁻ u in Ioo (0 : ℝ) 1, F u) ≤ M)
    (hKintegral : (∫⁻ p in openCoordTriangle 0 1, K p) = R) :
    (∫⁻ p in openCoordTriangle 0 1, J p) ≤ c * (X * M) + d * R := by
  let T := openCoordTriangle 0 1
  have hTsub : T ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
    intro p hp
    exact ⟨⟨hp.1, hp.2.1.trans hp.2.2⟩,
      ⟨hp.1.trans hp.2.1, hp.2.2⟩⟩
  have hmeasure : volume.restrict T ≤
      (volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]
    exact Measure.restrict_mono hTsub le_rfl
  have hFfst : AEMeasurable (fun p : ℝ × ℝ => F p.1)
      (volume.restrict T) :=
    (AEMeasurable.comp_fst hF).mono_measure hmeasure
  have hWF : AEMeasurable (fun p : ℝ × ℝ => W p * F p.1)
      (volume.restrict T) := hW.mul hFfst
  have hCW : AEMeasurable (fun p : ℝ × ℝ => c * (W p * F p.1))
      (volume.restrict T) := aemeasurable_const.mul hWF
  have hTonelli : (∫⁻ p in T, W p * F p.1) =
      ∫⁻ u in Ioo (0 : ℝ) 1, ∫⁻ v in Ioo u 1, W (u, v) * F u := by
    simpa only [outgoing_area_triangle_carrier, T] using
      (lintegral_open_triangle 0 1 _
        (by simpa only [outgoing_area_triangle_carrier, T] using hWF))
  have hWFbound : (∫⁻ p in T, W p * F p.1) ≤ X * M := by
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
        lintegral_const_mul'' _ hF
      _ ≤ X * M := mul_le_mul_of_nonneg_left hFintegral bot_le
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
        lintegral_const_mul' _ _ hd]
    _ ≤ c * (X * M) + d * R := by
      rw [hKintegral]
      exact add_le_add (mul_le_mul_of_nonneg_left hWFbound bot_le) le_rfl

end ChristodoulouBV

end
