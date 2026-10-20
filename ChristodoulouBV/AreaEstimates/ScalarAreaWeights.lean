module

public import ChristodoulouBV.AreaEstimates.ScalarAreaMeasurable
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Null weights in the scalar area estimates

The canonical radius is C¹ on the closed unit triangle and equals the actual
radius at strict points. It supplies measurable versions of the two null
weights used in (4.16) and (4.18).
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal Topology

namespace ChristodoulouBV

/-- The canonical radius has a continuous first jet on the closed unit
triangle, even though the frozen total radius is only specified off axis. -/
theorem sourceCanonicalRadius_contDiffOn {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    ContDiffOn ℝ 1 (C1Solution.canonicalRadius S)
      (closedCoordTriangle 0 1) := by
  exact C1Solution.weightedDiagonalRadius_contDiffOn (by norm_num)
    (unit_field_contDiffOn H).1

/-- On the strict unit triangle the canonical radius is the solution radius. -/
theorem sourceCanonicalRadius_eq_radius {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    C1Solution.canonicalRadius S (u, v) = S.r u v := by
  let B : ℝ := (v + 1) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < 1 := by dsimp [B]; linarith
  have hvB : v ≤ B := by dsimp [B]; linarith
  exact C1Solution.canonicalRadius_eq_radius hB hBb H hu.le huv hvB

/-- The incoming fiber weight `|ζ|/r`, represented using the canonical
radius so it is measurable on the whole open triangle. -/
noncomputable def sourceIncomingWeight (S : Fields) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (|S.zeta p.1 p.2| / C1Solution.canonicalRadius S p)

/-- The outgoing fiber weight `|θ|/r`. -/
noncomputable def sourceOutgoingWeight (S : Fields) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (|S.theta p.1 p.2| / C1Solution.canonicalRadius S p)

private theorem strict_triangle_measurable :
    MeasurableSet (openCoordTriangle (0 : ℝ) 1) := by
  rw [← interior_closedCoordTriangle]
  exact isOpen_interior.measurableSet

private theorem strict_triangle_subset_closed :
    openCoordTriangle (0 : ℝ) 1 ⊆ closedCoordTriangle 0 1 := by
  intro p hp
  exact ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩

private theorem sourceIncomingWeight_continuousOn {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    ContinuousOn (sourceIncomingWeight S) (openCoordTriangle 0 1) := by
  let T := openCoordTriangle 0 1
  have hzeta : ContinuousOn (fun p : ℝ × ℝ => S.zeta p.1 p.2) T :=
    (C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
      (by norm_num : (0 : ℝ) < 1) ▸ H.zeta_c1).continuousOn.mono
        strict_triangle_subset_closed
  have hr : ContinuousOn (C1Solution.canonicalRadius S) T :=
    (sourceCanonicalRadius_contDiffOn H).continuousOn.mono
      strict_triangle_subset_closed
  have hrne : ∀ p ∈ T, C1Solution.canonicalRadius S p ≠ 0 := by
    intro p hp
    rw [sourceCanonicalRadius_eq_radius H hp.1 hp.2.1 hp.2.2]
    exact ne_of_gt (H.solution.radius_pos p ⟨hp.1.le, hp.2.1, hp.2.2⟩)
  exact ENNReal.continuous_ofReal.comp_continuousOn
    (hzeta.abs.div hr hrne)

private theorem sourceOutgoingWeight_continuousOn {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    ContinuousOn (sourceOutgoingWeight S) (openCoordTriangle 0 1) := by
  let T := openCoordTriangle 0 1
  have htheta : ContinuousOn (fun p : ℝ × ℝ => S.theta p.1 p.2) T :=
    (C1Solution.closure_developmentWithInitialEdge_eq_closedCoordTriangle
      (by norm_num : (0 : ℝ) < 1) ▸ H.theta_c1).continuousOn.mono
        strict_triangle_subset_closed
  have hr : ContinuousOn (C1Solution.canonicalRadius S) T :=
    (sourceCanonicalRadius_contDiffOn H).continuousOn.mono
      strict_triangle_subset_closed
  have hrne : ∀ p ∈ T, C1Solution.canonicalRadius S p ≠ 0 := by
    intro p hp
    rw [sourceCanonicalRadius_eq_radius H hp.1 hp.2.1 hp.2.2]
    exact ne_of_gt (H.solution.radius_pos p ⟨hp.1.le, hp.2.1, hp.2.2⟩)
  exact ENNReal.continuous_ofReal.comp_continuousOn
    (htheta.abs.div hr hrne)

/-- The incoming canonical weight has the measurability and fiber bounds
required by the triangular Tonelli estimate. -/
theorem sourceIncomingWeight_fibers {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    AEMeasurable (sourceIncomingWeight S)
      (volume.restrict (openCoordTriangle 0 1)) ∧
    (∀ v ∈ Ioo (0 : ℝ) 1,
      AEMeasurable (fun u => sourceIncomingWeight S (u, v))
        (volume.restrict (Ioo 0 v))) ∧
    (∀ v ∈ Ioo (0 : ℝ) 1,
      (∫⁻ u in Ioo 0 v, sourceIncomingWeight S (u, v)) ≤ sourceY S) := by
  have hcont := sourceIncomingWeight_continuousOn H
  refine ⟨hcont.aemeasurable strict_triangle_measurable, ?_, ?_⟩
  · intro v hv
    have hline : Continuous (fun u : ℝ => (u, v)) :=
      continuous_id.prodMk continuous_const
    have hmap : MapsTo (fun u : ℝ => (u, v)) (Ioo 0 v)
        (openCoordTriangle 0 1) := by
      intro u hu
      exact ⟨hu.1, hu.2, hv.2⟩
    exact (hcont.comp hline.continuousOn hmap).aemeasurable measurableSet_Ioo
  · intro v hv
    have heq : EqOn (fun u => sourceIncomingWeight S (u, v))
        (fun u => ENNReal.ofReal (|S.zeta u v| / S.r u v)) (Ioo 0 v) := by
      intro u hu
      change ENNReal.ofReal
        (|S.zeta u v| / C1Solution.canonicalRadius S (u, v)) = _
      rw [sourceCanonicalRadius_eq_radius H hu.1 hu.2 hv.2]
    have hInt : (∫⁻ u in Ioo 0 v, sourceIncomingWeight S (u, v)) =
        ∫⁻ u in Ioo 0 v, ENNReal.ofReal (|S.zeta u v| / S.r u v) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact heq hu
    rw [hInt, sourceY]
    exact le_iSup_of_le v (le_iSup_of_le hv le_rfl)

/-- The outgoing canonical weight has the corresponding outgoing fibers. -/
theorem sourceOutgoingWeight_fibers {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    AEMeasurable (sourceOutgoingWeight S)
      (volume.restrict (openCoordTriangle 0 1)) ∧
    (∀ u ∈ Ioo (0 : ℝ) 1,
      AEMeasurable (fun v => sourceOutgoingWeight S (u, v))
        (volume.restrict (Ioo u 1))) ∧
    (∀ u ∈ Ioo (0 : ℝ) 1,
      (∫⁻ v in Ioo u 1, sourceOutgoingWeight S (u, v)) ≤ sourceX S) := by
  have hcont := sourceOutgoingWeight_continuousOn H
  refine ⟨hcont.aemeasurable strict_triangle_measurable, ?_, ?_⟩
  · intro u hu
    have hline : Continuous (fun v : ℝ => (u, v)) :=
      continuous_const.prodMk continuous_id
    have hmap : MapsTo (fun v : ℝ => (u, v)) (Ioo u 1)
        (openCoordTriangle 0 1) := by
      intro v hv
      exact ⟨hu.1, hv.1, hv.2⟩
    exact (hcont.comp hline.continuousOn hmap).aemeasurable measurableSet_Ioo
  · intro u hu
    have heq : EqOn (fun v => sourceOutgoingWeight S (u, v))
        (fun v => ENNReal.ofReal (|S.theta u v| / S.r u v)) (Ioo u 1) := by
      intro v hv
      change ENNReal.ofReal
        (|S.theta u v| / C1Solution.canonicalRadius S (u, v)) = _
      rw [sourceCanonicalRadius_eq_radius H hu.1 hv.1 hv.2]
    have hInt : (∫⁻ v in Ioo u 1, sourceOutgoingWeight S (u, v)) =
        ∫⁻ v in Ioo u 1, ENNReal.ofReal (|S.theta u v| / S.r u v) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
      exact heq hv
    rw [hInt, sourceX]
    exact le_iSup_of_le u (le_iSup_of_le hu le_rfl)

end ChristodoulouBV

end
