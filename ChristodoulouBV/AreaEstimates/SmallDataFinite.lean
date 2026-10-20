module

public import ChristodoulouBV.AreaEstimates.IncomingArea
public import ChristodoulouBV.AreaEstimates.OutgoingArea
public import ChristodoulouBV.AreaEstimates.ScalarArea
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Finiteness of the four Section 4 analytic areas

The small-data absorption takes place in `ℝ≥0∞`. Its cancellation steps
require finite Jacobian areas. Compact `C¹` regularity on the closed unit
triangle supplies this fact before any absorption.
-/

public section

open Set MeasureTheory
open scoped ENNReal Topology

namespace ChristodoulouBV

/-- A `C¹` planar map on the closed unit triangle has finite smooth analytic
area on the open triangle. -/
theorem smoothAnalyticArea_unit_ne_top {F : ℝ × ℝ → ℝ × ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 1)) :
    smoothAnalyticArea F (openCoordTriangle 0 1) ≠ ∞ := by
  let K := closedCoordTriangle (0 : ℝ) 1
  let E := openCoordTriangle (0 : ℝ) 1
  have hEopen : IsOpen E := by
    change IsOpen (openCoordTriangle 0 1)
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior
  have hEsub : E ⊆ K := by
    change openCoordTriangle 0 1 ⊆ closedCoordTriangle 0 1
    rw [← interior_closedCoordTriangle]
    exact interior_subset
  have hUnique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 1)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty (by norm_num))
  have hWithin : ContinuousOn (fderivWithin ℝ F K) K :=
    hF.continuousOn_fderivWithin hUnique (by norm_num)
  have hDet : ContinuousOn (fun p => |(fderivWithin ℝ F K p).det|) K :=
    (ContinuousLinearMap.continuous_det.comp_continuousOn hWithin).abs
  have hEfinite : volume E ≠ ∞ :=
    ne_top_of_le_ne_top (isCompact_closedCoordTriangle 0 1).measure_ne_top
      (measure_mono hEsub)
  have hInt : IntegrableOn (fun p => |(fderivWithin ℝ F K p).det|) E volume :=
    hDet.integrableOn_of_subset_isCompact
      (isCompact_closedCoordTriangle 0 1) hEopen.measurableSet hEsub hEfinite
  have hEq : (∫⁻ p in E, ENNReal.ofReal |(fderiv ℝ F p).det|) =
      ∫⁻ p in E, ENNReal.ofReal |(fderivWithin ℝ F K p).det| := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hEopen.measurableSet] with p hp
    have hKn : K ∈ 𝓝 p := by
      apply Filter.mem_of_superset (hEopen.mem_nhds hp) hEsub
    rw [fderivWithin_of_mem_nhds hKn]
  rw [smooth_analytic_area F hEopen.measurableSet, hEq]
  exact hInt.setLIntegral_lt_top.ne

/-- The four analytic areas in the coupled Section 4 inequalities are finite
before their self-terms are absorbed. -/
theorem s4_four_areas_ne_top {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hboot : s4_bootstrap S) :
    smoothAnalyticArea (sourcePhiAlphaLamMap S) (openCoordTriangle 0 1) ≠ ∞ ∧
    smoothAnalyticArea (sourcePhiBetaNuMap S) (openCoordTriangle 0 1) ≠ ∞ ∧
    smoothAnalyticArea (sourceLamPhiMap S) (openCoordTriangle 0 1) ≠ ∞ ∧
    smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 1) ≠ ∞ := by
  let K := closedCoordTriangle (0 : ℝ) 1
  let E := openCoordTriangle (0 : ℝ) 1
  have hclosure : closure E = K := closure_openCoordTriangle (by norm_num)
  obtain ⟨hlam, hnu, hphi, halpha, hbeta⟩ := unit_field_contDiffOn H
  have hEsub : E ⊆ K := by
    change openCoordTriangle 0 1 ⊆ closedCoordTriangle 0 1
    rw [← interior_closedCoordTriangle]
    exact interior_subset
  have hlamLower : ∀ p ∈ K, (1 / 3 : ℝ) ≤ S.lam p.1 p.2 := by
    intro p hp
    rw [← hclosure] at hp
    apply le_on_closure (s := E) (f := fun _ => (1 / 3 : ℝ))
      (g := fun q => S.lam q.1 q.2) ?_ continuousOn_const
      (hclosure ▸ hlam.continuousOn) hp
    intro q hq
    exact hboot.1 q ⟨hq.1.le, hq.2.1, hq.2.2⟩
  have hnuUpper : ∀ p ∈ K, S.nu p.1 p.2 ≤ -(1 / 3 : ℝ) := by
    intro p hp
    rw [← hclosure] at hp
    apply le_on_closure (s := E) (f := fun q => S.nu q.1 q.2)
      (g := fun _ => -(1 / 3 : ℝ)) ?_
      (hclosure ▸ hnu.continuousOn) continuousOn_const hp
    intro q hq
    exact sourceNu_le_neg_third H hboot hq
  have hlamNe : ∀ p ∈ K, S.lam p.1 p.2 ≠ 0 := by
    intro p hp
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) (hlamLower p hp))
  have hnuNe : ∀ p ∈ K, S.nu p.1 p.2 ≠ 0 := by
    intro p hp
    exact ne_of_lt (lt_of_le_of_lt (hnuUpper p hp) (by norm_num))
  have hAlphaMap : ContDiffOn ℝ 1 (sourcePhiAlphaLamMap S) K :=
    hphi.prodMk (halpha.div hlam hlamNe)
  have hBetaMap : ContDiffOn ℝ 1 (sourcePhiBetaNuMap S) K :=
    hphi.prodMk (hbeta.div hnu hnuNe)
  exact ⟨smoothAnalyticArea_unit_ne_top hAlphaMap,
    smoothAnalyticArea_unit_ne_top hBetaMap,
    smoothAnalyticArea_unit_ne_top (sourceLamPhiMap_contDiffOn H),
    smoothAnalyticArea_unit_ne_top (sourceNuPhiMap_contDiffOn H)⟩

end ChristodoulouBV

end
