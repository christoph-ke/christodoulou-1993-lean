module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesSafeMesh
import Mathlib.Tactic

/-!
# Uniform vector-field bounds along the terminal base

All radius-`δ` boxes centered on a compact continuous terminal base lie in
one compact set of safe states. The rational rectangle vector fields and
their derivatives are therefore bounded uniformly across those boxes.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

private theorem SafeRectangleBox.valueBound_le_of_bounds
    (B : SafeRectangleBox) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ z ∈ B.carrier, ‖rectangleF z‖ ≤ C)
    (hG : ∀ z ∈ B.carrier, ‖rectangleG z‖ ≤ C) :
    B.valueBound ≤ C := by
  have hneF : ((fun z => ‖rectangleF z‖) '' B.carrier).Nonempty := by
    refine ⟨‖rectangleF B.center‖, B.center, ?_, rfl⟩
    change B.center ∈ Metric.closedBall B.center B.radius
    exact Metric.mem_closedBall_self B.radius_pos.le
  have hneG : ((fun z => ‖rectangleG z‖) '' B.carrier).Nonempty := by
    refine ⟨‖rectangleG B.center‖, B.center, ?_, rfl⟩
    change B.center ∈ Metric.closedBall B.center B.radius
    exact Metric.mem_closedBall_self B.radius_pos.le
  change max 0 (max (sSup ((fun z => ‖rectangleF z‖) '' B.carrier))
    (sSup ((fun z => ‖rectangleG z‖) '' B.carrier))) ≤ C
  apply max_le hC
  apply max_le
  · exact csSup_le hneF (by rintro x ⟨z, hz, rfl⟩; exact hF z hz)
  · exact csSup_le hneG (by rintro x ⟨z, hz, rfl⟩; exact hG z hz)

private theorem SafeRectangleBox.derivBound_le_of_bounds
    (B : SafeRectangleBox) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ z ∈ B.carrier, ‖fderiv ℝ rectangleF z‖ ≤ C)
    (hG : ∀ z ∈ B.carrier, ‖fderiv ℝ rectangleG z‖ ≤ C) :
    (B.derivBound : ℝ) ≤ C := by
  have hneF : ((fun z => ‖fderiv ℝ rectangleF z‖) '' B.carrier).Nonempty := by
    refine ⟨‖fderiv ℝ rectangleF B.center‖, B.center, ?_, rfl⟩
    change B.center ∈ Metric.closedBall B.center B.radius
    exact Metric.mem_closedBall_self B.radius_pos.le
  have hneG : ((fun z => ‖fderiv ℝ rectangleG z‖) '' B.carrier).Nonempty := by
    refine ⟨‖fderiv ℝ rectangleG B.center‖, B.center, ?_, rfl⟩
    change B.center ∈ Metric.closedBall B.center B.radius
    exact Metric.mem_closedBall_self B.radius_pos.le
  change max 0 (max (sSup ((fun z => ‖fderiv ℝ rectangleF z‖) '' B.carrier))
    (sSup ((fun z => ‖fderiv ℝ rectangleG z‖) '' B.carrier))) ≤ C
  apply max_le hC
  apply max_le
  · exact csSup_le hneF (by rintro x ⟨z, hz, rfl⟩; exact hF z hz)
  · exact csSup_le hneG (by rintro x ⟨z, hz, rfl⟩; exact hG z hz)

end ChristodoulouBV.C1Solution

namespace ChristodoulouBV.Uniqueness

/-- Every radius-`δ` safe box centered on a compact continuous base has
one common bound for both rectangle vector fields and their first
derivatives. -/
theorem LowerCoverBaseData.exists_uniform_safe_box_bounds
    {a vStar L δ : ℝ} (D : LowerCoverBaseData a vStar L)
    (hboxes : ∀ t ∈ Icc 0 a,
      ∃ B : C1Solution.SafeRectangleBox,
        B.center = D.base t ∧ B.radius = δ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Icc 0 a, ∀ B : C1Solution.SafeRectangleBox,
        B.center = D.base t → B.radius = δ →
          B.valueBound ≤ C ∧ (B.derivBound : ℝ) ≤ C := by
  let U : Set (ℝ × C1Solution.RectangleState) :=
    Icc 0 a ×ˢ Metric.closedBall 0 δ
  let H : ℝ × C1Solution.RectangleState → C1Solution.RectangleState :=
    fun p => D.base p.1 + p.2
  let K : Set C1Solution.RectangleState := H '' U
  have hH : Continuous H :=
    (D.base_cont.comp continuous_fst).add continuous_snd
  have hK : IsCompact K :=
    ((isCompact_Icc : IsCompact (Icc 0 a)).prod
      (isCompact_closedBall (0 : C1Solution.RectangleState) δ)).image hH
  have hsafe : ∀ z ∈ K, C1Solution.IsSafeRectangleState z := by
    intro z hz
    obtain ⟨⟨t, w⟩, ⟨ht, hw⟩, rfl⟩ := hz
    obtain ⟨B, hcenter, hradius⟩ := hboxes t ht
    apply B.safe
    change D.base t + w ∈ Metric.closedBall B.center B.radius
    rw [hcenter, hradius]
    apply Metric.mem_closedBall.mpr
    have hnorm : ‖w‖ ≤ δ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    simpa only [dist_eq_norm, add_sub_cancel_left] using hnorm
  have hF : ContinuousOn C1Solution.rectangleF K := by
    intro z hz
    exact (C1Solution.contDiffAt_rectangleF (hsafe z hz)).continuousAt.continuousWithinAt
  have hG : ContinuousOn C1Solution.rectangleG K := by
    intro z hz
    exact (C1Solution.contDiffAt_rectangleG (hsafe z hz)).continuousAt.continuousWithinAt
  have hDF : ContinuousOn (fderiv ℝ C1Solution.rectangleF) K := by
    intro z hz
    exact ((C1Solution.contDiffAt_rectangleF (hsafe z hz))
      |>.continuousAt_fderiv (by decide)).continuousWithinAt
  have hDG : ContinuousOn (fderiv ℝ C1Solution.rectangleG) K := by
    intro z hz
    exact ((C1Solution.contDiffAt_rectangleG (hsafe z hz))
      |>.continuousAt_fderiv (by decide)).continuousWithinAt
  obtain ⟨CF, hCF⟩ := hK.exists_bound_of_continuousOn hF
  obtain ⟨CG, hCG⟩ := hK.exists_bound_of_continuousOn hG
  obtain ⟨CDF, hCDF⟩ := hK.exists_bound_of_continuousOn hDF
  obtain ⟨CDG, hCDG⟩ := hK.exists_bound_of_continuousOn hDG
  let C := max 0 (max CF (max CG (max CDF CDG)))
  have hC : 0 ≤ C := le_max_left _ _
  refine ⟨C, hC, ?_⟩
  intro t ht B hcenter hradius
  have hcarrier : B.carrier ⊆ K := by
    intro z hz
    refine ⟨(t, z - D.base t), ?_, ?_⟩
    · refine ⟨ht, ?_⟩
      apply Metric.mem_closedBall.mpr
      have hdist : dist z (D.base t) ≤ δ := by
        have hz' : dist z B.center ≤ B.radius := by
          simpa only [C1Solution.SafeRectangleBox.carrier,
            Metric.mem_closedBall] using hz
        simpa only [hcenter, hradius] using hz'
      simpa only [dist_zero_right, dist_eq_norm, sub_zero] using hdist
    · change D.base t + (z - D.base t) = z
      abel
  have hCF' : CF ≤ C :=
    le_max_of_le_right (le_max_left _ _)
  have hCG' : CG ≤ C :=
    le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hCDF' : CDF ≤ C :=
    le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _)))
  have hCDG' : CDG ≤ C :=
    le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_right _ _)))
  constructor
  · apply C1Solution.SafeRectangleBox.valueBound_le_of_bounds B hC
    · intro z hz
      exact (hCF z (hcarrier hz)).trans hCF'
    · intro z hz
      exact (hCG z (hcarrier hz)).trans hCG'
  · apply C1Solution.SafeRectangleBox.derivBound_le_of_bounds B hC
    · intro z hz
      exact (hCDF z (hcarrier hz)).trans hCDF'
    · intro z hz
      exact (hCDG z (hcarrier hz)).trans hCDG'

end ChristodoulouBV.Uniqueness

end
