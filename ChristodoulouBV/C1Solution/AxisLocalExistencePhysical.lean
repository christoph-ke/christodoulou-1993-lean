module

public import ChristodoulouBV.C1Solution.AxisLocalExistenceGeneralEdgeBounds
public import ChristodoulouBV.C1Solution.AxisLocalExistenceScaling
public import ChristodoulouBV.C1Solution.AxisLocalExistenceNormalizedClassical
public import ChristodoulouBV.C1Solution.AxisLocalExistenceSystemScaling
import Mathlib.Tactic

/-!
# Physical fields from a positive incoming edge

The normalized Picard reconstruction is returned to the physical radial
scale. This module records its regularity, signs, axis values, and exact
incoming trace before converting relative jets to classical equations.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

open ChristodoulouBV.C1Solution

/-- Positive global `C¹` edge expansion and scalar amplitude give physical
fields on a short axis triangle. Their incoming trace is unscaled. -/
theorem exists_physical_reconstructed_edge {a L : ℝ} {g hEdge : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 hEdge)
    (hga : 0 < g a) (hL : 0 < L) :
    ∃ k b : ℝ, 0 < k ∧ a < b ∧ b ≤ a + L ∧ k * g a = 1 / 2 ∧
      ∃ T : Fields,
      let K := closedCoordTriangle a b
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.r p.1 p.2) K ∧
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.phi p.1 p.2) K ∧
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.m p.1 p.2) K ∧
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.lam p.1 p.2) K ∧
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.nu p.1 p.2) K ∧
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.alpha p.1 p.2) K ∧
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => T.beta p.1 p.2) K ∧
      (∀ p ∈ K, 1 / (4 * k) ≤ T.lam p.1 p.2 ∧
        -(3 / (4 * k)) ≤ T.nu p.1 p.2 ∧
        T.nu p.1 p.2 ≤ -(1 / (4 * k)) ∧
        0 ≤ 2 * T.m p.1 p.2 / T.r p.1 p.2 ∧
        2 * T.m p.1 p.2 / T.r p.1 p.2 ≤ 1 / 4) ∧
      (∀ u ∈ Icc a b, T.r u u = 0 ∧ T.m u u = 0) ∧
      (∀ v ∈ Icc a b,
        T.r a v = ∫ s in a..v, g s ∧
        T.lam a v = g v ∧ T.alpha a v = g v * hEdge v) ∧
      AxisClassicalSolution a b T := by
  obtain ⟨k, b, M, hk, hab, hbL, hM, hka, hsmall, hglo, x, hfixed⟩ :=
    exists_normalized_reconstructed_edge_with_lower hg hh hga hL
  let S := x.1.toTriple.toFields
  let T := physicalScaleFields (1 / k) S
  have hkne : k ≠ 0 := ne_of_gt hk
  have hc : 0 < 1 / k := one_div_pos.mpr hk
  have hbasic := x.reconstructed_fields_basic hab hM hsmall hglo
  dsimp only at hbasic
  rcases hbasic with
    ⟨hr, hphi, hm, hlam, hnu, halpha, hbeta, hsign, haxis⟩
  refine ⟨k, b, hk, hab, hbL, hka, T, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiffOn_const.mul hr
  · exact hphi
  · exact contDiffOn_const.mul hm
  · exact contDiffOn_const.mul hlam
  · exact contDiffOn_const.mul hnu
  · exact contDiffOn_const.mul halpha
  · exact contDiffOn_const.mul hbeta
  · intro p hp
    obtain ⟨hl, hnlo, hnhi, hmlo, hmhi⟩ := hsign p hp
    have hrati := physicalScaleFields_massRatio (1 / k) S p.1 p.2
      (one_div_ne_zero hkne)
    change 2 * T.m p.1 p.2 / T.r p.1 p.2 =
      2 * S.m p.1 p.2 / S.r p.1 p.2 at hrati
    change (1 / 4 : ℝ) ≤ S.lam p.1 p.2 at hl
    change -(3 / 4 : ℝ) ≤ S.nu p.1 p.2 at hnlo
    change S.nu p.1 p.2 ≤ -(1 / 4 : ℝ) at hnhi
    simp only [T, physicalScaleFields]
    have hrati' : 2 * (1 / k * S.m p.1 p.2) /
        (1 / k * S.r p.1 p.2) =
        2 * S.m p.1 p.2 / S.r p.1 p.2 := by
      simpa only [T, physicalScaleFields] using hrati
    rw [hrati']
    constructor
    · have h := mul_le_mul_of_nonneg_left hl hc.le
      have hf : (1 / k) * (1 / 4 : ℝ) = 1 / (4 * k) := by
        field_simp [hkne]
      rw [← hf]
      exact h
    constructor
    · have h := mul_le_mul_of_nonneg_left hnlo hc.le
      have hf : (1 / k) * (-(3 / 4 : ℝ)) = -(3 / (4 * k)) := by
        field_simp [hkne]
      rw [← hf]
      exact h
    constructor
    · have h := mul_le_mul_of_nonneg_left hnhi hc.le
      have hf : (1 / k) * (-(1 / 4 : ℝ)) = -(1 / (4 * k)) := by
        field_simp [hkne]
      rw [← hf]
      exact h
    exact ⟨hmlo, hmhi⟩
  · intro u hu
    obtain ⟨hru, hmu⟩ := haxis u hu
    change S.r u u = 0 at hru
    change S.m u u = 0 at hmu
    exact ⟨by simp [T, physicalScaleFields, hru],
      by simp [T, physicalScaleFields, hmu]⟩
  · intro v hv
    obtain ⟨hrv, hlv, hav⟩ := x.reconstructed_edge_trace hv
    change S.r a v = ∫ s in a..v, (fun z => k * g z) s at hrv
    change S.lam a v = k * g v at hlv
    change S.alpha a v = k * g v * hEdge v at hav
    constructor
    · change (1 / k) * S.r a v = _
      rw [hrv, intervalIntegral.integral_const_mul]
      field_simp
    constructor
    · change (1 / k) * S.lam a v = _
      rw [hlv]
      field_simp
    · change (1 / k) * S.alpha a v = _
      rw [hav]
      field_simp
  · exact (x.is_classical_axis_triangle hab hM hsmall hglo hfixed).physicalScale hc

end ChristodoulouBV.AxisPicard

end
