module

public import ChristodoulouBV.AreaEstimates.SmallDataZ
import Mathlib.Tactic

/-!
# Lemma 4.3: uniform small-data estimates

One threshold and one coefficient are fixed before the solution.  The
linear bound on `Z` converts the coupled `DZ` estimates into the powers
of `D` stated in the paper.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

/-- A universal coefficient for all estimates in Lemma 4.3. -/
noncomputable def s4UniversalC : ℝ≥0∞ := 10 ^ 60

/-- The coefficient in Lemma 4.3 is positive and finite. -/
theorem s4UniversalC_pos : 0 < s4UniversalC := by
  norm_num [s4UniversalC]

/-- The coefficient in Lemma 4.3 is finite. -/
theorem s4UniversalC_ne_top : s4UniversalC ≠ ∞ := by
  norm_num [s4UniversalC]

private theorem power_scale_algebra {D Z : ℝ≥0∞}
    (hZ : Z ≤ 100000000000000000 * D) :
    Z ≤ s4UniversalC * D ∧
      10000000000000000 * D ≤ s4UniversalC * D ∧
      30000000000 * (D * Z) ≤ s4UniversalC * D ^ 2 ∧
      3000000000000 * D * (D + Z) ≤ s4UniversalC * D ^ 2 ∧
      1000000000000000 * (D * Z) * (D + Z) ≤
        s4UniversalC * D ^ 3 := by
  let C₀ : ℝ≥0∞ := 100000000000000000
  have hsum : D + Z ≤ (1 + C₀) * D := by
    calc
      D + Z ≤ D + C₀ * D := add_le_add_right hZ D
      _ = (1 + C₀) * D := by ring
  have hDZ : D * Z ≤ C₀ * D ^ 2 := by
    calc
      D * Z ≤ D * (C₀ * D) := by gcongr
      _ = C₀ * D ^ 2 := by ring
  have hDsum : D * (D + Z) ≤ (1 + C₀) * D ^ 2 := by
    calc
      D * (D + Z) ≤ D * ((1 + C₀) * D) := by gcongr
      _ = (1 + C₀) * D ^ 2 := by ring
  have hDZe : (D * Z) * (D + Z) ≤
      (C₀ * (1 + C₀)) * D ^ 3 := by
    calc
      (D * Z) * (D + Z) ≤
          (C₀ * D ^ 2) * ((1 + C₀) * D) := by gcongr
      _ = (C₀ * (1 + C₀)) * D ^ 3 := by ring
  have hC₀ : C₀ ≤ s4UniversalC := by
    norm_num [C₀, s4UniversalC]
  have hField : (10000000000000000 : ℝ≥0∞) ≤ s4UniversalC := by
    norm_num [s4UniversalC]
  have hArea : 30000000000 * C₀ ≤ s4UniversalC := by
    norm_num [C₀, s4UniversalC]
  have hLog : 3000000000000 * (1 + C₀) ≤ s4UniversalC := by
    norm_num [C₀, s4UniversalC]
  have hGeom : 1000000000000000 * (C₀ * (1 + C₀)) ≤
      s4UniversalC := by
    norm_num [C₀, s4UniversalC]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hZ.trans (mul_le_mul_of_nonneg_right hC₀ bot_le)
  · exact mul_le_mul_of_nonneg_right hField bot_le
  · calc
      30000000000 * (D * Z) ≤ 30000000000 * (C₀ * D ^ 2) := by gcongr
      _ = (30000000000 * C₀) * D ^ 2 := by ring
      _ ≤ s4UniversalC * D ^ 2 := by gcongr
  · calc
      3000000000000 * D * (D + Z) ≤
          3000000000000 * ((1 + C₀) * D ^ 2) := by
        calc
          3000000000000 * D * (D + Z) =
              3000000000000 * (D * (D + Z)) := by ring
          _ ≤ 3000000000000 * ((1 + C₀) * D ^ 2) := by gcongr
      _ = (3000000000000 * (1 + C₀)) * D ^ 2 := by ring
      _ ≤ s4UniversalC * D ^ 2 := by gcongr
  · calc
      1000000000000000 * (D * Z) * (D + Z) ≤
          1000000000000000 * ((C₀ * (1 + C₀)) * D ^ 3) := by
        calc
          1000000000000000 * (D * Z) * (D + Z) =
              1000000000000000 * ((D * Z) * (D + Z)) := by ring
          _ ≤ 1000000000000000 *
              ((C₀ * (1 + C₀)) * D ^ 3) := by gcongr
      _ = (1000000000000000 * (C₀ * (1 + C₀))) * D ^ 3 := by ring
      _ ≤ s4UniversalC * D ^ 3 := by gcongr

/-- Lemma 4.3 with universal constants fixed before the solution.  It
includes the three axis/null-slice variation estimates and all four
analytic-area estimates. -/
theorem lemma4_3 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    (hD : sourceD S ≤ s4Epsilon0) (hZ : sourceZ S ≤ s4Epsilon0) :
    sourceZ S ≤ s4UniversalC * sourceD S ∧
      (eVariationOn (fun t => S.alpha t t) (Ioo 0 1) ≤
          s4UniversalC * sourceD S ∧
        (⨆ u ∈ Ioo (0 : ℝ) 1,
          eVariationOn (S.alpha u) (Ioo u 1)) ≤
          s4UniversalC * sourceD S ∧
        (⨆ v ∈ Ioo (0 : ℝ) 1,
          eVariationOn (fun u => S.beta u v) (Ioo 0 v)) ≤
          s4UniversalC * sourceD S) ∧
      (eVariationOn (fun t => Real.log (S.lam t t)) (Ioo 0 1) ≤
          s4UniversalC * sourceD S ^ 2 ∧
        (⨆ u ∈ Ioo (0 : ℝ) 1,
          eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1)) ≤
          s4UniversalC * sourceD S ^ 2 ∧
        (⨆ v ∈ Ioo (0 : ℝ) 1,
          eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo 0 v)) ≤
          s4UniversalC * sourceD S ^ 2) ∧
      (smoothAnalyticArea (sourcePhiAlphaLamMap S) (openCoordTriangle 0 1) ≤
          s4UniversalC * sourceD S ^ 2 ∧
        smoothAnalyticArea (sourcePhiBetaNuMap S) (openCoordTriangle 0 1) ≤
          s4UniversalC * sourceD S ^ 2) ∧
      (smoothAnalyticArea (sourceLamPhiMap S) (openCoordTriangle 0 1) ≤
          s4UniversalC * sourceD S ^ 3 ∧
        smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 1) ≤
          s4UniversalC * sourceD S ^ 3) := by
  have hZ0 := s4_Z_le_sourceD H hr hcenter hboot hD hZ
  obtain ⟨hZ', hField, hArea, hLog, hGeom⟩ := power_scale_algebra hZ0
  obtain ⟨hAlphaAxis, hAlphaOut, hBetaIn⟩ :=
    eq4_36 H hr hcenter hboot hD hZ
  obtain ⟨hLogAxis, hLogOut, hLogIn⟩ :=
    eq4_35 H hr hcenter hboot hD hZ
  obtain ⟨hA, hB⟩ := eq4_33 H hr hcenter hboot hD hZ
  obtain ⟨hL, hN⟩ := eq4_34 H hr hcenter hboot hD hZ
  exact ⟨hZ',
    ⟨hAlphaAxis.trans hField, hAlphaOut.trans hField,
      hBetaIn.trans hField⟩,
    ⟨hLogAxis.trans hLog, hLogOut.trans hLog,
      hLogIn.trans hLog⟩,
    ⟨hA.trans hArea, hB.trans hArea⟩,
    ⟨hL.trans hGeom, hN.trans hGeom⟩⟩

end ChristodoulouBV

end
