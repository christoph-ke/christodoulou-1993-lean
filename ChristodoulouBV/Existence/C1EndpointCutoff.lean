module

public import ChristodoulouBV.Existence.C1BootstrapExit
public import ChristodoulouBV.Existence.C1EndpointShiftArea
public import ChristodoulouBV.Existence.C1EndpointDilation
public import ChristodoulouBV.AreaEstimates.SmallData
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Uniform Section 4 areas on finite endpoint cutoffs

Every finite cutoff can be normalized to the unit triangle and centered in
the scalar gauge. The constants in Lemma 4.3 are independent of that cutoff.
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

/-- The four centered analytic-area estimates hold on every finite cutoff,
with one constant and the variation of the original full datum. The
construction at the terminal open triangle still needs an exhaustion step. -/
theorem s6_centered_finite_cutoff_area_bounds
    {alpha₀ : ℝ → ℝ} {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v ∈ Ioo (0 : ℝ) b,
      S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {a : ℝ} (ha : 0 < a) (haB : a < B) :
    ∃ Q : Fields,
      IsC1Solution (developmentWithInitialEdge 1) Q ∧
      Q.phi 0 0 = 0 ∧
      (∀ v ∈ Ioo (0 : ℝ) 1, Q.r 0 v = v / 2) ∧
      scalarShift Q ((Uniqueness.rescaledFields S 0 a).phi 0 0) =
        Uniqueness.rescaledFields S 0 a ∧
      smoothAnalyticArea (sourcePhiAlphaLamMap Q)
        (openCoordTriangle 0 1) ≤
          s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 2 ∧
      smoothAnalyticArea (sourcePhiBetaNuMap Q)
        (openCoordTriangle 0 1) ≤
          s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 2 ∧
      smoothAnalyticArea (sourceLamPhiMap Q)
        (openCoordTriangle 0 1) ≤
          s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 3 ∧
      smoothAnalyticArea (sourceNuPhiMap Q)
        (openCoordTriangle 0 1) ≤
          s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 3 := by
  let T := Uniqueness.rescaledFields S 0 a
  obtain ⟨HT, htrace, hDscale⟩ := s6_scale ha (haB.trans hBb) H hdata
  have hrT : ∀ v ∈ Ioo (0 : ℝ) 1, T.r 0 v = v / 2 :=
    fun v hv => (htrace v hv).1
  obtain ⟨Q, HQ, hcenter, hDQ, _, _, hZQ, hInv, _⟩ :=
    scalar_shift HT hrT (by norm_num : (1 : ℝ) ≤ 1)
  have hrQ : ∀ v ∈ Ioo (0 : ℝ) 1, Q.r 0 v = v / 2 := by
    intro v hv
    have h := hrT v hv
    dsimp [T] at h
    rw [← hInv] at h
    simpa only [scalarShift] using h
  have hbootT :=
    (s6_no_first_exit_finite hB hBb H hdata hD a ha haB).1
  have hZT :=
    (s6_no_first_exit_finite hB hBb H hdata hD a ha haB).2
  have hbootQ : s4_bootstrap Q := by
    rw [← hInv] at hbootT
    simpa only [s4_bootstrap, scalarShift] using hbootT
  have hDsmall : sourceD Q ≤ s4Epsilon0 := by
    rw [hDQ]
    exact hDscale.trans (hD.le.trans epsilonChosen_le_s4)
  have hZsmall : sourceZ Q ≤ s4Epsilon0 := by
    rw [hZQ]
    exact hZT
  obtain ⟨_, _, _, ⟨hA, hBarea⟩, ⟨hL, hN⟩⟩ :=
    lemma4_3 HQ hrQ hcenter hbootQ hDsmall hZsmall
  have hDQbound : sourceD Q ≤ eVariationOn alpha₀ (Ioi (0 : ℝ)) := by
    rw [hDQ]
    exact hDscale
  refine ⟨Q, HQ, hcenter, hrQ, hInv, ?_, ?_, ?_, ?_⟩
  · exact hA.trans (by gcongr)
  · exact hBarea.trans (by gcongr)
  · exact hL.trans (by gcongr)
  · exact hN.trans (by gcongr)

/-- The same four estimates hold for the original, uncentered finite cutoff.
Scalar centering changes each target map only by a constant translation. -/
theorem s6_finite_cutoff_area_bounds
    {alpha₀ : ℝ → ℝ} {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v ∈ Ioo (0 : ℝ) b,
      S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {a : ℝ} (ha : 0 < a) (haB : a < B) :
    let T := Uniqueness.rescaledFields S 0 a
    smoothAnalyticArea (sourcePhiAlphaLamMap T) (openCoordTriangle 0 1) ≤
        s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 2 ∧
      smoothAnalyticArea (sourcePhiBetaNuMap T) (openCoordTriangle 0 1) ≤
        s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 2 ∧
      smoothAnalyticArea (sourceLamPhiMap T) (openCoordTriangle 0 1) ≤
        s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 3 ∧
      smoothAnalyticArea (sourceNuPhiMap T) (openCoordTriangle 0 1) ≤
        s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 3 := by
  let T := Uniqueness.rescaledFields S 0 a
  obtain ⟨Q, HQ, _, _, hInv, hA, hBarea, hL, hN⟩ :=
    s6_centered_finite_cutoff_area_bounds hB hBb H hdata hD ha haB
  have hbootT :=
    (s6_no_first_exit_finite hB hBb H hdata hD a ha haB).1
  have hbootQ : s4_bootstrap Q := by
    rw [← hInv] at hbootT
    simpa only [s4_bootstrap, scalarShift] using hbootT
  have hOpen : IsOpen (openCoordTriangle 0 1) := by
    rw [← interior_closedCoordTriangle]
    exact isOpen_interior
  have hlamQ : ∀ p ∈ openCoordTriangle 0 1, Q.lam p.1 p.2 ≠ 0 := by
    intro p hp
    have hp' : p ∈ developmentWithInitialEdge 1 := by
      simp only [openCoordTriangle, mem_ofPred_eq] at hp
      exact ⟨hp.1.le, hp.2.1, hp.2.2⟩
    exact ne_of_gt (HQ.solution.lam_pos p hp')
  have hnuQ : ∀ p ∈ openCoordTriangle 0 1, Q.nu p.1 p.2 ≠ 0 := by
    intro p hp
    have h := sourceNu_le_neg_third HQ hbootQ hp
    exact ne_of_lt (lt_of_le_of_lt h (by norm_num))
  obtain ⟨hAe, hBe, hLe, hNe⟩ :=
    s6_scalar_shift_four_areas Q (T.phi 0 0) hOpen hlamQ hnuQ
  rw [hInv] at hAe hBe hLe hNe
  exact ⟨hAe.le.trans hA, hBe.le.trans hBarea,
    hLe.le.trans hL, hNe.le.trans hN⟩

/-- Uniform area bounds in the original coordinates on every strict finite
cutoff. The same universal constant works for all four areas and all cutoffs. -/
theorem s6_finite_cutoff_area_bounds_original
    {alpha₀ : ℝ → ℝ} {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v ∈ Ioo (0 : ℝ) b,
      S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal epsilonChosen)
    {a : ℝ} (ha : 0 < a) (haB : a < B) :
    smoothAnalyticArea (sourcePhiAlphaLamMap S) (openCoordTriangle 0 a) ≤
        s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 2 ∧
      smoothAnalyticArea (sourcePhiBetaNuMap S) (openCoordTriangle 0 a) ≤
        s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 2 ∧
      smoothAnalyticArea (sourceLamPhiMap S) (openCoordTriangle 0 a) ≤
        s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 3 ∧
      smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 a) ≤
        s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 3 := by
  have HT := (s6_scale ha (haB.trans hBb) H hdata).1
  have hboot :=
    (s6_no_first_exit_finite hB hBb H hdata hD a ha haB).1
  obtain ⟨hAe, hBe, hLe, hNe⟩ := s6_rescaled_four_areas S ha HT hboot
  obtain ⟨hA, hBarea, hL, hN⟩ :=
    s6_finite_cutoff_area_bounds hB hBb H hdata hD ha haB
  exact ⟨hAe.le.trans hA, hBe.le.trans hBarea,
    hLe.le.trans hL, hNe.le.trans hN⟩

end ChristodoulouBV

end
