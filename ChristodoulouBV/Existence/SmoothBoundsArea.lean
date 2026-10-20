module

public import ChristodoulouBV.Existence.SmoothBoundsCore
import all ChristodoulouBV.AreaEstimates.AnalyticArea
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!+# Global analytic areas of the smooth approximants

The endpoint finite-cutoff estimates exhaust the global development. The initial
edge has zero analytic area because the analytic measure has a density with
respect to planar volume. This also treats the zero-variation case directly.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace ChristodoulouBV

/-- A uniform finite-triangle analytic-area estimate passes to the global
development, including its initial edge. -/
theorem smooth_analytic_area_global_of_cutoffs (F : ℝ × ℝ → ℝ × ℝ)
    {C : ℝ≥0∞}
    (hcut : ∀ a : ℝ, 0 < a → smoothAnalyticArea F (openCoordTriangle 0 a) ≤ C) :
    smoothAnalyticArea F globalDomain ≤ C := by
  let E : ℕ → Set (ℝ × ℝ) := fun n => openCoordTriangle 0 ((n : ℝ) + 1)
  have hmono : Monotone E := by
    intro n m hnm p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.trans_le (by exact_mod_cast Nat.add_le_add_right hnm 1)⟩
  have hbound : smoothAnalyticArea F (⋃ n, E n) ≤ C := by
    rw [hmono.measure_iUnion]
    exact iSup_le (fun n => hcut _ (by positivity))
  have hline : smoothAnalyticArea F ({0} ×ˢ (univ : Set ℝ)) = 0 := by
    apply withDensity_absolutelyContinuous volume _
    rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, measure_singleton, zero_mul]
  have hsub : globalDomain ⊆ (⋃ n, E n) ∪ ({0} ×ˢ (univ : Set ℝ)) := by
    intro p hp
    rcases eq_or_lt_of_le hp.1 with hzero | hpos
    · exact Or.inr ⟨hzero.symm, mem_univ _⟩
    · obtain ⟨n, hn⟩ := exists_nat_gt p.2
      exact Or.inl (mem_iUnion.mpr ⟨n, hpos, hp.2, hn.trans (lt_add_one _)⟩)
  calc
    smoothAnalyticArea F globalDomain ≤
        smoothAnalyticArea F ((⋃ n, E n) ∪ ({0} ×ˢ (univ : Set ℝ))) := measure_mono hsub
    _ ≤ smoothAnalyticArea F (⋃ n, E n) +
        smoothAnalyticArea F ({0} ×ˢ (univ : Set ℝ)) := measure_union_le _ _
    _ ≤ C := by simpa only [hline, add_zero] using hbound

/-- All four analytic areas, on every finite triangle and on the global
development, have one universal coefficient. -/
theorem smooth_area_bounds
    {alpha₀ : ℝ → ℝ} {S : Fields}
    (hfinite : ∀ b : ℝ, 0 < b → IsC1Solution (developmentWithInitialEdge b) S)
    (hdata : ∀ v : ℝ, 0 < v → S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen) :
    (∀ a : ℝ, 0 < a →
      smoothAnalyticArea (sourcePhiAlphaLamMap S) (openCoordTriangle 0 a) ≤
          s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 2 ∧
      smoothAnalyticArea (sourcePhiBetaNuMap S) (openCoordTriangle 0 a) ≤
          s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 2 ∧
      smoothAnalyticArea (sourceLamPhiMap S) (openCoordTriangle 0 a) ≤
          s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 3 ∧
      smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 a) ≤
          s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 3) ∧
    (smoothAnalyticArea (sourcePhiAlphaLamMap S) globalDomain ≤
          s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 2 ∧
      smoothAnalyticArea (sourcePhiBetaNuMap S) globalDomain ≤
          s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 2 ∧
      smoothAnalyticArea (sourceLamPhiMap S) globalDomain ≤
          s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 3 ∧
      smoothAnalyticArea (sourceNuPhiMap S) globalDomain ≤
          s4UniversalC * eVariationOn alpha₀ (Ioi (0 : ℝ)) ^ 3) := by
  have hcut (a : ℝ) (ha : 0 < a) :=
    s6_finite_cutoff_area_bounds_original (by linarith : 0 < a + 1)
      (by linarith : a + 1 < a + 2) (hfinite (a + 2) (by linarith))
      (fun v hv => hdata v hv.1) hD ha (lt_add_one a)
  exact ⟨hcut,
    smooth_analytic_area_global_of_cutoffs _ (fun a ha => (hcut a ha).1),
    smooth_analytic_area_global_of_cutoffs _ (fun a ha => (hcut a ha).2.1),
    smooth_analytic_area_global_of_cutoffs _ (fun a ha => (hcut a ha).2.2.1),
    smooth_analytic_area_global_of_cutoffs _ (fun a ha => (hcut a ha).2.2.2)⟩

end ChristodoulouBV

end
