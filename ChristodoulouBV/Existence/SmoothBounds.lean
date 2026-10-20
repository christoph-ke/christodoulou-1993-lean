module

public import ChristodoulouBV.Existence.SmoothBoundsArea
public import ChristodoulouBV.Existence.SmoothBoundsTV
public import ChristodoulouBV.Existence.SmoothBoundsAmplitude
import Mathlib.Tactic

/-!+# Uniform bounds for the smooth approximation sequence

Every bound belongs to the same global C¹
witness with the exact approximating datum. All coefficients are the established
universal coefficients. Only raw scalar amplitudes and raw `α,β` variation
retain the datum-dependent scalar offset. The three-term variation is
invariant under that offset and includes the initial outgoing ray.
-/

public section

open Set Filter
open scoped ENNReal Topology

namespace ChristodoulouBV

/-- The quantitative conclusions for one member of the smooth sequence.
`alpha₀` is this member's exact datum, `D` is the variation of the original
BV datum, and `C` is the common scalar offset of the entire sequence.
This is an output record, constructed without estimate hypotheses. -/
structure SmoothSolutionBounds (alpha₀ : ℝ → ℝ) (D : ℝ≥0∞) (C : ℝ)
    (S : Fields) : Prop where
  /-- The global C¹ solution. -/
  solution : IsC1Solution globalDomain S
  /-- C¹ regularity on the closure of every finite triangle. -/
  finite : ∀ b : ℝ, 0 < b → IsC1Solution (developmentWithInitialEdge b) S
  /-- Exact initial radius and scalar-radius derivative traces. -/
  initial_data : ∀ v : ℝ, 0 < v → S.r 0 v = v / 2 ∧ S.alpha 0 v = alpha₀ v
  /-- Nonnegativity of the common scalar offset. -/
  offset_nonneg : 0 ≤ C
  /-- The actual centering constant of this member lies below that offset. -/
  offset_le : |S.phi 0 0| ≤ C
  /-- All six universal geometry inequalities, including `u = 0`. -/
  geometry : ∀ p ∈ globalDomain,
    (1 / 3 : ℝ) ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ 1 / 2 ∧
    (1 / 3 : ℝ) ≤ -S.nu p.1 p.2 ∧ -S.nu p.1 p.2 ≤ 2 / 3 ∧
    (2 / 3 : ℝ) ≤ 1 - 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
    1 - 2 * S.m p.1 p.2 / S.r p.1 p.2 ≤ 1
  /-- Centered, raw, and invariant amplitudes and both mass majorants. -/
  amplitudes : SmoothAmplitudes D C S
  /-- The outgoing three-term TV, with a universal coefficient. -/
  three_term_out : ∀ u : ℝ, 0 ≤ u →
    e1OutgoingTV S u ≤ ENNReal.ofReal (s6EndpointTVK * D.toReal)
  /-- The incoming three-term TV, with the same coefficient. -/
  three_term_in : ∀ v : ℝ, 0 < v →
    e1IncomingTV S v ≤ ENNReal.ofReal (s6EndpointTVK * D.toReal)
  /-- Centered outgoing scalar variation and expansion variation. -/
  variation_out : ∀ u : ℝ, 0 ≤ u →
    eVariationOn ((smoothCenteredFields S).alpha u) (Ioi u) ≤ s4UniversalC * D ∧
    eVariationOn (S.lam u) (Ioi u) ≤ s4UniversalC * D ^ 2
  /-- Centered incoming scalar variation and expansion variation. -/
  variation_in : ∀ v : ℝ, 0 < v →
    eVariationOn (fun u => (smoothCenteredFields S).beta u v) (Ioo 0 v) ≤ s4UniversalC * D ∧
    eVariationOn (fun u => S.nu u v) (Ioo 0 v) ≤ s4UniversalC * D ^ 2
  /-- Original outgoing scalar variation with the inverse shift retained. -/
  raw_variation_out : ∀ u : ℝ, 0 ≤ u → eVariationOn (S.alpha u) (Ioi u) ≤
    s4UniversalC * D + ENNReal.ofReal C * (s4UniversalC * D ^ 2)
  /-- Original incoming scalar variation with the inverse shift retained. -/
  raw_variation_in : ∀ v : ℝ, 0 < v → eVariationOn (fun u => S.beta u v) (Ioo 0 v) ≤
    s4UniversalC * D + ENNReal.ofReal C * (s4UniversalC * D ^ 2)
  /-- The four finite-triangle analytic areas, uniformly in the cutoff. -/
  areas_finite : ∀ a : ℝ, 0 < a →
    smoothAnalyticArea (sourcePhiAlphaLamMap S) (openCoordTriangle 0 a) ≤ s4UniversalC * D ^ 2 ∧
    smoothAnalyticArea (sourcePhiBetaNuMap S) (openCoordTriangle 0 a) ≤ s4UniversalC * D ^ 2 ∧
    smoothAnalyticArea (sourceLamPhiMap S) (openCoordTriangle 0 a) ≤ s4UniversalC * D ^ 3 ∧
    smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 a) ≤ s4UniversalC * D ^ 3
  /-- The same four area bounds on the full global development. -/
  areas_global :
    smoothAnalyticArea (sourcePhiAlphaLamMap S) globalDomain ≤ s4UniversalC * D ^ 2 ∧
    smoothAnalyticArea (sourcePhiBetaNuMap S) globalDomain ≤ s4UniversalC * D ^ 2 ∧
    smoothAnalyticArea (sourceLamPhiMap S) globalDomain ≤ s4UniversalC * D ^ 3 ∧
    smoothAnalyticArea (sourceNuPhiMap S) globalDomain ≤ s4UniversalC * D ^ 3

/-- Uniform smooth bounds for any smooth data approximation sequence with sharp variation control. Each solution
uses its own scalar centering; its original trace is preserved exactly.
All coefficients and all shift-invariant estimates depend only on `D`.
The original scalar estimates use the finite common supremum of offsets. -/
theorem uniform_smooth_bounds_for_sequence
    (alpha₀ : ℝ → ℝ) (alphaₙ : ℕ → ℝ → ℝ)
    (hsmooth : ∀ n, ContDiffOn ℝ 1 (alphaₙ n) (Ici 0))
    (hpoint : ∀ v : ℝ, 0 < v → Tendsto (fun n => alphaₙ n v) atTop (𝓝 (alpha₀ v)))
    (hvar : ∀ n, eVariationOn (alphaₙ n) (Ioi (0 : ℝ)) ≤ eVariationOn alpha₀ (Ioi 0))
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen) :
    ∃ T : ℕ → Fields, ∀ n,
      SmoothSolutionBounds (alphaₙ n) (eVariationOn alpha₀ (Ioi (0 : ℝ)))
        (smoothScalarOffset T) (T n) := by
  have hsmall (n : ℕ) := (hvar n).trans_lt hD
  have hex (n : ℕ) : ∃ S : Fields,
      IsC1Solution globalDomain S ∧
      (∀ v : ℝ, 0 < v → S.r 0 v = v / 2 ∧ S.alpha 0 v = alphaₙ n v) ∧
      ∀ b : ℝ, 0 < b → IsC1Solution (developmentWithInitialEdge b) S := by
    obtain ⟨S, HS, hdata, hfinite, _⟩ :=
      exists_global_c1_small_variation (alphaₙ n) (hsmooth n) (hsmall n)
    exact ⟨S, HS, hdata, hfinite⟩
  choose T hsolution hdata hfinite using hex
  obtain ⟨hC0, hC, hamp⟩ :=
    smooth_amplitude_bounds hfinite hdata hsmall hD hvar (hpoint 1 (by norm_num))
  refine ⟨T, fun n => ?_⟩
  have hreal := ENNReal.toReal_mono (ne_of_lt (hD.trans_le le_top)) (hvar n)
  obtain ⟨hout, hin⟩ := global_c1_universal_tv_bound (hfinite n) (hdata n) (hsmall n)
  obtain ⟨hvout, hvin⟩ := smooth_centered_variation_bounds (hfinite n) (hdata n) (hsmall n)
  obtain ⟨hrout, hrin⟩ := smooth_raw_variation_bounds (hfinite n) (hdata n) (hsmall n)
  obtain ⟨hcut, hglobal⟩ := smooth_area_bounds (hfinite n) (hdata n) (hsmall n)
  refine ⟨hsolution n, hfinite n, hdata n, hC0, hC n,
    global_c1_geometry (hfinite n) (hdata n) (hsmall n), hamp n,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    exact (hout u hu).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hreal s6EndpointTVK_pos.le))
  · intro v hv
    exact (hin v hv).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hreal s6EndpointTVK_pos.le))
  · intro u hu
    exact ⟨(hvout u hu).1.trans (by gcongr; exact hvar n),
      (hvout u hu).2.trans (by gcongr; exact hvar n)⟩
  · intro v hv
    exact ⟨(hvin v hv).1.trans (by gcongr; exact hvar n),
      (hvin v hv).2.trans (by gcongr; exact hvar n)⟩
  · intro u hu
    exact (hrout u hu).trans (by gcongr; exacts [hvar n, hC n, hvar n])
  · intro v hv
    exact (hrin v hv).trans (by gcongr; exacts [hvar n, hC n, hvar n])
  · intro a ha
    obtain ⟨hA, hB, hL, hN⟩ := hcut a ha
    exact ⟨hA.trans (by gcongr; exact hvar n), hB.trans (by gcongr; exact hvar n),
      hL.trans (by gcongr; exact hvar n), hN.trans (by gcongr; exact hvar n)⟩
  · obtain ⟨hA, hB, hL, hN⟩ := hglobal
    exact ⟨hA.trans (by gcongr; exact hvar n), hB.trans (by gcongr; exact hvar n),
      hL.trans (by gcongr; exact hvar n), hN.trans (by gcongr; exact hvar n)⟩

/-- Uniform smooth approximants for every small BV datum, including
arbitrary prescribed jump values and `D = 0`. The global solution sequence
retains the quantitative estimates needed by the BV limit construction and the quantitative witness. -/
theorem uniform_smooth_bounds (alpha₀ : ℝ → ℝ)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen) :
    ∃ (alphaₙ : ℕ → ℝ → ℝ) (T : ℕ → Fields),
      (∀ n, ContDiffOn ℝ 1 (alphaₙ n) (Ici 0)) ∧
      (∀ v : ℝ, 0 < v → Tendsto (fun n => alphaₙ n v) atTop (𝓝 (alpha₀ v))) ∧
      (∀ n, eVariationOn (alphaₙ n) (Ioi (0 : ℝ)) ≤ eVariationOn alpha₀ (Ioi 0)) ∧
      (∀ n, eVariationOn (alphaₙ n) (Ioi (0 : ℝ)) < ENNReal.ofReal epsilonChosen) ∧
      Tendsto (fun n => eVariationOn (alphaₙ n) (Ioi (0 : ℝ))) atTop
        (𝓝 (eVariationOn alpha₀ (Ioi (0 : ℝ)))) ∧
      ∀ n, SmoothSolutionBounds (alphaₙ n) (eVariationOn alpha₀ (Ioi (0 : ℝ)))
        (smoothScalarOffset T) (T n) := by
  obtain ⟨alphaₙ, hsmooth, hpoint, hvar, hsmall, hvarlim, _⟩ :=
    smooth_data_below_epsilon epsilonChosen alpha₀ hD
  obtain ⟨T, hT⟩ := uniform_smooth_bounds_for_sequence alpha₀ alphaₙ hsmooth hpoint hvar hD
  exact ⟨alphaₙ, T, hsmooth, hpoint, hvar, hsmall, hvarlim, hT⟩

end ChristodoulouBV

end
