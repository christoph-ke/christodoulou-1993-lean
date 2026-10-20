module

public import ChristodoulouBV.AreaEstimates.ScalarAreaDensityCore
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Pointwise densities for the two scalar areas

The constants `3`, `45`, and `72` follow from the `1/3` expansion lower
bounds and the amplitude bounds (4.3).
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace ChristodoulouBV

/-- Pointwise analytic density estimate underlying (4.16). -/
theorem source_alpha_area_density_le {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {p : ℝ × ℝ} (hp : p ∈ openCoordTriangle 0 1) :
    ENNReal.ofReal |(fderiv ℝ (sourcePhiAlphaLamMap S) p).det| ≤
      3 * (sourceIncomingWeight S p *
        sourceAlphaMajorantMeasurable S p.2) +
      (45 * ENNReal.ofReal (sourceD S).toReal) *
        ENNReal.ofReal |(fderiv ℝ (sourceLamPhiMap S) p).det| := by
  rcases p with ⟨u, v⟩
  have hu : 0 < u := hp.1
  have huv : u < v := hp.2.1
  have hv : v < 1 := hp.2.2
  have hvI : v ∈ Ioo (0 : ℝ) 1 := ⟨hu.trans huv, hv⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hu.le, huv, hv⟩
  have hrpos : 0 < S.r u v := H.solution.radius_pos (u, v) hpU
  have hlam : (1 / 3 : ℝ) ≤ S.lam u v := hboot.1 (u, v) hpU
  have htheta := (sourceThetaZeta_pointwise H hr hcenter hboot hp).1
  have hcoef := alpha_area_coefficients (zeta := S.zeta u v) hrpos hlam
    ENNReal.toReal_nonneg htheta
  have hweight : sourceIncomingWeight S (u, v) =
      ENNReal.ofReal (|S.zeta u v| / S.r u v) := by
    change ENNReal.ofReal
      (|S.zeta u v| / C1Solution.canonicalRadius S (u, v)) = _
    rw [sourceCanonicalRadius_eq_radius H hu huv hv]
  have hcoef1 : ENNReal.ofReal |S.zeta u v / S.r u v / S.lam u v| ≤
      3 * sourceIncomingWeight S (u, v) := by
    simpa only [hweight] using hcoef.1
  obtain ⟨hlamK, _, _, halphaK, _⟩ := unit_field_contDiffOn H
  have hlamDiff := s4_differentiableAt_of_contDiffOn hlamK hu huv hv
  have halphaDiff := s4_differentiableAt_of_contDiffOn halphaK hu huv hv
  have hres : ENNReal.ofReal
      |(fderiv ℝ (fun p : ℝ × ℝ => S.alpha p.1 p.2) (u, v)) (0, 1) -
        (fderiv ℝ (fun p : ℝ × ℝ => S.lam p.1 p.2) (u, v)) (0, 1) *
          S.phi u v| ≤ sourceAlphaMajorantMeasurable S v := by
    rw [← s4_vertical_deriv halphaDiff,
      ← s4_vertical_deriv hlamDiff]
    simpa only [← sourceAlphaMajorantMeasurable_eq H hr hvI] using
      (eq4_15a H hr hcenter hboot hu huv hv)
  have hj := source_alpha_area_jacobian H hu huv hv
  simpa only [mul_assoc] using
    (scalar_jacobian_density_bound hj hcoef1 hres
      (by simpa only [mul_one] using hcoef.2))

/-- Pointwise analytic density estimate underlying (4.18). -/
theorem source_beta_area_density_le {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {p : ℝ × ℝ} (hp : p ∈ openCoordTriangle 0 1) :
    ENNReal.ofReal |(fderiv ℝ (sourcePhiBetaNuMap S) p).det| ≤
      3 * (sourceOutgoingWeight S p *
        sourceBetaMajorantMeasurable S p.1) +
      (72 * ENNReal.ofReal (sourceD S).toReal) *
        ENNReal.ofReal |(fderiv ℝ (sourceNuPhiMap S) p).det| := by
  rcases p with ⟨u, v⟩
  have hu : 0 < u := hp.1
  have huv : u < v := hp.2.1
  have hv : v < 1 := hp.2.2
  have huI : u ∈ Ioo (0 : ℝ) 1 := ⟨hu, huv.trans hv⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hu.le, huv, hv⟩
  have hrpos : 0 < S.r u v := H.solution.radius_pos (u, v) hpU
  have hnu : S.nu u v ≤ -(1 / 3 : ℝ) :=
    sourceNu_le_neg_third H hboot hp
  have hzeta := (sourceThetaZeta_pointwise H hr hcenter hboot hp).2
  have hcoef := beta_area_coefficients (theta := S.theta u v) hrpos hnu
    ENNReal.toReal_nonneg hzeta
  have hweight : sourceOutgoingWeight S (u, v) =
      ENNReal.ofReal (|S.theta u v| / S.r u v) := by
    change ENNReal.ofReal
      (|S.theta u v| / C1Solution.canonicalRadius S (u, v)) = _
    rw [sourceCanonicalRadius_eq_radius H hu huv hv]
  have hcoef1 : ENNReal.ofReal |-(S.theta u v / S.r u v / S.nu u v)| ≤
      3 * sourceOutgoingWeight S (u, v) := by
    simpa only [abs_neg, hweight] using hcoef.1
  obtain ⟨_, hnuK, _, _, hbetaK⟩ := unit_field_contDiffOn H
  have hnuDiff := s4_differentiableAt_of_contDiffOn hnuK hu huv hv
  have hbetaDiff := s4_differentiableAt_of_contDiffOn hbetaK hu huv hv
  have hres : ENNReal.ofReal
      |(fderiv ℝ (fun p : ℝ × ℝ => S.beta p.1 p.2) (u, v)) (1, 0) -
        (fderiv ℝ (fun p : ℝ × ℝ => S.nu p.1 p.2) (u, v)) (1, 0) *
          S.phi u v| ≤ sourceBetaMajorantMeasurable S u := by
    rw [← s4_horizontal_deriv hbetaDiff,
      ← s4_horizontal_deriv hnuDiff]
    exact (eq4_17a H hr hcenter hboot hu huv hv).trans
      (sourceBetaMajorant_le_measurable H hr hcenter hboot huI)
  have hj := source_beta_area_jacobian H hu huv hv
  simpa only [mul_assoc] using
    (scalar_jacobian_density_bound hj hcoef1 hres
      (by simpa only [mul_one] using hcoef.2))

end ChristodoulouBV

end
