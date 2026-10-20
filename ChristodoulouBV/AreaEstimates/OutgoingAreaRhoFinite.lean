module

public import ChristodoulouBV.AreaEstimates.OutgoingAreaRhoFiber
public import ChristodoulouBV.AreaEstimates.ScalarAreaDensityCore
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Finite incoming-fiber rho estimate

This is the compact-interval form of (4.23). The terminal boundary term is
retained until the axis limit is taken.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

/-- The Jacobian density is locally interval integrable along each incoming
fiber, including its initial endpoint. -/
theorem sourcePhiBetaNu_jacobian_integrable_fiber {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {v c : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo 0 v) :
    IntervalIntegrable
      (fun u => |(fderiv ℝ (sourcePhiBetaNuMap S) (u, v)).det|)
      volume 0 c := by
  let B : ℝ := (v + 1) / 2
  let K := closedCoordTriangle 0 B
  let F := sourcePhiBetaNuMap S
  let J : ℝ → ℝ := fun u => (fderivWithin ℝ F K (u, v)).det
  have hB : 0 < B := by dsimp [B]; linarith only [hv.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hv.2]
  have hvB : v < B := by dsimp [B]; linarith only [hv.2]
  have hUnique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hMap := sourcePhiBetaNuMap_contDiffOn hB hB1 H
  have hWithin := hMap.continuousOn_fderivWithin hUnique (by norm_num)
  have hDet : ContinuousOn (fun p => (fderivWithin ℝ F K p).det) K :=
    ContinuousLinearMap.continuous_det.comp_continuousOn hWithin
  have hpath : ContinuousOn (fun u : ℝ => (u, v)) (Icc 0 c) := by
    fun_prop
  have hmap : MapsTo (fun u : ℝ => (u, v)) (Icc 0 c) K := by
    intro u hu
    exact ⟨hu.1, hu.2.trans hc.2.le, hvB.le⟩
  have hJ : ContinuousOn J (Icc 0 c) := hDet.comp hpath hmap
  have hJInt : IntervalIntegrable (fun u => |J u|) volume 0 c :=
    hJ.abs.intervalIntegrable_of_Icc hc.1.le
  apply hJInt.congr_uIoo
  intro u hu
  have hu' : u ∈ Ioo (0 : ℝ) c := by
    simpa only [uIoo_of_le hc.1.le] using hu
  have hp : (u, v) ∈ openCoordTriangle 0 B :=
    ⟨hu'.1, hu'.2.trans hc.2, hvB⟩
  have hKn : K ∈ 𝓝 (u, v) := by
    apply mem_of_superset (isOpen_interior.mem_nhds ?_) interior_subset
    rw [interior_closedCoordTriangle]
    exact hp
  simp only [J, fderivWithin_of_mem_nhds hKn, F]

/-- The finite-interval weighted `ρ` inequality before discarding the
axis term. The left integral is exactly twice the rho density integral. -/
theorem sourceRho_finite_integral_bound {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {v c : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) (hc : c ∈ Ioo 0 v) :
    (∫ u in (0 : ℝ)..c, 2 * (|sourceRho S u v| / S.r u v ^ 3)) ≤
      |sourceRho S c v / S.nu c v| / S.r c v ^ 2 +
        ∫ u in (0 : ℝ)..c,
          |(fderiv ℝ (sourcePhiBetaNuMap S) (u, v)).det| := by
  let B : ℝ := (v + 1) / 2
  let K := closedCoordTriangle 0 B
  let R : ℝ → ℝ := fun u => C1Solution.canonicalRadius S (u, v)
  let I : ℝ → ℝ := fun u => sourceRho S u v / S.nu u v
  let J : ℝ → ℝ := fun u => -(fderiv ℝ (sourcePhiBetaNuMap S) (u, v)).det
  have hB : 0 < B := by dsimp [B]; linarith only [hv.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hv.2]
  have hvB : v < B := by dsimp [B]; linarith only [hv.2]
  have hmap : MapsTo (fun u : ℝ => (u, v)) (Icc 0 c) K := by
    intro u hu
    exact ⟨hu.1, hu.2.trans hc.2.le, hvB.le⟩
  have hpair : ContDiffOn ℝ 1 (fun u : ℝ => (u, v)) (Icc 0 c) := by
    fun_prop
  have hR : ContDiffOn ℝ 1 R (Icc 0 c) :=
    (C1Solution.canonicalRadius_contDiffOn hB hB1 H).comp hpair hmap
  have hR2 : ContDiffOn ℝ 1 (fun u => R u ^ 2) (Icc 0 c) := hR.pow 2
  have hI : ContDiffOn ℝ 1 I (Icc 0 c) :=
    sourceRhoOverNu_contDiffOn_fiber H hv hc
  have hRpos (u : ℝ) (hu : u ∈ Icc 0 c) : 0 < R u := by
    have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
      ⟨hu.1, hu.2.trans_lt hc.2, hv.2⟩
    change 0 < C1Solution.canonicalRadius S (u, v)
    rw [C1Solution.canonicalRadius_eq_radius hB hB1 H
      hu.1 (hu.2.trans_lt hc.2) hvB.le]
    exact H.solution.radius_pos (u, v) hpU
  have hRderiv (u : ℝ) (hu : u ∈ Ioo 0 c) :
      deriv (fun t => R t ^ 2) u = 2 * R u * S.nu u v := by
    have hp : (u, v) ∈ openCoordTriangle 0 B :=
      ⟨hu.1, hu.2.trans hc.2, hvB⟩
    have hpK : (u, v) ∈ K :=
      ⟨hu.1.le, (hu.2.trans hc.2).le, hvB.le⟩
    have hKn : K ∈ 𝓝 (u, v) := by
      apply mem_of_superset (isOpen_interior.mem_nhds ?_) interior_subset
      rw [interior_closedCoordTriangle]
      exact hp
    have hDiff : DifferentiableAt ℝ (C1Solution.canonicalRadius S) (u, v) :=
      ((C1Solution.canonicalRadius_contDiffOn hB hB1 H).differentiableOn
        (by norm_num) _ hpK).differentiableAt hKn
    have hjet := C1Solution.canonicalRadius_horizontal_jet hB hB1 H hpK
    have hline : HasDerivAt (fun t : ℝ => (t, v)) (1, 0) u :=
      (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
    have hhas : HasDerivAt R (S.nu u v) u := by
      have h := hDiff.hasFDerivAt.comp_hasDerivAt u hline
      change HasDerivAt R
        ((fderiv ℝ (C1Solution.canonicalRadius S) (u, v)) (1, 0)) u at h
      rwa [← fderivWithin_of_mem_nhds hKn, hjet] at h
    have heq : (R ^ (2 : ℕ)) = (fun t => R t ^ 2) := by
      funext t
      simp
    rw [← heq]
    simpa only [Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat,
      mul_assoc] using
      (hhas.pow 2).deriv
  have hIderiv (u : ℝ) (hu : u ∈ Ioo 0 c) :
      deriv I u = R u ^ 2 * J u := by
    have hp : (u, v) ∈ openCoordTriangle 0 1 :=
      ⟨hu.1, hu.2.trans hc.2, hv.2⟩
    have h := eq4_22 H hr hcenter hboot hp
    change deriv (fun t => sourceRho S t v / S.nu t v) u =
      C1Solution.canonicalRadius S (u, v) ^ 2 *
        -(fderiv ℝ (sourcePhiBetaNuMap S) (u, v)).det
    rw [C1Solution.canonicalRadius_eq_radius hB hB1 H
      hu.1.le (hu.2.trans hc.2) hvB.le]
    convert h using 1; ring
  have hJInt : IntervalIntegrable (fun u => |J u|) volume 0 c := by
    change IntervalIntegrable
      (fun u => |-(fderiv ℝ (sourcePhiBetaNuMap S) (u, v)).det|)
      volume 0 c
    simpa only [abs_neg] using sourcePhiBetaNu_jacobian_integrable_fiber H hv hc
  have hHardy := outgoing_area_finite_hardy hc.1.le hI hR2
    (fun u hu => pow_pos (hRpos u hu) 2) hIderiv hJInt
  have hLeft : (∫ u in (0 : ℝ)..c,
      |I u| * (-deriv (fun t => R t ^ 2) u) / (R u ^ 2) ^ 2) =
      ∫ u in (0 : ℝ)..c, 2 * (|sourceRho S u v| / S.r u v ^ 3) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hc.1.le
    intro u hu
    have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
      ⟨hu.1.le, hu.2.trans hc.2, hv.2⟩
    have hrpos := H.solution.radius_pos (u, v) hpU
    have hpK : (u, v) ∈ K :=
      ⟨hu.1.le, (hu.2.trans hc.2).le, hvB.le⟩
    have hnneg : S.nu u v < 0 :=
      C1Solution.nu_neg_closed_triangle hB hB1 H hpK
    have hnune := ne_of_lt hnneg
    change |I u| * (-deriv (fun t => R t ^ 2) u) /
      (R u ^ 2) ^ 2 = 2 * (|sourceRho S u v| / S.r u v ^ 3)
    rw [hRderiv u hu, show R u = S.r u v from
      C1Solution.canonicalRadius_eq_radius hB hB1 H
        hu.1.le (hu.2.trans hc.2) hvB.le]
    dsimp [I]
    rw [abs_div, abs_of_neg hnneg]
    field_simp [ne_of_gt hrpos, hnune]
  have hRight : (∫ u in (0 : ℝ)..c, |J u|) =
      ∫ u in (0 : ℝ)..c,
        |(fderiv ℝ (sourcePhiBetaNuMap S) (u, v)).det| := by
    apply intervalIntegral.integral_congr_Ioo_of_le hc.1.le
    intro u hu
    simp only [J, abs_neg]
  rw [hLeft, hRight] at hHardy
  have hRc : R c = S.r c v :=
    C1Solution.canonicalRadius_eq_radius hB hB1 H
      hc.1.le hc.2 hvB.le
  simpa only [I, hRc] using hHardy

end ChristodoulouBV

end
