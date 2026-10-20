module

public import ChristodoulouBV.AreaEstimates.IncomingAreaRhoFiber
public import ChristodoulouBV.AreaEstimates.ScalarAreaDensityCore
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Finite outgoing-fiber rho estimate

The finite-interval estimate retains the lower boundary term that is later
removed by the conjugate axis cancellation.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

namespace ChristodoulouBV

/-- The `(φ, α/λ)` Jacobian density is interval integrable on compact
outgoing fibers separated from the diagonal. -/
theorem sourcePhiAlphaLam_jacobian_integrable_fiber {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    {u a c : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (ha : a ∈ Ioo u 1) (hc : c ∈ Ioo a 1) :
    IntervalIntegrable
      (fun v => |(fderiv ℝ (sourcePhiAlphaLamMap S) (u, v)).det|)
      volume a c := by
  let B : ℝ := (c + 1) / 2
  let K := closedCoordTriangle 0 B
  let F := sourcePhiAlphaLamMap S
  let J : ℝ → ℝ := fun v => (fderivWithin ℝ F K (u, v)).det
  have hB : 0 < B := by dsimp [B]; linarith only [hu.1, ha.1, hc.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hc.2]
  have hcB : c < B := by dsimp [B]; linarith only [hc.2]
  have hUnique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hMap := sourcePhiAlphaLamMap_contDiffOn hB hB1 H
  have hWithin := hMap.continuousOn_fderivWithin hUnique (by norm_num)
  have hDet : ContinuousOn (fun p => (fderivWithin ℝ F K p).det) K :=
    ContinuousLinearMap.continuous_det.comp_continuousOn hWithin
  have hpath : ContinuousOn (fun v : ℝ => (u, v)) (Icc a c) := by
    fun_prop
  have hmap : MapsTo (fun v : ℝ => (u, v)) (Icc a c) K := by
    intro v hv
    exact ⟨hu.1.le, ha.1.le.trans hv.1, hv.2.trans hcB.le⟩
  have hJ : ContinuousOn J (Icc a c) := hDet.comp hpath hmap
  have hJInt : IntervalIntegrable (fun v => |J v|) volume a c :=
    hJ.abs.intervalIntegrable_of_Icc hc.1.le
  apply hJInt.congr_uIoo
  intro v hv
  have hv' : v ∈ Ioo a c := by
    simpa only [uIoo_of_le hc.1.le] using hv
  have hp : (u, v) ∈ openCoordTriangle 0 B :=
    ⟨hu.1, ha.1.trans hv'.1, hv'.2.trans hcB⟩
  have hKn : K ∈ 𝓝 (u, v) := by
    apply mem_of_superset (isOpen_interior.mem_nhds ?_) interior_subset
    rw [interior_closedCoordTriangle]
    exact hp
  simp only [J, fderivWithin_of_mem_nhds hKn, F]

/-- The compact forward estimate behind (4.28), with its lower boundary
term displayed explicitly. -/
theorem sourceRho_forward_finite_integral_bound {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {u a c : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (ha : a ∈ Ioo u 1) (hc : c ∈ Ioo a 1) :
    (∫ v in a..c, 2 * (|sourceRho S u v| / S.r u v ^ 3)) ≤
      |sourceRho S u a / S.lam u a| / S.r u a ^ 2 +
        ∫ v in a..c,
          |(fderiv ℝ (sourcePhiAlphaLamMap S) (u, v)).det| := by
  let B : ℝ := (c + 1) / 2
  let K := closedCoordTriangle 0 B
  let R : ℝ → ℝ := fun v => C1Solution.canonicalRadius S (u, v)
  let I : ℝ → ℝ := fun v => sourceRho S u v / S.lam u v
  let J : ℝ → ℝ := fun v => (fderiv ℝ (sourcePhiAlphaLamMap S) (u, v)).det
  have hB : 0 < B := by dsimp [B]; linarith only [hu.1, ha.1, hc.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [hc.2]
  have hcB : c < B := by dsimp [B]; linarith only [hc.2]
  have hmap : MapsTo (fun v : ℝ => (u, v)) (Icc a c) K := by
    intro v hv
    exact ⟨hu.1.le, ha.1.le.trans hv.1, hv.2.trans hcB.le⟩
  have hpair : ContDiffOn ℝ 1 (fun v : ℝ => (u, v)) (Icc a c) := by
    fun_prop
  have hR : ContDiffOn ℝ 1 R (Icc a c) :=
    (C1Solution.canonicalRadius_contDiffOn hB hB1 H).comp hpair hmap
  have hR2 : ContDiffOn ℝ 1 (fun v => R v ^ 2) (Icc a c) := hR.pow 2
  have hI : ContDiffOn ℝ 1 I (Icc a c) :=
    sourceRhoOverLam_contDiffOn_fiber H hu ha hc
  have hRpos (v : ℝ) (hv : v ∈ Icc a c) : 0 < R v := by
    have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
      ⟨hu.1.le, ha.1.trans_le hv.1, hv.2.trans_lt hc.2⟩
    change 0 < C1Solution.canonicalRadius S (u, v)
    rw [C1Solution.canonicalRadius_eq_radius hB hB1 H
      hu.1.le (ha.1.trans_le hv.1) (hv.2.trans hcB.le)]
    exact H.solution.radius_pos (u, v) hpU
  have hRderiv (v : ℝ) (hv : v ∈ Ioo a c) :
      deriv (fun t => R t ^ 2) v = 2 * R v * S.lam u v := by
    have hp : (u, v) ∈ openCoordTriangle 0 B :=
      ⟨hu.1, ha.1.trans hv.1, hv.2.trans hcB⟩
    have hpK : (u, v) ∈ K :=
      ⟨hu.1.le, (ha.1.trans hv.1).le, hv.2.le.trans hcB.le⟩
    have hKn : K ∈ 𝓝 (u, v) := by
      apply mem_of_superset (isOpen_interior.mem_nhds ?_) interior_subset
      rw [interior_closedCoordTriangle]
      exact hp
    have hDiff : DifferentiableAt ℝ (C1Solution.canonicalRadius S) (u, v) :=
      ((C1Solution.canonicalRadius_contDiffOn hB hB1 H).differentiableOn
        (by norm_num) _ hpK).differentiableAt hKn
    have hjet := C1Solution.canonicalRadius_vertical_jet hB hB1 H hpK
    have hline : HasDerivAt (fun t : ℝ => (u, t)) (0, 1) v :=
      (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
    have hhas : HasDerivAt R (S.lam u v) v := by
      have h := hDiff.hasFDerivAt.comp_hasDerivAt v hline
      change HasDerivAt R
        ((fderiv ℝ (C1Solution.canonicalRadius S) (u, v)) (0, 1)) v at h
      rwa [← fderivWithin_of_mem_nhds hKn, hjet] at h
    have heq : (R ^ (2 : ℕ)) = (fun t => R t ^ 2) := by
      funext t
      simp
    rw [← heq]
    simpa only [Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat,
      mul_assoc] using (hhas.pow 2).deriv
  have hIderiv (v : ℝ) (hv : v ∈ Ioo a c) :
      deriv I v = R v ^ 2 * J v := by
    have hp : (u, v) ∈ openCoordTriangle 0 1 :=
      ⟨hu.1, ha.1.trans hv.1, hv.2.trans hc.2⟩
    have h := eq4_27 H hr hcenter hboot hp
    change deriv (fun t => sourceRho S u t / S.lam u t) v =
      C1Solution.canonicalRadius S (u, v) ^ 2 *
        (fderiv ℝ (sourcePhiAlphaLamMap S) (u, v)).det
    rw [C1Solution.canonicalRadius_eq_radius hB hB1 H
      hu.1.le (ha.1.trans hv.1) (hv.2.le.trans hcB.le)]
    exact h
  have hJInt : IntervalIntegrable (fun v => |J v|) volume a c :=
    sourcePhiAlphaLam_jacobian_integrable_fiber H hu ha hc
  have hHardy := incoming_area_finite_hardy hc.1.le hI hR2
    (fun v hv => pow_pos (hRpos v hv) 2) hIderiv hJInt
  have hLeft : (∫ v in a..c,
      |I v| * deriv (fun t => R t ^ 2) v / (R v ^ 2) ^ 2) =
      ∫ v in a..c, 2 * (|sourceRho S u v| / S.r u v ^ 3) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hc.1.le
    intro v hv
    have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
      ⟨hu.1.le, ha.1.trans hv.1, hv.2.trans hc.2⟩
    have hrpos := H.solution.radius_pos (u, v) hpU
    have hlampos := H.solution.lam_pos (u, v) hpU
    change |I v| * deriv (fun t => R t ^ 2) v /
      (R v ^ 2) ^ 2 = 2 * (|sourceRho S u v| / S.r u v ^ 3)
    rw [hRderiv v hv, show R v = S.r u v from
      C1Solution.canonicalRadius_eq_radius hB hB1 H
        hu.1.le (ha.1.trans hv.1) (hv.2.le.trans hcB.le)]
    dsimp [I]
    rw [abs_div, abs_of_pos hlampos]
    field_simp [ne_of_gt hrpos, ne_of_gt hlampos]
  have hRight : (∫ v in a..c, |J v|) =
      ∫ v in a..c,
        |(fderiv ℝ (sourcePhiAlphaLamMap S) (u, v)).det| := rfl
  rw [hLeft, hRight] at hHardy
  have hRa : R a = S.r u a :=
    C1Solution.canonicalRadius_eq_radius hB hB1 H
      hu.1.le ha.1 (hc.1.le.trans hcB.le)
  simpa only [I, hRa] using hHardy

end ChristodoulouBV

end
