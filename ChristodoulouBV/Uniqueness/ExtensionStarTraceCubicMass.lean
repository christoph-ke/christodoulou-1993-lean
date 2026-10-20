module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceMass
import ChristodoulouBV.BVSolution.AxisTraces
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Cubic mass improvement on outgoing rays

A linear-in-radius scalar quotient gives a cubic mass estimate. This is the
second mass improvement in part (A) of the terminal trace argument.
-/

public section

open Set MeasureTheory Filter
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- A bound `|θ/λ| ≤ C r` makes the outgoing mass at most `C² r³/6`.
The coefficient follows by integrating the mass density in the radius
coordinate from its canonical axis value. -/
theorem mass_le_sixth_sq_mul_radius_cubed_of_theta_ratio_le_radius
    {b u v C : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hu : 0 < u) (huv : u < v) (hvb : v < b) (hC : 0 ≤ C)
    (hθ : ∀ t ∈ Ioc u v,
      |S.theta u t / S.lam u t| ≤ C * S.r u t) :
    S.m u v ≤ C ^ 2 / 6 * (S.r u v) ^ 3 := by
  let B := (v + b) / 2
  let K := closedCoordTriangle 0 B
  let R : ℝ → ℝ := fun t => C1Solution.canonicalRadius S (u, t)
  let L : ℝ → ℝ := fun t => S.lam u t
  let F : ℝ → ℝ := fun t => IsBVSolution.massV S u t
  let G : ℝ → ℝ := fun t => (C ^ 2 / 2) * (L t * R t ^ 2)
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc u v) K := by
    intro t ht
    exact ⟨hu.le, ht.1, ht.2.trans hvB.le⟩
  have hRc1 : ContDiffOn ℝ 1 R (Icc u v) :=
    (C1Solution.canonicalRadius_contDiffOn hB hBb H).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn hmap
  have hRcont : ContinuousOn R (Icc u v) := hRc1.continuousOn
  have hLcont : ContinuousOn L (Icc u v) :=
    (C1Solution.five_fields_contDiffOn hB hBb H).1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap
  have hR0 : R u = 0 := (C1Solution.canonical_outgoing_axis S u).1
  have hRv : R v = S.r u v :=
    C1Solution.canonicalRadius_eq_radius hB hBb H hu.le huv hvB.le
  have hRderiv : ∀ t ∈ Ioo u v, HasDerivAt R (L t) t := by
    intro t ht
    have hpi : (u, t) ∈ interior K := by
      rw [interior_closedCoordTriangle]
      exact ⟨hu, ht.1, ht.2.trans hvB⟩
    have hdiff : DifferentiableAt ℝ (C1Solution.canonicalRadius S) (u, t) :=
      (((C1Solution.canonicalRadius_contDiffOn hB hBb H).differentiableOn
        (by norm_num)).mono interior_subset (u, t) hpi).differentiableAt
          (isOpen_interior.mem_nhds hpi)
    have hpair : HasDerivAt (fun s : ℝ => (u, s)) (0, 1) t :=
      (hasDerivAt_const t u).prodMk (hasDerivAt_id' t)
    have hjet := C1Solution.canonicalRadius_vertical_jet hB hBb H
      (show (u, t) ∈ K from interior_subset hpi)
    have hunique : UniqueDiffWithinAt ℝ K (u, t) :=
      (uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
        (by rw [interior_closedCoordTriangle]
            exact openCoordTriangle_nonempty hB)) (u, t) (interior_subset hpi)
    rw [fderivWithin_eq_fderiv hunique hdiff] at hjet
    have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt t hpair
    rw [hjet] at hcomp
    simpa only [R, L, Function.comp_def] using hcomp
  have hGcont : ContinuousOn G (Icc u v) :=
    continuousOn_const.mul (hLcont.mul (hRcont.pow 2))
  have hGint : IntervalIntegrable G volume u v :=
    hGcont.intervalIntegrable_of_Icc huv.le
  have hBV := H.isBVSolution_development (hu.trans (huv.trans hvb))
  have hp : (u, v) ∈ developmentWithInitialEdge b := ⟨hu.le, huv, hvb⟩
  have hFint : IntervalIntegrable F volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.le).2
      (hBV.mass_density_integrable_on_axis_slice hp)
  have hFG : ∀ t ∈ Ioo u v, F t ≤ G t := by
    intro t ht
    have ht' : t ∈ Ioc u v := ⟨ht.1, ht.2.le⟩
    have hpt : (u, t) ∈ developmentWithInitialEdge b :=
      ⟨hu.le, ht.1, ht.2.trans hvb⟩
    have hr : 0 < S.r u t := H.solution.radius_pos (u, t) hpt
    have hl : 0 < S.lam u t := H.solution.lam_pos (u, t) hpt
    have hmu := H.reduced_signs_of_c1 hpt
    have hR : R t = S.r u t :=
      C1Solution.canonicalRadius_eq_radius hB hBb H hu.le ht.1
        (ht.2.trans hvB).le
    have hθsq : (S.theta u t / S.lam u t) ^ 2 ≤
        C ^ 2 * (S.r u t) ^ 2 := by
      have hsq := (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg hC hr.le)).2 (hθ t ht')
      simpa only [sq_abs, mul_pow] using hsq
    have hq : 1 - 2 * S.m u t / S.r u t ≤ 1 := by
      linarith [hmu.2.1]
    have hmass : F t =
        (1 - 2 * S.m u t / S.r u t) *
          (S.lam u t * (S.theta u t / S.lam u t) ^ 2) / 2 := by
      dsimp [F, IsBVSolution.massV]
      field_simp [hl.ne']
    dsimp [G, L]
    rw [hmass, hR]
    have hprod :
        (1 - 2 * S.m u t / S.r u t) *
          (S.lam u t * (S.theta u t / S.lam u t) ^ 2) ≤
          S.lam u t * (C ^ 2 * (S.r u t) ^ 2) := by
      have hfirst :
          (1 - 2 * S.m u t / S.r u t) *
            (S.lam u t * (S.theta u t / S.lam u t) ^ 2) ≤
          S.lam u t * (S.theta u t / S.lam u t) ^ 2 := by
        exact mul_le_of_le_one_left
          (mul_nonneg hl.le (sq_nonneg _)) hq
      exact hfirst.trans (mul_le_mul_of_nonneg_left hθsq hl.le)
    nlinarith only [hprod]
  have hInt : S.m u v ≤ ∫ t in u..v, G t := by
    rw [hBV.mass_out_integral_from_axis hp]
    exact intervalIntegral.integral_mono_on_of_le_Ioo huv.le hFint hGint hFG
  have hRpowCont : ContinuousOn (fun t => R t ^ 3) (Icc u v) :=
    hRcont.pow 3
  have hDcont : ContinuousOn (fun t => 3 * R t ^ 2 * L t) (Icc u v) :=
    (continuousOn_const.mul (hRcont.pow 2)).mul hLcont
  have hD : ∀ t ∈ Ioo u v,
      HasDerivAt (fun s => R s ^ 3) (3 * R t ^ 2 * L t) t := by
    intro t ht
    convert (hRderiv t ht).pow 3 using 1
  have hFTC := intervalIntegral.integral_eq_sub_of_continuousOn_hasDerivAt
    huv.le hRpowCont hDcont hD
  have hGintEq : (∫ t in u..v, G t) =
      C ^ 2 / 6 * (S.r u v) ^ 3 := by
    have hpoint : G = fun t => (C ^ 2 / 6) * (3 * R t ^ 2 * L t) := by
      funext t
      dsimp [G]
      ring
    rw [hpoint, intervalIntegral.integral_const_mul, hFTC, hR0, hRv]
    ring
  exact hInt.trans_eq hGintEq

end ChristodoulouBV.Uniqueness

end
