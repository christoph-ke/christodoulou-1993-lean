module

public import ChristodoulouBV.Uniqueness.ExtensionStarTrace
import ChristodoulouBV.BVSolution.AxisTraces
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Radial mass improvement for the terminal trace

The outgoing mass density is integrated in the canonical radius coordinate,
so the estimate remains uniform as the outgoing ray approaches the axis.
-/

public section

open Set MeasureTheory Filter
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- A square-root bound for `θ/λ` gives a quadratic mass bound on one outgoing
ray. This is the radius-coordinate integration used in the
terminal trace estimate. -/
theorem mass_le_quarter_sq_mul_radius_sq_of_theta_ratio_le_sqrt
    {b u v C : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hu : 0 < u) (huv : u < v) (hvb : v < b) (hC : 0 ≤ C)
    (hθ : ∀ t ∈ Ioc u v,
      |S.theta u t / S.lam u t| ≤ C * Real.sqrt (S.r u t)) :
    S.m u v ≤ C ^ 2 / 4 * (S.r u v) ^ 2 := by
  let B := (v + b) / 2
  let K := closedCoordTriangle 0 B
  let R : ℝ → ℝ := fun t => C1Solution.canonicalRadius S (u, t)
  let L : ℝ → ℝ := fun t => S.lam u t
  let F : ℝ → ℝ := fun t => IsBVSolution.massV S u t
  let G : ℝ → ℝ := fun t => (C ^ 2 / 2) * (L t * R t)
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
    continuousOn_const.mul (hLcont.mul hRcont)
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
    have hsqrt := Real.sq_sqrt hr.le
    have hθsq : (S.theta u t / S.lam u t) ^ 2 ≤ C ^ 2 * S.r u t := by
      have hsq := (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg hC (Real.sqrt_nonneg _))).2 (hθ t ht')
      simpa only [sq_abs, mul_pow, hsqrt] using hsq
    have hq : 0 ≤ 1 - 2 * S.m u t / S.r u t ∧
        1 - 2 * S.m u t / S.r u t ≤ 1 := by
      constructor <;> linarith [hmu.2.2, hmu.2.1]
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
          S.lam u t * (C ^ 2 * S.r u t) := by
      have hfirst :
          (1 - 2 * S.m u t / S.r u t) *
            (S.lam u t * (S.theta u t / S.lam u t) ^ 2) ≤
            S.lam u t * (S.theta u t / S.lam u t) ^ 2 := by
        exact mul_le_of_le_one_left
          (mul_nonneg hl.le (sq_nonneg _)) hq.2
      exact hfirst.trans (mul_le_mul_of_nonneg_left hθsq hl.le)
    nlinarith only [hprod]
  have hInt : S.m u v ≤ ∫ t in u..v, G t := by
    rw [hBV.mass_out_integral_from_axis hp]
    exact intervalIntegral.integral_mono_on_of_le_Ioo huv.le hFint hGint hFG
  have hRpowCont : ContinuousOn (fun t => R t ^ 2) (Icc u v) :=
    hRcont.pow 2
  have hDcont : ContinuousOn (fun t => 2 * R t * L t) (Icc u v) :=
    (continuousOn_const.mul hRcont).mul hLcont
  have hD : ∀ t ∈ Ioo u v,
      HasDerivAt (fun s => R s ^ 2) (2 * R t * L t) t := by
    intro t ht
    convert (hRderiv t ht).pow 2 using 1
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_continuousOn_hasDerivAt
    huv.le hRpowCont hDcont hD
  have hGintEq : (∫ t in u..v, G t) = C ^ 2 / 4 * (S.r u v) ^ 2 := by
    have hpoint : G = fun t => (C ^ 2 / 4) * (2 * R t * L t) := by
      funext t
      dsimp [G]
      ring
    rw [hpoint, intervalIntegral.integral_const_mul, hFTC, hR0, hRv]
    ring
  exact hInt.trans_eq hGintEq

/-- The first radius improvement in part (A): one constant controls the mass
quadratically in the radius on every old outgoing ray above `u₀`. -/
theorem exists_uniform_quadratic_mass_bound_before_star_of_incoming_bddAbove
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε0 : 0 ≤ ε)
    (hε1 : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε)
    (hIncoming : BddAbove
      (incomingWeightedAlphaPrimeValues u₀ vStar ((1 : ℝ) / 2) S)) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, u₀ < u → u < v → v < b →
          (S b).m u v ≤ A ^ 2 / 9 * ((S b).r u v) ^ 2 := by
  obtain ⟨A, hA0, _, hθ⟩ :=
    exists_uniform_theta_ratio_bound_before_star_of_incoming_bddAbove
      hu₀ hα hfamily hε0 hε1 htail hIncoming
  refine ⟨A, hA0, ?_⟩
  intro b hb u v hu₀u huv hvb
  have hu : 0 < u := hu₀.1.trans hu₀u
  have hθsqrt : ∀ t ∈ Ioc u v,
      |(S b).theta u t / (S b).lam u t| ≤
        (2 * A / 3) * Real.sqrt ((S b).r u t) := by
    intro t ht
    have h := hθ b hb u t hu₀u ht.1 (ht.2.trans_lt hvb)
    calc
      |(S b).theta u t / (S b).lam u t| ≤
          A / (2 - (1 : ℝ) / 2) *
            ((S b).r u t) ^ (1 - (1 : ℝ) / 2) := h
      _ = (2 * A / 3) * Real.sqrt ((S b).r u t) := by
        have htwo : (2 : ℝ) - 1 / 2 = 3 / 2 := by norm_num
        have hone : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
        have hcoeff : A / (3 / 2) = 2 * A / 3 := by ring
        rw [htwo, hone, hcoeff, Real.sqrt_eq_rpow]
  have hmass := mass_le_quarter_sq_mul_radius_sq_of_theta_ratio_le_sqrt
    (hfamily b hb).1 hu huv hvb (by positivity : 0 ≤ 2 * A / 3) hθsqrt
  convert hmass using 1
  ring

/-- The quadratic mass estimate makes the mass ratio at most linear in the
radius, uniformly across the compatible family. -/
theorem exists_uniform_linear_mass_ratio_before_star_of_incoming_bddAbove
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε0 : 0 ≤ ε)
    (hε1 : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε)
    (hIncoming : BddAbove
      (incomingWeightedAlphaPrimeValues u₀ vStar ((1 : ℝ) / 2) S)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, u₀ < u → u < v → v < b →
          2 * (S b).m u v / (S b).r u v ≤ M * (S b).r u v := by
  obtain ⟨A, hA0, hmass⟩ :=
    exists_uniform_quadratic_mass_bound_before_star_of_incoming_bddAbove
      hu₀ hα hfamily hε0 hε1 htail hIncoming
  refine ⟨2 * A ^ 2 / 9, by positivity, ?_⟩
  intro b hb u v hu₀u huv hvb
  have hr : 0 < (S b).r u v :=
    (hfamily b hb).1.solution.radius_pos (u, v)
      ⟨(hu₀.1.trans hu₀u).le, huv, hvb⟩
  apply (div_le_iff₀ hr).2
  have hm := hmass b hb u v hu₀u huv hvb
  nlinarith only [hm]

end ChristodoulouBV.Uniqueness

end
