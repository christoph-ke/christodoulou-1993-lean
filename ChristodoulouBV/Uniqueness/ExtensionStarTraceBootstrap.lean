module

public import ChristodoulouBV.Uniqueness.ExtensionTransportEquation
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceTransportAlgebra
public import ChristodoulouBV.ForMathlib.IntervalIntegral.IncomingSqrtRadius
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Unweighted incoming bootstrap on one old member

The weighted estimate, the first mass improvement, and the mass gap imply an
integrable derivative bound for `α′`. A monotone comparison with `√r` gives
the unweighted estimate without a second-derivative assumption at the axis.
-/

public section

open Set
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- At an interior point of a C¹ member, the actual radius has incoming
derivative `ν`. The radius is locally equal to its canonical C¹ extension. -/
theorem radius_hasDerivAt_u_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hvb : v < b) :
    HasDerivAt (fun s => S.r s v) (S.nu u v) u := by
  let B := (v + b) / 2
  let K := closedCoordTriangle 0 B
  let F := C1Solution.canonicalRadius S
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hpi : (u, v) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact ⟨hu, huv, hvB⟩
  have hF : ContDiffOn ℝ 1 F K := C1Solution.canonicalRadius_contDiffOn hB hBb H
  have hdiff : DifferentiableAt ℝ F (u, v) :=
    ((hF.differentiableOn (by norm_num)).mono interior_subset (u, v) hpi).differentiableAt
      (isOpen_interior.mem_nhds hpi)
  have hunique : UniqueDiffWithinAt ℝ K (u, v) :=
    (uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)) (u, v) (interior_subset hpi)
  have hwithin : fderivWithin ℝ F K (u, v) = fderiv ℝ F (u, v) :=
    fderivWithin_eq_fderiv hunique hdiff
  have hpair : HasDerivAt (fun s : ℝ => (s, v)) (1, 0) u :=
    (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
  have hcomp : HasDerivAt (fun s => F (s, v))
      (fderiv ℝ F (u, v) (1, 0)) u := by
    simpa only [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt u hpair
  have hjet := C1Solution.canonicalRadius_horizontal_jet hB hBb H
    (show (u, v) ∈ K from interior_subset hpi)
  rw [hwithin] at hjet
  rw [hjet] at hcomp
  have heq : (fun s => S.r s v) =ᶠ[𝓝 u] (fun s => F (s, v)) := by
    filter_upwards [Ioo_mem_nhds hu huv] with s hs
    exact (C1Solution.canonicalRadius_eq_radius hB hBb H hs.1.le hs.2 hvB.le).symm
  exact hcomp.congr_of_eventuallyEq heq

/-- The one-member form of the improved unweighted (5.3) estimate. All
coefficient hypotheses are imposed only at strict interior points of the
incoming segment; its endpoints are handled by C¹ continuity. -/
theorem alphaPrime_abs_le_incoming_add_sqrt_radius
    {b u₀ u v A M q₀ B₀ : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hu₀ : 0 < u₀) (hu₀u : u₀ < u) (huv : u < v) (hvb : v < b)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hq₀ : 0 < q₀)
    (hweighted : ∀ s ∈ Ioo u₀ u,
      Real.sqrt (S.r s v) *
        |deriv (fun t => S.alpha s t / S.lam s t) v / S.lam s v| ≤ A)
    (hθ : ∀ s ∈ Ioo u₀ u,
      |S.theta s v / S.lam s v| ≤ (2 * A / 3) * Real.sqrt (S.r s v))
    (hμ : ∀ s ∈ Ioo u₀ u,
      2 * S.m s v / S.r s v ≤ M * S.r s v)
    (hgap : ∀ s ∈ Ioo u₀ u,
      q₀ ≤ 1 - 2 * S.m s v / S.r s v)
    (hseed : |deriv (fun t => S.alpha u₀ t / S.lam u₀ t) v /
      S.lam u₀ v| ≤ B₀) :
    |deriv (fun t => S.alpha u t / S.lam u t) v / S.lam u v| ≤
      B₀ + 2 * ((4 * M * A + 8 * A ^ 3 / 27) / q₀) *
        Real.sqrt (S.r u₀ v) := by
  let R : ℝ → ℝ := fun s => S.r s v
  let N : ℝ → ℝ := fun s => S.nu s v
  let F : ℝ → ℝ := fun s =>
    deriv (fun t => S.alpha s t / S.lam s t) v / S.lam s v
  let D : ℝ → ℝ := fun s =>
    -2 * (N s / R s) *
        ((2 * S.m s v / R s) / (1 - 2 * S.m s v / R s)) * F s +
      3 * (N s / R s ^ 2) *
        ((2 * S.m s v / R s) / (1 - 2 * S.m s v / R s)) *
          (S.theta s v / S.lam s v) -
      (N s / R s ^ 2) *
        (1 / (1 - 2 * S.m s v / R s)) *
          (S.theta s v / S.lam s v) ^ 3
  have hseg : ∀ s ∈ Icc u₀ u, (s, v) ∈ openDevelopment 0 b := by
    intro s hs
    exact ⟨⟨hu₀.trans_le hs.1, (hs.2.trans_lt huv).trans hvb⟩,
      ⟨hs.2.trans_lt huv, hvb⟩⟩
  have hRderiv : ∀ s ∈ Icc u₀ u, HasDerivAt R (N s) s := by
    intro s hs
    exact radius_hasDerivAt_u_of_c1 H (hu₀.trans_le hs.1)
      (hs.2.trans_lt huv) hvb
  have hFderiv : ∀ s ∈ Icc u₀ u, HasDerivAt F (D s) s := by
    intro s hs
    simpa only [F, D, R, N] using alphaPrime_hasDerivAt_u H (hseg s hs)
  have hRcont : ContinuousOn R (Icc u₀ u) := by
    intro s hs
    exact (hRderiv s hs).continuousAt.continuousWithinAt
  have hFcont : ContinuousOn F (Icc u₀ u) := by
    intro s hs
    exact (hFderiv s hs).continuousAt.continuousWithinAt
  have hRpos : ∀ s ∈ Icc u₀ u, 0 < R s := by
    intro s hs
    have hp := hseg s hs
    exact H.solution.radius_pos (s, v) ⟨hp.1.1.le, hp.2.1, hp.2.2⟩
  have hDbound : ∀ s ∈ Ioo u₀ u,
      |D s| ≤ ((4 * M * A + 8 * A ^ 3 / 27) / q₀) *
        ((-N s) / Real.sqrt (R s)) := by
    intro s hs
    have hp := hseg s ⟨hs.1.le, hs.2.le⟩
    have hpt : (s, v) ∈ developmentWithInitialEdge b :=
      ⟨hp.1.1.le, hp.2.1, hp.2.2⟩
    let x := Real.sqrt (R s)
    let μ := 2 * S.m s v / R s
    let q := 1 - μ
    let f := S.theta s v / S.lam s v
    have hr := hRpos s ⟨hs.1.le, hs.2.le⟩
    have hx : 0 < x := Real.sqrt_pos.2 hr
    have hx2 : x ^ 2 = R s := Real.sq_sqrt hr.le
    have hx4 : x ^ 4 = R s ^ 2 := by
      calc
        x ^ 4 = (x ^ 2) ^ 2 := by ring
        _ = R s ^ 2 := by rw [hx2]
    have hν : N s ≤ 0 := (H.reduced_signs_of_c1 hpt).1.le
    have hμ0 : 0 ≤ μ := by
      simpa only [μ, R] using H.mass_ratio_nonneg_of_c1 hpt
    have hμ' : μ ≤ M * x ^ 2 := by
      rw [hx2]
      exact hμ s hs
    have hpoint := abs_transport_rhs_le_sqrt_radius hx hν hμ0 hq₀
      (hgap s hs) hA hM hμ' (hweighted s hs) (hθ s hs)
    rw [hx2, hx4] at hpoint
    simpa only [D, R, N, F, μ, q, f] using hpoint
  have hmain := intervalIntegral.abs_le_initial_add_sqrt_radius_of_deriv_bound
    hu₀u (div_nonneg (by positivity) hq₀.le) hRcont hFcont
    hRpos (fun s hs => hRderiv s ⟨hs.1.le, hs.2.le⟩)
    (fun s hs => hFderiv s ⟨hs.1.le, hs.2.le⟩) hDbound
  dsimp [F, R] at hmain
  linarith only [hmain, hseed]

end ChristodoulouBV.Uniqueness

end
