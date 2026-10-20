module

public import ChristodoulouBV.C1Solution.ExtractionJets
public import ChristodoulouBV.C1Solution.ExtractionMass
import ChristodoulouBV.C1Solution.Extraction
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The original radial equation on the reduced C¹ carrier

The frozen `IsSolution` is the *reduced* characteristic system. Its conformal
clause supplies a positive `Ω` separately at each point; it does not supply an
independent original Einstein-scalar solution or a continuous `Ω` field.
The results below transfer the original radial display (1.4a) to the interior
of this reduced C¹ carrier. Classical two-sided derivatives on the initial edge
`u = 0` are not determined by the frozen one-sided development.
-/

public section

open Set
open scoped Topology

namespace ChristodoulouBV.IsC1Solution

/-- The reduced C¹ mass gap is strictly positive at every point of the
development. This excludes the zero set before any division by `1 - μ`. -/
theorem mass_gap_pos_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ developmentWithInitialEdge b) :
    0 < 1 - 2 * S.m p.1 p.2 / S.r p.1 p.2 := by
  obtain ⟨u, v⟩ := p
  obtain ⟨hu, huv, hv⟩ := hp
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v ≤ B := by dsimp [B]; linarith
  have hr := H.solution.radius_pos (u, v) ⟨hu, huv, hv⟩
  have hgap := C1Solution.mass_gap_pos hB hBb H hu huv hvB
  have heq : 1 - 2 * S.m u v / S.r u v =
      (S.r u v - 2 * S.m u v) / S.r u v := by
    field_simp
  rw [heq]
  exact div_pos hgap hr

/-- The mass ratio of the reduced C¹ solution is nonnegative. This holds on the reduced carrier. -/
theorem mass_ratio_nonneg_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ developmentWithInitialEdge b) :
    0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 := by
  obtain ⟨u, v⟩ := p
  obtain ⟨hu, huv, hv⟩ := hp
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v ≤ B := by dsimp [B]; linarith
  have hm := C1Solution.mass_nonneg hB hBb H hu huv hvB
  have hr := H.solution.radius_pos (u, v) ⟨hu, huv, hv⟩
  exact div_nonneg (mul_nonneg (by norm_num) hm) hr.le

/-- The pretrapped sign branch on the reduced C¹ carrier. The two zero and
negative branches of the original Proposition 1.1 are empty here because the
frozen solution already has positive `λ` and the mass gap is positive. -/
theorem reduced_signs_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ developmentWithInitialEdge b) :
    S.nu p.1 p.2 < 0 ∧
      0 < S.lam p.1 p.2 ∧
      0 ≤ 2 * S.m p.1 p.2 / S.r p.1 p.2 ∧
      2 * S.m p.1 p.2 / S.r p.1 p.2 < 1 := by
  obtain ⟨u, v⟩ := p
  obtain ⟨hu, huv, hv⟩ := hp
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v ≤ B := by dsimp [B]; linarith
  have hnu := C1Solution.nu_neg hB hBb H hu huv hvB
  have hlam := H.solution.lam_pos (u, v) ⟨hu, huv, hv⟩
  have hmu := H.mass_ratio_nonneg_of_c1 (p := (u, v)) ⟨hu, huv, hv⟩
  have hgap := H.mass_gap_pos_of_c1 (p := (u, v)) ⟨hu, huv, hv⟩
  exact ⟨hnu, hlam, hmu, by linarith⟩

/-- The pointwise positive conformal witness of the reduced carrier has the
quotient form of (1.5). The denominator is justified by `mass_gap_pos_of_c1`. -/
theorem reduced_metric_identity_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ developmentWithInitialEdge b) :
    ∃ Ω : ℝ, 0 < Ω ∧
      Ω ^ 2 = -(4 * S.lam p.1 p.2 * S.nu p.1 p.2) /
        (1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) := by
  obtain ⟨Ω, hΩ, hmetric⟩ := H.solution.conformal p hp
  refine ⟨Ω, hΩ, ?_⟩
  have hgap : 1 - 2 * S.m p.1 p.2 / S.r p.1 p.2 ≠ 0 :=
    ne_of_gt (H.mass_gap_pos_of_c1 hp)
  apply (eq_div_iff hgap).2
  nlinarith only [hmetric]

/-- The incoming derivative of `λ` is the frozen reduced density at a genuine
interior point. The relative first jet on a closed triangle becomes a classical
derivative here because `0 < u < v < b`. -/
theorem lam_deriv_u_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < b) :
    deriv (fun s => S.lam s v) u =
      (2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v) := by
  let B := (v + b) / 2
  let K := closedCoordTriangle 0 B
  let F : ℝ × ℝ → ℝ := fun p => S.lam p.1 p.2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hp : (u, v) ∈ K := ⟨hu.le, huv.le, hvB.le⟩
  have hpi : (u, v) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact ⟨hu, huv, hvB⟩
  have hF : ContDiffOn ℝ 1 F K := (C1Solution.five_fields_contDiffOn hB hBb H).1
  have hdiff : DifferentiableAt ℝ F (u, v) :=
    ((hF.differentiableOn (by norm_num)).mono interior_subset (u, v) hpi).differentiableAt
      (isOpen_interior.mem_nhds hpi)
  have hunique : UniqueDiffWithinAt ℝ K (u, v) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
      (u, v) (interior_subset hpi)
  have hwithin : fderivWithin ℝ F K (u, v) = fderiv ℝ F (u, v) :=
    fderivWithin_eq_fderiv hunique hdiff
  have hpair : HasDerivAt (fun s : ℝ => (s, v)) (1, 0) u :=
    (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
  have hcomp : HasDerivAt (fun s => S.lam s v)
      (fderiv ℝ F (u, v) (1, 0)) u := by
    simpa only [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt u hpair
  have hjet := (C1Solution.four_mixed_coordinate_jets hB hBb H hp).1
  rw [hwithin] at hjet
  rw [hcomp.deriv, hjet]
  exact C1Solution.canonicalMixedCoefficient_eq_frozen hB hBb H hu.le huv hvB.le

/-- At a strict interior point, the classical incoming derivative of the
actual radius equals `ν`. The actual radius is compared with its canonical
C¹ representative only on a neighborhood contained in the development. -/
theorem radius_deriv_u_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < b) :
    deriv (fun s => S.r s v) u = S.nu u v := by
  let B := (v + b) / 2
  let K := closedCoordTriangle 0 B
  let F := C1Solution.canonicalRadius S
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hp : (u, v) ∈ K := ⟨hu.le, huv.le, hvB.le⟩
  have hpi : (u, v) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact ⟨hu, huv, hvB⟩
  have hF : ContDiffOn ℝ 1 F K := C1Solution.canonicalRadius_contDiffOn hB hBb H
  have hdiff : DifferentiableAt ℝ F (u, v) :=
    ((hF.differentiableOn (by norm_num)).mono interior_subset (u, v) hpi).differentiableAt
      (isOpen_interior.mem_nhds hpi)
  have hunique : UniqueDiffWithinAt ℝ K (u, v) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
      (u, v) (interior_subset hpi)
  have hwithin : fderivWithin ℝ F K (u, v) = fderiv ℝ F (u, v) :=
    fderivWithin_eq_fderiv hunique hdiff
  have hpair : HasDerivAt (fun s : ℝ => (s, v)) (1, 0) u :=
    (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
  have hcomp : HasDerivAt (fun s => F (s, v))
      (fderiv ℝ F (u, v) (1, 0)) u := by
    simpa only [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt u hpair
  have hjet := C1Solution.canonicalRadius_horizontal_jet hB hBb H hp
  rw [hwithin] at hjet
  rw [hjet] at hcomp
  have heq : (fun s => S.r s v) =ᶠ[𝓝 u] (fun s => F (s, v)) := by
    filter_upwards [Ioo_mem_nhds hu huv] with s hs
    exact (C1Solution.canonicalRadius_eq_radius hB hBb H hs.1.le hs.2 hvB.le).symm
  exact (hcomp.congr_of_eventuallyEq heq).deriv

/-- At a strict interior point, the classical outgoing derivative of the
actual radius equals `λ`. -/
theorem radius_deriv_v_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < b) :
    deriv (S.r u) v = S.lam u v := by
  let B := (v + b) / 2
  let K := closedCoordTriangle 0 B
  let F := C1Solution.canonicalRadius S
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hp : (u, v) ∈ K := ⟨hu.le, huv.le, hvB.le⟩
  have hpi : (u, v) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact ⟨hu, huv, hvB⟩
  have hF : ContDiffOn ℝ 1 F K := C1Solution.canonicalRadius_contDiffOn hB hBb H
  have hdiff : DifferentiableAt ℝ F (u, v) :=
    ((hF.differentiableOn (by norm_num)).mono interior_subset (u, v) hpi).differentiableAt
      (isOpen_interior.mem_nhds hpi)
  have hunique : UniqueDiffWithinAt ℝ K (u, v) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
      (u, v) (interior_subset hpi)
  have hwithin : fderivWithin ℝ F K (u, v) = fderiv ℝ F (u, v) :=
    fderivWithin_eq_fderiv hunique hdiff
  have hpair : HasDerivAt (fun s : ℝ => (u, s)) (0, 1) v :=
    (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
  have hcomp : HasDerivAt (fun s => F (u, s))
      (fderiv ℝ F (u, v) (0, 1)) v := by
    simpa only [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt v hpair
  have hjet := C1Solution.canonicalRadius_vertical_jet hB hBb H hp
  rw [hwithin] at hjet
  rw [hjet] at hcomp
  have heq : S.r u =ᶠ[𝓝 v] (fun s => F (u, s)) := by
    filter_upwards [Ioo_mem_nhds huv hvB] with s hs
    exact (C1Solution.canonicalRadius_eq_radius hB hBb H hu.le hs.1 hs.2.le).symm
  exact (hcomp.congr_of_eventuallyEq heq).deriv

/-- The coordinate form of the metric mass identity (1.5) on the reduced C¹
carrier, using the actual classical first derivatives of `r`. This does not
define the original metric tensor as a separate object. -/
theorem reduced_metric_contraction_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v Ω : ℝ} (hu : 0 < u)
    (hp : (u, v) ∈ developmentWithInitialEdge b)
    (hΩ : 0 < Ω)
    (hmetric : (1 - 2 * S.m u v / S.r u v) * Ω ^ 2 =
      -(4 * S.lam u v * S.nu u v)) :
    1 - 2 * S.m u v / S.r u v =
      -(4 * deriv (fun s => S.r s v) u * deriv (S.r u) v) / Ω ^ 2 := by
  rw [H.radius_deriv_u_of_c1 hu hp.2.1 hp.2.2,
    H.radius_deriv_v_of_c1 hu hp.2.1 hp.2.2]
  apply (eq_div_iff (pow_ne_zero 2 (ne_of_gt hΩ))).2
  nlinarith only [hmetric]

/-- The `r_uv = λ_u` notation is an equality of actual classical iterated
derivatives at every strict interior point of the reduced development. -/
theorem radius_mixed_deriv_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < b) :
    deriv (fun s => deriv (S.r s) v) u =
      deriv (fun s => S.lam s v) u := by
  have heq : (fun s => deriv (S.r s) v) =ᶠ[𝓝 u]
      (fun s => S.lam s v) := by
    filter_upwards [Ioo_mem_nhds hu huv] with s hs
    exact H.radius_deriv_v_of_c1 hs.1 hs.2 hv
  exact heq.deriv_eq

/-- Equation (1.4a) at an interior point of the **reduced C¹ carrier**, for
any positive pointwise witness of the frozen conformal clause. Here the mixed derivative `∂u∂v r` is
represented by `∂u λ`; the classical derivative bridge is
`lam_deriv_u_of_c1`. The original-system equation is not a field of
`IsC1Solution` and is not asserted for an arbitrary original carrier. -/
theorem radial_einstein_equation_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v Ω : ℝ} (hu : 0 < u)
    (hp : (u, v) ∈ developmentWithInitialEdge b)
    (_hΩ : 0 < Ω)
    (hmetric : (1 - 2 * S.m u v / S.r u v) * Ω ^ 2 =
      -(4 * S.lam u v * S.nu u v)) :
    S.r u v * deriv (fun s => S.lam s v) u +
      S.nu u v * S.lam u v = -(Ω ^ 2) / 4 := by
  have hderiv := H.lam_deriv_u_of_c1 hu hp.2.1 hp.2.2
  have hr : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hp)
  have hgap : 1 - 2 * S.m u v / S.r u v ≠ 0 :=
    ne_of_gt (H.mass_gap_pos_of_c1 hp)
  have hrm : S.r u v - 2 * S.m u v ≠ 0 := by
    have heq : (1 - 2 * S.m u v / S.r u v) * S.r u v =
        S.r u v - 2 * S.m u v := by field_simp
    rw [← heq]
    exact mul_ne_zero hgap hr
  rw [hderiv]
  calc
    S.r u v *
        ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
          ((1 - 2 * S.m u v / S.r u v) * S.r u v)) +
        S.nu u v * S.lam u v =
        S.lam u v * S.nu u v /
          (1 - 2 * S.m u v / S.r u v) := by
            field_simp [hr, hgap, hrm]
            ring
    _ = -(Ω ^ 2) / 4 := by
      apply (div_eq_iff hgap).2
      nlinarith only [hmetric]

/-- The radial identity also holds at the initial edge as a *relative* first
jet of `λ` on a smaller closed triangle. This is the boundary interpretation
available from the reduced C¹ carrier; it does not assert a two-sided
classical derivative of an arbitrary total field at `u = 0`. -/
theorem radial_einstein_equation_within_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v Ω : ℝ}
    (hp : (u, v) ∈ developmentWithInitialEdge b)
    (_hΩ : 0 < Ω)
    (hmetric : (1 - 2 * S.m u v / S.r u v) * Ω ^ 2 =
      -(4 * S.lam u v * S.nu u v)) :
    S.r u v *
        (fderivWithin ℝ (fun q : ℝ × ℝ => S.lam q.1 q.2)
          (closedCoordTriangle 0 ((v + b) / 2)) (u, v)) (1, 0) +
      S.nu u v * S.lam u v = -(Ω ^ 2) / 4 := by
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith [hp.1, hp.2.1, hp.2.2]
  have hBb : B < b := by dsimp [B]; linarith [hp.2.2]
  have hvB : v ≤ B := by dsimp [B]; linarith [hp.2.2]
  have hpK : (u, v) ∈ closedCoordTriangle 0 B := ⟨hp.1, hp.2.1.le, hvB⟩
  have hjet := (C1Solution.four_mixed_coordinate_jets hB hBb H hpK).1
  rw [C1Solution.canonicalMixedCoefficient_eq_frozen hB hBb H
    hp.1 hp.2.1 hvB] at hjet
  have hr : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hp)
  have hgap : 1 - 2 * S.m u v / S.r u v ≠ 0 :=
    ne_of_gt (H.mass_gap_pos_of_c1 hp)
  have hrm : S.r u v - 2 * S.m u v ≠ 0 := by
    have heq : (1 - 2 * S.m u v / S.r u v) * S.r u v =
        S.r u v - 2 * S.m u v := by field_simp
    rw [← heq]
    exact mul_ne_zero hgap hr
  change S.r u v *
      (fderivWithin ℝ (fun q : ℝ × ℝ => S.lam q.1 q.2)
        (closedCoordTriangle 0 B) (u, v)) (1, 0) +
      S.nu u v * S.lam u v = -(Ω ^ 2) / 4
  rw [hjet]
  calc
    S.r u v *
        ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
          ((1 - 2 * S.m u v / S.r u v) * S.r u v)) +
        S.nu u v * S.lam u v =
        S.lam u v * S.nu u v /
          (1 - 2 * S.m u v / S.r u v) := by
            field_simp [hr, hgap, hrm]
            ring
    _ = -(Ω ^ 2) / 4 := by
      apply (div_eq_iff hgap).2
      nlinarith only [hmetric]

/-- The same reduced-carrier transfer with all three derivatives written as
classical derivatives of the actual radius. This is the literal interior form
of the original-system display (1.4a). -/
theorem radial_einstein_equation_classical_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v Ω : ℝ} (hu : 0 < u)
    (hp : (u, v) ∈ developmentWithInitialEdge b)
    (hΩ : 0 < Ω)
    (hmetric : (1 - 2 * S.m u v / S.r u v) * Ω ^ 2 =
      -(4 * S.lam u v * S.nu u v)) :
    S.r u v * deriv (fun s => deriv (S.r s) v) u +
      deriv (fun s => S.r s v) u * deriv (S.r u) v = -(Ω ^ 2) / 4 := by
  rw [H.radius_mixed_deriv_of_c1 hu hp.2.1 hp.2.2,
    H.radius_deriv_u_of_c1 hu hp.2.1 hp.2.2,
    H.radius_deriv_v_of_c1 hu hp.2.1 hp.2.2]
  exact H.radial_einstein_equation_of_c1 hu hp hΩ hmetric

end ChristodoulouBV.IsC1Solution

end
