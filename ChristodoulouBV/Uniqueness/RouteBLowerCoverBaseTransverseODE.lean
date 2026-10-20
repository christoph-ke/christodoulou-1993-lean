module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseTransverseSource
import ChristodoulouBV.Uniqueness.RouteBLowerCoverJetClosure
import ChristodoulouBV.C1Solution.ExtractionRemovable
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Transverse outgoing equations on a finite member

The incoming coordinate jets of `ν` and `β` obey linear outgoing equations
at strict interior points of each finite solution.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

private theorem grav_expression_eq_frozen
    (m lam nu r : ℝ) (hr : r ≠ 0) :
    (2 * m / r) * lam * nu / ((1 - 2 * m / r) * r) =
      2 * m * (lam / (1 - 2 * m / r)) * nu / r ^ 2 := by
  field_simp [hr]

/-- On a finite member, the incoming jet of `ν` satisfies the outgoing
linear ODE with coefficient `A = 2mκ/r²` and source `Aᵤν`. -/
theorem finite_nu_incoming_jet_hasDerivAt_v
    {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    let K := closedCoordTriangle 0 B
    let P : ℝ → ℝ := fun t =>
      (fderivWithin ℝ (fun q : ℝ × ℝ => S.nu q.1 q.2) K (u, t)) (1, 0)
    HasDerivAt P
      ((2 * S.m u v *
          (S.lam u v / (1 - 2 * S.m u v / S.r u v)) /
          S.r u v ^ 2) * P v +
        ((S.lam u v / (1 - 2 * S.m u v / S.r u v)) *
          S.zeta u v ^ 2 / S.r u v ^ 2 -
          4 * S.m u v *
            (S.lam u v / (1 - 2 * S.m u v / S.r u v)) *
            S.nu u v ^ 2 / S.r u v ^ 3)) v := by
  dsimp only
  let K := closedCoordTriangle 0 B
  let F : ℝ × ℝ → ℝ := fun q => S.nu q.1 q.2
  let G := C1Solution.canonicalMixedCoefficient b S
  let P : ℝ → ℝ := fun t => (fderivWithin ℝ F K (u, t)) (1, 0)
  have hu : 0 < u := hp.1
  have huv : u < v := hp.2.1
  have hvB : v < B := hp.2.2
  have hvb : v < b := hvB.trans hBb
  have hpK : (u, v) ∈ K := ⟨hu.le, huv.le, hvB.le⟩
  have hi : (u, v) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact hp
  have hFC1 := (C1Solution.five_fields_contDiffOn hB hBb H).2.1
  have hGC1 := C1Solution.canonicalMixedCoefficient_contDiffOn hB hBb H
  have hFdiff : DifferentiableAt ℝ F (u, v) :=
    ((hFC1.differentiableOn (by norm_num)).mono interior_subset
      (u, v) hi).differentiableAt (isOpen_interior.mem_nhds hi)
  have hGdiff : DifferentiableAt ℝ G (u, v) :=
    ((hGC1.differentiableOn (by norm_num)).mono interior_subset
      (u, v) hi).differentiableAt (isOpen_interior.mem_nhds hi)
  have hunique : UniqueDiffWithinAt ℝ K (u, v) :=
    (uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)) (u, v) hpK
  have hwithinF : fderivWithin ℝ F K (u, v) = fderiv ℝ F (u, v) :=
    fderivWithin_eq_fderiv hunique hFdiff
  have hwithinG : fderivWithin ℝ G K (u, v) = fderiv ℝ G (u, v) :=
    fderivWithin_eq_fderiv hunique hGdiff
  have hν : HasDerivAt (fun t => S.nu t v) (P v) u := by
    have hpair : HasDerivAt (fun t : ℝ => (t, v)) (1, 0) u :=
      (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
    simpa only [P, F, hwithinF, Function.comp_def] using
      hFdiff.hasFDerivAt.comp_hasDerivAt u hpair
  have hraw := finite_grav_hasDerivAt_u H hu huv hvb hν
  have hEq : (fun t => G (t, v)) =ᶠ[𝓝 u]
      (fun t => 2 * S.m t v *
        (S.lam t v / (1 - 2 * S.m t v / S.r t v)) *
        S.nu t v / S.r t v ^ 2) := by
    filter_upwards [Ioo_mem_nhds hu huv] with t ht
    have htU : (t, v) ∈ developmentWithInitialEdge b :=
      ⟨ht.1.le, ht.2, hvb⟩
    have hr : S.r t v ≠ 0 :=
      ne_of_gt (H.solution.radius_pos (t, v) htU)
    change C1Solution.canonicalMixedCoefficient b S (t, v) = _
    rw [C1Solution.canonicalMixedCoefficient_eq_frozen
      hB hBb H ht.1.le ht.2 hvB.le]
    exact grav_expression_eq_frozen _ _ _ _ hr
  have hGderiv := hraw.congr_of_eventuallyEq hEq
  have hGjet : (fderivWithin ℝ G K (u, v)) (1, 0) =
      (2 * S.m u v *
        (S.lam u v / (1 - 2 * S.m u v / S.r u v)) /
        S.r u v ^ 2) * P v +
        ((S.lam u v / (1 - 2 * S.m u v / S.r u v)) *
          S.zeta u v ^ 2 / S.r u v ^ 2 -
          4 * S.m u v *
            (S.lam u v / (1 - 2 * S.m u v / S.r u v)) *
            S.nu u v ^ 2 / S.r u v ^ 3) := by
    rw [hwithinG]
    exact fderiv_apply_first_of_hasDerivAt hGdiff hGderiv
  have hsource (q : ℝ × ℝ) (hq : q ∈ K) :
      (fderivWithin ℝ F K q) (0, 1) = G q :=
    (C1Solution.four_mixed_coordinate_jets hB hBb H hq).2.1
  have hmixed := hasDerivAt_horizontal_jet_of_vertical_source_on_triangle
    hB hFC1 hGC1 hsource hp
  change HasDerivAt P ((fderivWithin ℝ G K (u, v)) (1, 0)) v at hmixed
  rw [hGjet] at hmixed
  exact hmixed

/-- On a finite member, the incoming jet of `β` has outgoing source
`(Aνᵤ + Aᵤν)φ + Aνζ/r`. -/
theorem finite_beta_incoming_jet_hasDerivAt_v
    {b B : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B) :
    let K := closedCoordTriangle 0 B
    let P : ℝ → ℝ := fun t =>
      (fderivWithin ℝ (fun q : ℝ × ℝ => S.nu q.1 q.2) K (u, t)) (1, 0)
    let Q : ℝ → ℝ := fun t =>
      (fderivWithin ℝ (fun q : ℝ × ℝ => S.beta q.1 q.2) K (u, t)) (1, 0)
    HasDerivAt Q
      (((2 * S.m u v *
          (S.lam u v / (1 - 2 * S.m u v / S.r u v)) /
          S.r u v ^ 2) * P v +
        ((S.lam u v / (1 - 2 * S.m u v / S.r u v)) *
          S.zeta u v ^ 2 / S.r u v ^ 2 -
          4 * S.m u v *
            (S.lam u v / (1 - 2 * S.m u v / S.r u v)) *
            S.nu u v ^ 2 / S.r u v ^ 3)) * S.phi u v +
        (2 * S.m u v *
          (S.lam u v / (1 - 2 * S.m u v / S.r u v)) /
          S.r u v ^ 2) * S.nu u v *
          (S.zeta u v / S.r u v)) v := by
  dsimp only
  let K := closedCoordTriangle 0 B
  let N : ℝ × ℝ → ℝ := fun q => S.nu q.1 q.2
  let F : ℝ × ℝ → ℝ := fun q => S.beta q.1 q.2
  let G : ℝ × ℝ → ℝ := fun q =>
    C1Solution.canonicalMixedCoefficient b S q * S.phi q.1 q.2
  let P : ℝ → ℝ := fun t => (fderivWithin ℝ N K (u, t)) (1, 0)
  let Q : ℝ → ℝ := fun t => (fderivWithin ℝ F K (u, t)) (1, 0)
  have hu : 0 < u := hp.1
  have huv : u < v := hp.2.1
  have hvB : v < B := hp.2.2
  have hvb : v < b := hvB.trans hBb
  have hpK : (u, v) ∈ K := ⟨hu.le, huv.le, hvB.le⟩
  have hi : (u, v) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact hp
  have hNC1 := (C1Solution.five_fields_contDiffOn hB hBb H).2.1
  have hFC1 := C1Solution.beta_contDiffOn hB hBb H
  have hGC1 := (C1Solution.canonicalMixedCoefficient_contDiffOn hB hBb H).mul
    (C1Solution.five_fields_contDiffOn hB hBb H).2.2.1
  have hNdiff : DifferentiableAt ℝ N (u, v) :=
    ((hNC1.differentiableOn (by norm_num)).mono interior_subset
      (u, v) hi).differentiableAt (isOpen_interior.mem_nhds hi)
  have hGdiff : DifferentiableAt ℝ G (u, v) :=
    ((hGC1.differentiableOn (by norm_num)).mono interior_subset
      (u, v) hi).differentiableAt (isOpen_interior.mem_nhds hi)
  have hunique : UniqueDiffWithinAt ℝ K (u, v) :=
    (uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)) (u, v) hpK
  have hwithinN : fderivWithin ℝ N K (u, v) = fderiv ℝ N (u, v) :=
    fderivWithin_eq_fderiv hunique hNdiff
  have hwithinG : fderivWithin ℝ G K (u, v) = fderiv ℝ G (u, v) :=
    fderivWithin_eq_fderiv hunique hGdiff
  have hν : HasDerivAt (fun t => S.nu t v) (P v) u := by
    have hpair : HasDerivAt (fun t : ℝ => (t, v)) (1, 0) u :=
      (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
    simpa only [P, N, hwithinN, Function.comp_def] using
      hNdiff.hasFDerivAt.comp_hasDerivAt u hpair
  have hraw := finite_grav_phi_hasDerivAt_u H hu huv hvb hν
  have hEq : (fun t => G (t, v)) =ᶠ[𝓝 u]
      (fun t => (2 * S.m t v *
        (S.lam t v / (1 - 2 * S.m t v / S.r t v)) *
        S.nu t v / S.r t v ^ 2) * S.phi t v) := by
    filter_upwards [Ioo_mem_nhds hu huv] with t ht
    have htU : (t, v) ∈ developmentWithInitialEdge b :=
      ⟨ht.1.le, ht.2, hvb⟩
    have hr : S.r t v ≠ 0 :=
      ne_of_gt (H.solution.radius_pos (t, v) htU)
    dsimp [G]
    rw [C1Solution.canonicalMixedCoefficient_eq_frozen
      hB hBb H ht.1.le ht.2 hvB.le]
    rw [grav_expression_eq_frozen _ _ _ _ hr]
  have hGderiv := hraw.congr_of_eventuallyEq hEq
  have hGjet : (fderivWithin ℝ G K (u, v)) (1, 0) =
      ((2 * S.m u v *
          (S.lam u v / (1 - 2 * S.m u v / S.r u v)) /
          S.r u v ^ 2) * P v +
        ((S.lam u v / (1 - 2 * S.m u v / S.r u v)) *
          S.zeta u v ^ 2 / S.r u v ^ 2 -
          4 * S.m u v *
            (S.lam u v / (1 - 2 * S.m u v / S.r u v)) *
            S.nu u v ^ 2 / S.r u v ^ 3)) * S.phi u v +
        (2 * S.m u v *
          (S.lam u v / (1 - 2 * S.m u v / S.r u v)) /
          S.r u v ^ 2) * S.nu u v *
          (S.zeta u v / S.r u v) := by
    rw [hwithinG]
    exact fderiv_apply_first_of_hasDerivAt hGdiff hGderiv
  have hsource (q : ℝ × ℝ) (hq : q ∈ K) :
      (fderivWithin ℝ F K q) (0, 1) = G q :=
    (C1Solution.four_mixed_coordinate_jets hB hBb H hq).2.2.2
  have hmixed := hasDerivAt_horizontal_jet_of_vertical_source_on_triangle
    hB hFC1 hGC1 hsource hp
  change HasDerivAt Q ((fderivWithin ℝ G K (u, v)) (1, 0)) v at hmixed
  rw [hGjet] at hmixed
  exact hmixed

end ChristodoulouBV.Uniqueness

end
