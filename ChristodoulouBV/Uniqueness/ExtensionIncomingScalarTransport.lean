module

public import ChristodoulouBV.C1Solution.ExtractionJets
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Off-axis scalar transport in the C¹ class

The first coordinate jets supplied by the frozen integral equations yield
the classical `θ_u` and `ζ_v` equations without a second derivative of `φ`.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

private theorem horizontal_hasDerivAt_of_jet {B : ℝ}
    (hB : 0 < B) {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B))
    {u v g : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B)
    (hjet : (fderivWithin ℝ F (closedCoordTriangle 0 B) (u, v)) (1, 0) = g) :
    HasDerivAt (fun t => F (t, v)) g u := by
  let K := closedCoordTriangle 0 B
  have hqi : (u, v) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact hp
  have hdiff : DifferentiableAt ℝ F (u, v) :=
    ((hF.differentiableOn (by norm_num)).mono interior_subset (u, v) hqi).differentiableAt
      (isOpen_interior.mem_nhds hqi)
  have hwithin : fderivWithin ℝ F K (u, v) = fderiv ℝ F (u, v) :=
    fderivWithin_eq_fderiv
      ((uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
        (by rw [interior_closedCoordTriangle]
            exact openCoordTriangle_nonempty hB)) (u, v) (interior_subset hqi)) hdiff
  have hpair : HasDerivAt (fun t : ℝ => (t, v)) (1, 0) u :=
    (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
  have hcomp : HasDerivAt (fun t => F (t, v))
      (fderiv ℝ F (u, v) (1, 0)) u := by
    simpa only [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt u hpair
  rw [hwithin] at hjet
  rwa [hjet] at hcomp

private theorem vertical_hasDerivAt_of_jet {B : ℝ}
    (hB : 0 < B) {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B))
    {u v g : ℝ} (hp : (u, v) ∈ openCoordTriangle 0 B)
    (hjet : (fderivWithin ℝ F (closedCoordTriangle 0 B) (u, v)) (0, 1) = g) :
    HasDerivAt (fun t => F (u, t)) g v := by
  let K := closedCoordTriangle 0 B
  have hqi : (u, v) ∈ interior K := by
    rw [interior_closedCoordTriangle]
    exact hp
  have hdiff : DifferentiableAt ℝ F (u, v) :=
    ((hF.differentiableOn (by norm_num)).mono interior_subset (u, v) hqi).differentiableAt
      (isOpen_interior.mem_nhds hqi)
  have hwithin : fderivWithin ℝ F K (u, v) = fderiv ℝ F (u, v) :=
    fderivWithin_eq_fderiv
      ((uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
        (by rw [interior_closedCoordTriangle]
            exact openCoordTriangle_nonempty hB)) (u, v) (interior_subset hqi)) hdiff
  have hpair : HasDerivAt (fun t : ℝ => (u, t)) (0, 1) v :=
    (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
  have hcomp : HasDerivAt (fun t => F (u, t))
      (fderiv ℝ F (u, v) (0, 1)) v := by
    simpa only [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt v hpair
  rw [hwithin] at hjet
  rwa [hjet] at hcomp

/-- The outgoing radius primitive has its classical derivative at a strict
interior point of a C¹ family member. -/
theorem radius_hasDerivAt_v_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openDevelopment 0 b) :
    HasDerivAt (S.r u) (S.lam u v) v := by
  obtain ⟨⟨hu, _⟩, ⟨huv, hv⟩⟩ := hp
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hpK : (u, v) ∈ openCoordTriangle 0 B := ⟨hu, huv, hvB⟩
  have hpKC : (u, v) ∈ closedCoordTriangle 0 B := ⟨hu.le, huv.le, hvB.le⟩
  have hcanonical := vertical_hasDerivAt_of_jet hB
    (C1Solution.canonicalRadius_contDiffOn hB hBb H) hpK
    (C1Solution.canonicalRadius_vertical_jet hB hBb H hpKC)
  have hEq : S.r u =ᶠ[𝓝 v]
      (fun t => C1Solution.canonicalRadius S (u, t)) := by
    filter_upwards [Ioo_mem_nhds huv hvB] with t ht
    exact (C1Solution.canonicalRadius_eq_radius hB hBb H
      hu.le ht.1 ht.2.le).symm
  exact hcanonical.congr_of_eventuallyEq hEq

/-- The outgoing derivative of the incoming expansion is the mixed radius
coefficient, represented by the C¹ closed-triangle jet. -/
theorem nu_hasDerivAt_v_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openDevelopment 0 b) :
    HasDerivAt (S.nu u)
      ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v)) v := by
  obtain ⟨⟨hu, _⟩, ⟨huv, hv⟩⟩ := hp
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hpK : (u, v) ∈ openCoordTriangle 0 B := ⟨hu, huv, hvB⟩
  have hpKC : (u, v) ∈ closedCoordTriangle 0 B := ⟨hu.le, huv.le, hvB.le⟩
  have hjet := (C1Solution.four_mixed_coordinate_jets hB hBb H hpKC).2.1
  have hcoeff := C1Solution.canonicalMixedCoefficient_eq_frozen hB hBb H
    hu.le huv hvB.le
  convert vertical_hasDerivAt_of_jet hB
    (C1Solution.five_fields_contDiffOn hB hBb H).2.1 hpK hjet using 1
  rw [hcoeff]

/-- The incoming transport equation for the outgoing scalar amplitude. -/
theorem theta_hasDerivAt_u_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openDevelopment 0 b) :
    HasDerivAt (fun t => S.theta t v)
      (-(S.lam u v * S.zeta u v / S.r u v)) u := by
  obtain ⟨⟨hu, _⟩, ⟨huv, hv⟩⟩ := hp
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hpK : (u, v) ∈ openCoordTriangle 0 B := ⟨hu, huv, hvB⟩
  have hpKC : (u, v) ∈ closedCoordTriangle 0 B := ⟨hu.le, huv.le, hvB.le⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge b := ⟨hu.le, huv, hv⟩
  have hr0 : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hfour := C1Solution.four_mixed_coordinate_jets hB hBb H hpKC
  have hcoeff := C1Solution.canonicalMixedCoefficient_eq_frozen hB hBb H
    hu.le huv hvB.le
  have hα : HasDerivAt (fun t => S.alpha t v)
      ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v) * S.phi u v) u := by
    convert horizontal_hasDerivAt_of_jet hB
      (C1Solution.alpha_contDiffOn hB hBb H) hpK hfour.2.2.1 using 1
    rw [hcoeff]
  have hlam : HasDerivAt (fun t => S.lam t v)
      ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v)) u := by
    convert horizontal_hasDerivAt_of_jet hB
      (C1Solution.five_fields_contDiffOn hB hBb H).1 hpK hfour.1 using 1
    rw [hcoeff]
  have hphiJet := C1Solution.zeta_eq_canonicalRadius_mul_phi_horizontal_jet
    hB hBb H hpKC
  rw [C1Solution.canonicalRadius_eq_radius hB hBb H hu.le huv hvB.le] at hphiJet
  have hphi0 := horizontal_hasDerivAt_of_jet hB
    (C1Solution.five_fields_contDiffOn hB hBb H).2.2.1 hpK (g :=
      (fderivWithin ℝ (fun q : ℝ × ℝ => S.phi q.1 q.2)
        (closedCoordTriangle 0 B) (u, v)) (1, 0)) rfl
  have hphi : HasDerivAt (fun t => S.phi t v) (S.zeta u v / S.r u v) u := by
    convert hphi0 using 1
    field_simp
    linarith only [hphiJet]
  have h := hα.sub (hlam.mul hphi)
  unfold Fields.theta
  convert h using 1
  field_simp
  ring

/-- The outgoing transport equation for the incoming scalar amplitude. -/
theorem zeta_hasDerivAt_v_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openDevelopment 0 b) :
    HasDerivAt (fun t => S.zeta u t)
      (-(S.nu u v * S.theta u v / S.r u v)) v := by
  obtain ⟨⟨hu, _⟩, ⟨huv, hv⟩⟩ := hp
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hpK : (u, v) ∈ openCoordTriangle 0 B := ⟨hu, huv, hvB⟩
  have hpKC : (u, v) ∈ closedCoordTriangle 0 B := ⟨hu.le, huv.le, hvB.le⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge b := ⟨hu.le, huv, hv⟩
  have hr0 : S.r u v ≠ 0 := ne_of_gt (H.solution.radius_pos (u, v) hpU)
  have hfour := C1Solution.four_mixed_coordinate_jets hB hBb H hpKC
  have hcoeff := C1Solution.canonicalMixedCoefficient_eq_frozen hB hBb H
    hu.le huv hvB.le
  have hβ : HasDerivAt (fun t => S.beta u t)
      ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v) * S.phi u v) v := by
    convert vertical_hasDerivAt_of_jet hB
      (C1Solution.beta_contDiffOn hB hBb H) hpK hfour.2.2.2 using 1
    rw [hcoeff]
  have hnu : HasDerivAt (fun t => S.nu u t)
      ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v)) v := by
    convert vertical_hasDerivAt_of_jet hB
      (C1Solution.five_fields_contDiffOn hB hBb H).2.1 hpK hfour.2.1 using 1
    rw [hcoeff]
  have hphiJet := C1Solution.theta_eq_canonicalRadius_mul_phi_vertical_jet
    hB hBb H hpKC
  rw [C1Solution.canonicalRadius_eq_radius hB hBb H hu.le huv hvB.le] at hphiJet
  have hphi0 := vertical_hasDerivAt_of_jet hB
    (C1Solution.five_fields_contDiffOn hB hBb H).2.2.1 hpK (g :=
      (fderivWithin ℝ (fun q : ℝ × ℝ => S.phi q.1 q.2)
        (closedCoordTriangle 0 B) (u, v)) (0, 1)) rfl
  have hphi : HasDerivAt (fun t => S.phi u t) (S.theta u v / S.r u v) v := by
    convert hphi0 using 1
    field_simp
    linarith only [hphiJet]
  have h := hβ.sub (hnu.mul hphi)
  unfold Fields.zeta
  convert h using 1
  field_simp
  ring

end ChristodoulouBV.Uniqueness

end
