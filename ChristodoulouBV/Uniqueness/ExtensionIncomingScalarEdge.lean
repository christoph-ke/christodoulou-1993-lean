module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarTransport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle

/-!
# Outgoing scalar transport on the initial edge

The closed C¹ jets give a classical outgoing derivative even at `u = 0`,
because the outgoing line is locally inside the closed triangle there.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- A closed triangle C¹ vertical jet gives a classical derivative at every
point strictly inside its vertical fiber, including points on `u = 0`. -/
theorem vertical_hasDerivAt_of_closed_jet {B : ℝ}
    {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F (closedCoordTriangle 0 B))
    {u v g : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvB : v < B)
    (hjet : (fderivWithin ℝ F (closedCoordTriangle 0 B) (u, v)) (0, 1) = g) :
    HasDerivAt (fun t => F (u, t)) g v := by
  let K := closedCoordTriangle 0 B
  have hp : (u, v) ∈ K := ⟨hu, huv.le, hvB.le⟩
  have hdiff : DifferentiableWithinAt ℝ F K (u, v) :=
    hF.differentiableOn (by norm_num) (u, v) hp
  have hpath : HasDerivAt (fun t : ℝ => (u, t)) (0, 1) v :=
    (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
  have hnear : ∀ᶠ t in 𝓝 v, (u, t) ∈ K := by
    filter_upwards [Ioo_mem_nhds huv hvB] with t ht
    exact ⟨hu, ht.1.le, ht.2.le⟩
  have h := hdiff.hasFDerivWithinAt.comp_hasDerivAt v hpath hnear
  change HasDerivAt (fun t => F (u, t))
    ((fderivWithin ℝ F (closedCoordTriangle 0 B) (u, v)) (0, 1)) v at h
  rwa [hjet] at h

/-- The outgoing scalar transport equation holds on the initial edge of a
finite C¹ member, including the endpoint needed by the strip estimate. -/
theorem zeta_hasDerivAt_v_initial_of_c1 {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) b) :
    HasDerivAt (fun t => S.zeta 0 t)
      (-(S.nu 0 v * S.theta 0 v / S.r 0 v)) v := by
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith [hv.1, hv.2]
  have hBb : B < b := by dsimp [B]; linarith [hv.2]
  have hvB : v < B := by dsimp [B]; linarith [hv.2]
  have hpK : (0, v) ∈ closedCoordTriangle 0 B := ⟨le_refl 0, hv.1.le, hvB.le⟩
  have hpU : (0, v) ∈ developmentWithInitialEdge b := ⟨le_refl 0, hv.1, hv.2⟩
  have hr0 : S.r 0 v ≠ 0 := ne_of_gt (H.solution.radius_pos (0, v) hpU)
  have hfour := C1Solution.four_mixed_coordinate_jets hB hBb H hpK
  have hcoeff := C1Solution.canonicalMixedCoefficient_eq_frozen hB hBb H
    (le_refl 0) hv.1 hvB.le
  have hβ : HasDerivAt (fun t => S.beta 0 t)
      ((2 * S.m 0 v / S.r 0 v) * S.lam 0 v * S.nu 0 v /
        ((1 - 2 * S.m 0 v / S.r 0 v) * S.r 0 v) * S.phi 0 v) v := by
    convert vertical_hasDerivAt_of_closed_jet
      (C1Solution.beta_contDiffOn hB hBb H) (le_refl 0) hv.1 hvB hfour.2.2.2 using 1
    rw [hcoeff]
  have hnu : HasDerivAt (fun t => S.nu 0 t)
      ((2 * S.m 0 v / S.r 0 v) * S.lam 0 v * S.nu 0 v /
        ((1 - 2 * S.m 0 v / S.r 0 v) * S.r 0 v)) v := by
    convert vertical_hasDerivAt_of_closed_jet
      (C1Solution.five_fields_contDiffOn hB hBb H).2.1
      (le_refl 0) hv.1 hvB hfour.2.1 using 1
    rw [hcoeff]
  have hphiJet := C1Solution.theta_eq_canonicalRadius_mul_phi_vertical_jet
    hB hBb H hpK
  rw [C1Solution.canonicalRadius_eq_radius hB hBb H (le_refl 0) hv.1 hvB.le]
    at hphiJet
  have hphi0 := vertical_hasDerivAt_of_closed_jet
    (C1Solution.five_fields_contDiffOn hB hBb H).2.2.1
    (le_refl 0) hv.1 hvB (g :=
      (fderivWithin ℝ (fun q : ℝ × ℝ => S.phi q.1 q.2)
        (closedCoordTriangle 0 B) (0, v)) (0, 1)) rfl
  have hphi : HasDerivAt (fun t => S.phi 0 t) (S.theta 0 v / S.r 0 v) v := by
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
