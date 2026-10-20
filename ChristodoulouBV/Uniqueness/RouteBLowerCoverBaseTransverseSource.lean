module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseTransverseMixed
public import ChristodoulouBV.Uniqueness.RouteBLowerCoverTransverseCoefficients
import ChristodoulouBV.Uniqueness.ExtensionIncomingQuotientC1
import ChristodoulouBV.Uniqueness.ExtensionStarTraceScalarIncoming
import ChristodoulouBV.C1Solution.ExtractionMass
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Incoming derivative of the finite outgoing sources

The mass, radius, quotient, and scalar incoming equations give the explicit
derivatives needed in the transport equations for `νᵤ` and `βᵤ`.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The finite mixed source `K = 2mκν/r²` has incoming derivative
`A νᵤ + Aᵤν`, with the latter written in continuous lower-order fields. -/
theorem finite_grav_hasDerivAt_u
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v P : ℝ} (hu : 0 < u) (huv : u < v) (hvb : v < b)
    (hν : HasDerivAt (fun t => S.nu t v) P u) :
    HasDerivAt
      (fun t => 2 * S.m t v *
        (S.lam t v / (1 - 2 * S.m t v / S.r t v)) *
        S.nu t v / S.r t v ^ 2)
      ((2 * S.m u v *
          (S.lam u v / (1 - 2 * S.m u v / S.r u v)) /
          S.r u v ^ 2) * P +
        ((S.lam u v / (1 - 2 * S.m u v / S.r u v)) *
          S.zeta u v ^ 2 / S.r u v ^ 2 -
          4 * S.m u v *
            (S.lam u v / (1 - 2 * S.m u v / S.r u v)) *
            S.nu u v ^ 2 / S.r u v ^ 3)) u := by
  let B : ℝ := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith only [hu, huv, hvb]
  have hBb : B < b := by dsimp [B]; linarith only [hvb]
  have hvB : v < B := by dsimp [B]; linarith only [hvb]
  have hpK : (u, v) ∈ openCoordTriangle 0 B := ⟨hu, huv, hvB⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge b := ⟨hu.le, huv, hvb⟩
  have hrpos := H.solution.radius_pos (u, v) hpU
  have hνneg := (H.reduced_signs_of_c1 hpU).1
  have hr : HasDerivAt (fun t => S.r t v) (S.nu u v) u := by
    have hcanonical : DifferentiableAt ℝ
        (fun t => C1Solution.canonicalRadius S (t, v)) u := by
      have hi : (u, v) ∈ interior (closedCoordTriangle 0 B) := by
        rw [interior_closedCoordTriangle]
        exact hpK
      have hd := ((C1Solution.canonicalRadius_contDiffOn hB hBb H).differentiableOn
        (by norm_num)).mono interior_subset (u, v) hi |>.differentiableAt
        (isOpen_interior.mem_nhds hi)
      exact hd.comp u
        (((hasDerivAt_id' u).prodMk (hasDerivAt_const u v)).differentiableAt)
    have heq : (fun t => C1Solution.canonicalRadius S (t, v)) =ᶠ[𝓝 u]
        (fun t => S.r t v) := by
      filter_upwards [Ioo_mem_nhds hu huv] with t ht
      exact C1Solution.canonicalRadius_eq_radius hB hBb H
        ht.1.le ht.2 hvB.le
    have hd := hcanonical.congr_of_eventuallyEq heq.symm |>.hasDerivAt
    rw [H.radius_deriv_u_of_c1 hu huv hvb] at hd
    exact hd
  have hm : HasDerivAt (fun t => S.m t v)
      ((1 - 2 * S.m u v / S.r u v) * S.zeta u v ^ 2 /
        (2 * S.nu u v)) u := by
    have hd := C1Solution.canonicalMass_horizontal_hasDerivAt hB hBb H hpK
    have heq : (fun t => C1Solution.canonicalMass b S (t, v)) =ᶠ[𝓝 u]
        (fun t => S.m t v) := by
      filter_upwards [Ioo_mem_nhds hu huv] with t ht
      exact C1Solution.canonicalMass_eq_mass
        ⟨ht.1.le, ht.2, hvb⟩
    have hd' := hd.congr_of_eventuallyEq heq.symm
    convert hd' using 1
    dsimp [C1Solution.canonicalMassIncomingDensity]
    rw [C1Solution.canonicalMassRatio_eq_mass_ratio H hpU]
  have hκ : HasDerivAt
      (fun t => S.lam t v / (1 - 2 * S.m t v / S.r t v))
      ((S.lam u v / (1 - 2 * S.m u v / S.r u v)) *
        S.zeta u v ^ 2 / (S.r u v * S.nu u v)) u := by
    convert incoming_quotient_hasDerivAt_u_of_c1 H hu huv hvb using 1
    field_simp [ne_of_lt hνneg]
  exact grav_hasDerivAt_of_incoming_equations hr hm hκ hν
    (ne_of_gt hrpos) (ne_of_lt hνneg)

/-- Differentiating `Kφ` gives the source for the finite `βᵤ` equation. -/
theorem finite_grav_phi_hasDerivAt_u
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v P : ℝ} (hu : 0 < u) (huv : u < v) (hvb : v < b)
    (hν : HasDerivAt (fun t => S.nu t v) P u) :
    HasDerivAt
      (fun t => (2 * S.m t v *
        (S.lam t v / (1 - 2 * S.m t v / S.r t v)) *
        S.nu t v / S.r t v ^ 2) * S.phi t v)
      (((2 * S.m u v *
          (S.lam u v / (1 - 2 * S.m u v / S.r u v)) /
          S.r u v ^ 2) * P +
        ((S.lam u v / (1 - 2 * S.m u v / S.r u v)) *
          S.zeta u v ^ 2 / S.r u v ^ 2 -
          4 * S.m u v *
            (S.lam u v / (1 - 2 * S.m u v / S.r u v)) *
            S.nu u v ^ 2 / S.r u v ^ 3)) * S.phi u v +
        (2 * S.m u v *
          (S.lam u v / (1 - 2 * S.m u v / S.r u v)) /
          S.r u v ^ 2) * S.nu u v *
          (S.zeta u v / S.r u v)) u := by
  have hφ := phi_hasDerivAt_u_of_c1 H
    (show (u, v) ∈ openDevelopment 0 b from
      ⟨⟨hu, huv.trans hvb⟩, ⟨huv, hvb⟩⟩)
  convert (finite_grav_hasDerivAt_u H hu huv hvb hν).mul hφ using 1
  ring

end ChristodoulouBV.Uniqueness

end
