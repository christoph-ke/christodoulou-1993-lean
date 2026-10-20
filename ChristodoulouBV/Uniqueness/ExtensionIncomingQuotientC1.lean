module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingFluxFamily
public import ChristodoulouBV.Uniqueness.ExtensionIncomingQuotient
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Incoming quotient equation on a C¹ member

The frozen primitives and their C¹ representatives give the classical
incoming equation for the expansion quotient at strict off-axis points.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- At a strict off-axis point of a C¹ member, the quotient solves the
linear equation with the incoming scalar flux as its coefficient. -/
theorem incoming_quotient_hasDerivAt_u_of_c1
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hu : 0 < u) (huv : u < v) (hvb : v < b) :
    HasDerivAt
      (fun t => S.lam t v / (1 - 2 * S.m t v / S.r t v))
      (-(S.zeta u v ^ 2 / (S.r u v * (-S.nu u v)) *
        (S.lam u v / (1 - 2 * S.m u v / S.r u v)))) u := by
  let B : ℝ := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hpK : (u, v) ∈ openCoordTriangle 0 B := ⟨hu, huv, hvB⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge b := ⟨hu.le, huv, hvb⟩
  have hrpos := H.solution.radius_pos (u, v) hpU
  have hnuNeg := (H.reduced_signs_of_c1 hpU).1
  have hqpos := H.mass_gap_pos_of_c1 hpU
  have hRdiff : DifferentiableAt ℝ (fun t => S.r t v) u := by
    have hcanon : DifferentiableAt ℝ
        (fun t => C1Solution.canonicalRadius S (t, v)) u := by
      have hK : (u, v) ∈ interior (closedCoordTriangle 0 B) := by
        rw [interior_closedCoordTriangle]
        exact hpK
      have hd := ((C1Solution.canonicalRadius_contDiffOn hB hBb H).differentiableOn
        (by norm_num)).mono interior_subset (u, v) hK |>.differentiableAt
        (isOpen_interior.mem_nhds hK)
      exact hd.comp u
        ((hasDerivAt_id' u).prodMk (hasDerivAt_const u v)).differentiableAt
    have heq : (fun t => C1Solution.canonicalRadius S (t, v)) =ᶠ[𝓝 u]
        (fun t => S.r t v) := by
      filter_upwards [Ioo_mem_nhds hu huv] with t ht
      exact C1Solution.canonicalRadius_eq_radius hB hBb H
        ht.1.le ht.2 hvB.le
    exact hcanon.congr_of_eventuallyEq heq.symm
  have hR : HasDerivAt (fun t => S.r t v) (S.nu u v) u := by
    have h := hRdiff.hasDerivAt
    rw [H.radius_deriv_u_of_c1 hu huv hvb] at h
    exact h
  have hLdiff : DifferentiableAt ℝ (fun t => S.lam t v) u := by
    have hK : (u, v) ∈ interior (closedCoordTriangle 0 B) := by
      rw [interior_closedCoordTriangle]
      exact hpK
    have hd := (((C1Solution.five_fields_contDiffOn hB hBb H).1.differentiableOn
      (by norm_num)).mono interior_subset (u, v) hK).differentiableAt
      (isOpen_interior.mem_nhds hK)
    exact hd.comp u
      ((hasDerivAt_id' u).prodMk (hasDerivAt_const u v)).differentiableAt
  have hL : HasDerivAt (fun t => S.lam t v)
      ((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
        ((1 - 2 * S.m u v / S.r u v) * S.r u v)) u := by
    have h := hLdiff.hasDerivAt
    rw [H.lam_deriv_u_of_c1 hu huv hvb] at h
    exact h
  have hM : HasDerivAt (fun t => S.m t v)
      ((1 - 2 * S.m u v / S.r u v) * S.zeta u v ^ 2 /
        (2 * S.nu u v)) u := by
    have h := C1Solution.canonicalMass_horizontal_hasDerivAt hB hBb H hpK
    have heq : (fun t => C1Solution.canonicalMass b S (t, v)) =ᶠ[𝓝 u]
        (fun t => S.m t v) := by
      filter_upwards [Ioo_mem_nhds hu huv] with t ht
      exact C1Solution.canonicalMass_eq_mass
        ⟨ht.1.le, ht.2, hvb⟩
    have h' := h.congr_of_eventuallyEq heq.symm
    convert h' using 1
    dsimp [C1Solution.canonicalMassIncomingDensity]
    rw [C1Solution.canonicalMassRatio_eq_mass_ratio H hpU]
  have hκ := incoming_expansion_quotient_hasDerivAt hR hM hL
    (ne_of_gt hrpos) (ne_of_lt hnuNeg) (ne_of_gt hqpos)
  convert hκ using 1
  field_simp [ne_of_lt hnuNeg]

/-- The expansion quotient is continuous on an incoming segment including
the initial edge. The closed canonical radius and mass provide its endpoint
values there. -/
theorem incoming_quotient_continuousOn_of_c1
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u₁ v : ℝ} (hu₁ : 0 ≤ u₁) (hu₁v : u₁ < v) (hvb : v < b) :
    ContinuousOn
      (fun u => S.lam u v / (1 - 2 * S.m u v / S.r u v))
      (Icc (0 : ℝ) u₁) := by
  let B : ℝ := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hmap (u : ℝ) (hu : u ∈ Icc (0 : ℝ) u₁) :
      (u, v) ∈ closedCoordTriangle 0 B := by
    change 0 ≤ u ∧ u ≤ v ∧ v ≤ B
    exact ⟨hu.1, hu.2.trans hu₁v.le, hvB.le⟩
  have hpU (u : ℝ) (hu : u ∈ Icc (0 : ℝ) u₁) :
      (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hu.1, hu.2.trans_lt hu₁v, hvb⟩
  have hlam : ContinuousOn (fun u => S.lam u v) (Icc (0 : ℝ) u₁) :=
    (C1Solution.five_fields_contDiffOn hB hBb H).1.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hmap
  have hr : ContinuousOn (fun u => S.r u v) (Icc (0 : ℝ) u₁) := by
    have hcanon : ContinuousOn
        (fun u => C1Solution.canonicalRadius S (u, v)) (Icc (0 : ℝ) u₁) :=
      (C1Solution.canonicalRadius_contDiffOn hB hBb H).continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn hmap
    apply hcanon.congr
    intro u hu
    exact (C1Solution.canonicalRadius_eq_radius hB hBb H
      hu.1 (hu.2.trans_lt hu₁v) hvB.le).symm
  have hm : ContinuousOn (fun u => S.m u v) (Icc (0 : ℝ) u₁) := by
    have hcanon : ContinuousOn
        (fun u => C1Solution.canonicalMass b S (u, v)) (Icc (0 : ℝ) u₁) :=
      (C1Solution.canonicalMass_contDiffOn hB hBb H).continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn hmap
    apply hcanon.congr
    intro u hu
    exact (C1Solution.canonicalMass_eq_mass (hpU u hu)).symm
  have hrne : ∀ u ∈ Icc (0 : ℝ) u₁, S.r u v ≠ 0 :=
    fun u hu => ne_of_gt (H.solution.radius_pos (u, v) (hpU u hu))
  have hq : ContinuousOn (fun u => 1 - 2 * S.m u v / S.r u v)
      (Icc (0 : ℝ) u₁) :=
    continuousOn_const.sub ((continuousOn_const.mul hm).div hr hrne)
  have hqne : ∀ u ∈ Icc (0 : ℝ) u₁,
      1 - 2 * S.m u v / S.r u v ≠ 0 :=
    fun u hu => ne_of_gt (H.mass_gap_pos_of_c1 (hpU u hu))
  exact hlam.div hq hqne

end ChristodoulouBV.Uniqueness

end
