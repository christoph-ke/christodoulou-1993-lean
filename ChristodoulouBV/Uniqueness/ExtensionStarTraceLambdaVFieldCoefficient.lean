module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceLambdaVCoefficient
public import ChristodoulouBV.Uniqueness.ExtensionTransportEquation
import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarTransport
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Outgoing derivative of the mixed field coefficient

The canonical C¹ mass and radius agree with the frozen fields off axis.
Their classical outgoing derivatives give equation (8) for each old member.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The mass ratio has the outgoing derivative prescribed by the reduced
mass equation at every strict interior point. -/
theorem mass_ratio_hasDerivAt_v_of_c1
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openDevelopment 0 b) :
    HasDerivAt (fun t => 2 * S.m u t / S.r u t)
      ((1 - 2 * S.m u v / S.r u v) * (S.theta u v)^2 /
        (S.r u v * S.lam u v) -
        (2 * S.m u v / S.r u v) * S.lam u v / S.r u v) v := by
  obtain ⟨⟨hu, _⟩, ⟨huv, hv⟩⟩ := hp
  let B : ℝ := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hpi : (u, v) ∈ interior (closedCoordTriangle 0 B) := by
    rw [interior_closedCoordTriangle]
    exact ⟨hu, huv, hvB⟩
  have hmcanon : DifferentiableAt ℝ
      (fun t => C1Solution.canonicalMass b S (u, t)) v := by
    have hd : DifferentiableAt ℝ (C1Solution.canonicalMass b S) (u, v) :=
      (((C1Solution.canonicalMass_contDiffOn hB hBb H).differentiableOn
        (by norm_num)).mono interior_subset (u, v) hpi).differentiableAt
        (isOpen_interior.mem_nhds hpi)
    exact hd.comp v
      ((hasDerivAt_const v u).prodMk (hasDerivAt_id' v)).differentiableAt
  have hmeq : (fun t => C1Solution.canonicalMass b S (u, t)) =ᶠ[𝓝 v]
      S.m u := by
    filter_upwards [Ioo_mem_nhds huv hv] with t ht
    exact C1Solution.canonicalMass_eq_mass
      (show (u, t) ∈ developmentWithInitialEdge b from
        ⟨hu.le, ht.1, ht.2⟩)
  have hm : DifferentiableAt ℝ (S.m u) v :=
    hmcanon.congr_of_eventuallyEq hmeq.symm
  have hr := radius_hasDerivAt_v_of_c1 H
    (show (u, v) ∈ openDevelopment 0 b from
      ⟨⟨hu, huv.trans hv⟩, ⟨huv, hv⟩⟩)
  have hrne : S.r u v ≠ 0 :=
    ne_of_gt (H.solution.radius_pos (u, v) ⟨hu.le, huv, hv⟩)
  have hμdiff : DifferentiableAt ℝ
      (fun t => 2 * S.m u t / S.r u t) v :=
    ((hm.hasDerivAt.const_mul 2).div hr hrne).differentiableAt
  have h := hμdiff.hasDerivAt
  rw [mass_ratio_deriv_v H
    (show (u, v) ∈ openDevelopment 0 b from
      ⟨⟨hu, huv.trans hv⟩, ⟨huv, hv⟩⟩)] at h
  exact h

/-- Equation (8) for the actual mixed coefficient of one C¹ old member. -/
theorem mixed_coefficient_hasDerivAt_v_of_c1
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openDevelopment 0 b) :
    HasDerivAt
      (fun t =>
        (2 * S.m u t / S.r u t) /
          ((1 - 2 * S.m u t / S.r u t) * S.r u t))
      (S.lam u v * (S.theta u v / S.lam u v) ^ 2 /
          ((1 - 2 * S.m u v / S.r u v) * (S.r u v) ^ 2) -
        (2 * S.m u v / S.r u v) * S.lam u v *
          (1 / (1 - 2 * S.m u v / S.r u v) ^ 2 +
            1 / (1 - 2 * S.m u v / S.r u v)) / (S.r u v) ^ 2) v := by
  have hpU : (u, v) ∈ developmentWithInitialEdge b :=
    ⟨hp.1.1.le, hp.2.1, hp.2.2⟩
  have hr : 0 < S.r u v := H.solution.radius_pos (u, v) hpU
  have hq : 0 < 1 - 2 * S.m u v / S.r u v :=
    H.mass_gap_pos_of_c1 hpU
  have hl : S.lam u v ≠ 0 :=
    ne_of_gt (H.solution.lam_pos (u, v) hpU)
  have hμ := mass_ratio_hasDerivAt_v_of_c1 H hp
  have hμ' : HasDerivAt (fun t => 2 * S.m u t / S.r u t)
      ((1 - 2 * S.m u v / S.r u v) * S.lam u v *
        (S.theta u v / S.lam u v) ^ 2 / S.r u v -
        (2 * S.m u v / S.r u v) * S.lam u v / S.r u v) v := by
    convert hμ using 1
    field_simp [hl]
  exact mass_ratio_coefficient_hasDerivAt hr hq
    (radius_hasDerivAt_v_of_c1 H hp) hμ'

end ChristodoulouBV.Uniqueness

end
