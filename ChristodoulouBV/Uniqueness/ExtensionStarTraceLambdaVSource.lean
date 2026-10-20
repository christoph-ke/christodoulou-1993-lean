module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceLambdaVFieldCoefficient
import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarTransport
import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarEdge
import ChristodoulouBV.Uniqueness.ExtensionSourceBridge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# Outgoing derivative of the incoming lambda source

The mixed source `λᵤ = ν λ μ/((1-μ)r)` is differentiated once in `v`.
This identifies all three terms in equation (10) before commuting the
characteristic derivatives.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The outgoing derivative of the right side of the `λᵤ` equation is
the linear expression in `λᵥ` displayed in equation (10). -/
theorem lambda_incoming_source_hasDerivAt_v_of_c1
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openDevelopment 0 b) :
    HasDerivAt
      (fun t => S.nu u t * S.lam u t *
        ((2 * S.m u t / S.r u t) /
          ((1 - 2 * S.m u t / S.r u t) * S.r u t)))
      (((2 * S.m u v / S.r u v) * S.lam u v * S.nu u v /
          ((1 - 2 * S.m u v / S.r u v) * S.r u v) *
          S.lam u v + S.nu u v * deriv (S.lam u) v) *
          ((2 * S.m u v / S.r u v) /
            ((1 - 2 * S.m u v / S.r u v) * S.r u v)) +
        S.nu u v * S.lam u v *
          (S.lam u v * (S.theta u v / S.lam u v) ^ 2 /
              ((1 - 2 * S.m u v / S.r u v) * (S.r u v) ^ 2) -
            (2 * S.m u v / S.r u v) * S.lam u v *
              (1 / (1 - 2 * S.m u v / S.r u v) ^ 2 +
                1 / (1 - 2 * S.m u v / S.r u v)) / (S.r u v) ^ 2)) v := by
  obtain ⟨⟨hu, _⟩, ⟨huv, hv⟩⟩ := hp
  let B : ℝ := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hpK : (u, v) ∈ openCoordTriangle 0 B := ⟨hu, huv, hvB⟩
  have hlam := vertical_hasDerivAt_of_closed_jet
    ((C1Solution.five_fields_contDiffOn hB hBb H).1)
    hu.le huv hvB
    (g := (fderivWithin ℝ (fun p : ℝ × ℝ => S.lam p.1 p.2)
      (closedCoordTriangle 0 B) (u, v)) (0, 1)) rfl
  have hnu := nu_hasDerivAt_v_of_c1 H
    (show (u, v) ∈ openDevelopment 0 b from
      ⟨⟨hu, huv.trans hv⟩, ⟨huv, hv⟩⟩)
  have hcoeff := mixed_coefficient_hasDerivAt_v_of_c1 H
    (show (u, v) ∈ openDevelopment 0 b from
      ⟨⟨hu, huv.trans hv⟩, ⟨huv, hv⟩⟩)
  have h := (hnu.mul hlam).mul hcoeff
  have hfun :
      ((S.nu u * fun t => S.lam u t) * fun t =>
        (2 * S.m u t / S.r u t) /
          ((1 - 2 * S.m u t / S.r u t) * S.r u t)) =
      (fun t => S.nu u t * S.lam u t *
        ((2 * S.m u t / S.r u t) /
          ((1 - 2 * S.m u t / S.r u t) * S.r u t))) := by
    funext t
    simp only [Pi.mul_apply]
  rw [hfun] at h
  rw [hlam.deriv]
  simpa only [Prod.fst, Prod.snd, Pi.mul_apply] using h

end ChristodoulouBV.Uniqueness

end
