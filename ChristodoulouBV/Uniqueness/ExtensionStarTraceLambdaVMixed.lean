module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceLambdaVSource
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.MixedPartialTriangle
import ChristodoulouBV.BVSolution.C1InitialCompatibility
import ChristodoulouBV.C1Solution.ExtractionJets
import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarEdge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# The incoming equation for the outgoing derivative of lambda

The mixed partial follows from the C¹ canonical coefficient on each finite
old member. It gives equation (10) at strict interior points.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The fixed initial radius gauge gives the zero incoming seed for the
outgoing derivative of `λ`. -/
theorem lambda_v_initial_eq_zero_of_gauge
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) b, S.r 0 v = v / 2)
    {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) b) :
    deriv (S.lam 0) v = 0 := by
  have heq : S.lam 0 =ᶠ[𝓝 v] (fun _ => (1 / 2 : ℝ)) := by
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with t ht
    exact initial_lam_eq_of_gauge H hr ht
  rw [heq.deriv_eq]
  exact deriv_const v (1 / 2 : ℝ)

/-- The outgoing derivative of `λ` is continuous along every closed incoming
segment that stays off the axis. This includes the endpoint `u = 0`. -/
theorem lambda_v_continuousOn_incoming_of_c1
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvb : v < b) :
    ContinuousOn (fun s => deriv (S.lam s) v) (Icc 0 u) := by
  let B : ℝ := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  let K := closedCoordTriangle 0 B
  let F : ℝ × ℝ → ℝ := fun p => S.lam p.1 p.2
  have hF : ContDiffOn ℝ 1 F K :=
    (C1Solution.five_fields_contDiffOn hB hBb H).1
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  have hmap : MapsTo (fun s : ℝ => (s, v)) (Icc 0 u) K := by
    intro s hs
    exact ⟨hs.1, (hs.2.trans_lt huv).le, hvB.le⟩
  have hjet : ContinuousOn
      (fun s => (fderivWithin ℝ F K (s, v)) (0, 1)) (Icc 0 u) := by
    exact ((hF.continuousOn_fderivWithin hunique (by norm_num)).clm_apply
      continuousOn_const).comp
        (continuous_id.prodMk continuous_const).continuousOn hmap
  apply hjet.congr
  intro s hs
  have hderiv := vertical_hasDerivAt_of_closed_jet hF
    hs.1 (hs.2.trans_lt huv) hvB
    (g := (fderivWithin ℝ F K (s, v)) (0, 1)) rfl
  exact hderiv.deriv

/-- Equation (10) for `L = λᵥ` on the strict interior of a finite old
development. No C² regularity of `λ` is required. -/
theorem lambda_v_hasDerivAt_u_of_c1
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openDevelopment 0 b) :
    HasDerivAt (fun s => deriv (S.lam s) v)
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
                1 / (1 - 2 * S.m u v / S.r u v)) / (S.r u v) ^ 2)) u := by
  have hp0 := hp
  obtain ⟨⟨hu, _⟩, ⟨huv, hv⟩⟩ := hp
  let B : ℝ := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  let F : ℝ × ℝ → ℝ := fun p => S.lam p.1 p.2
  let G : ℝ × ℝ → ℝ := C1Solution.canonicalMixedCoefficient b S
  have hF := (C1Solution.five_fields_contDiffOn hB hBb H).1
  have hG := C1Solution.canonicalMixedCoefficient_contDiffOn hB hBb H
  have hsource : ∀ p ∈ closedCoordTriangle 0 B,
      (fderivWithin ℝ F (closedCoordTriangle 0 B) p) (1, 0) = G p := by
    intro p hpK
    exact (C1Solution.four_mixed_coordinate_jets hB hBb H hpK).1
  have hmixed := hasDerivAt_vertical_deriv_of_horizontal_source_on_triangle
    hB hF hG hsource (show (u, v) ∈ openCoordTriangle 0 B from
      ⟨hu, huv, hvB⟩)
  have hEq : (fun t => G (u, t)) =ᶠ[𝓝 v]
      (fun t => S.nu u t * S.lam u t *
        ((2 * S.m u t / S.r u t) /
          ((1 - 2 * S.m u t / S.r u t) * S.r u t))) := by
    filter_upwards [Ioo_mem_nhds huv hvB] with t ht
    have hcoeff := C1Solution.canonicalMixedCoefficient_eq_frozen
      hB hBb H hu.le ht.1 ht.2.le
    dsimp [G]
    rw [hcoeff]
    ring
  have hsourceDeriv := lambda_incoming_source_hasDerivAt_v_of_c1 H hp0
  have hderivEq : deriv (fun t => G (u, t)) v =
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
                1 / (1 - 2 * S.m u v / S.r u v)) / (S.r u v) ^ 2)) := by
    rw [hEq.deriv_eq]
    exact hsourceDeriv.deriv
  rw [hderivEq] at hmixed
  simpa only [F, Function.comp_def, Prod.fst, Prod.snd] using hmixed

end ChristodoulouBV.Uniqueness

end
