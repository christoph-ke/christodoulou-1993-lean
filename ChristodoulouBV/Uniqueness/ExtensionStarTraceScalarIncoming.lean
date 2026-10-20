module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceZetaLinear
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceRadiusFloor
import ChristodoulouBV.Uniqueness.ExtensionIncomingScalarTransport
import ChristodoulouBV.C1Solution.Extraction
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Uniform incoming scalar quotient bound

The regular-axis linear vanishing of `ζ` and the uniform radius floor
give the missing scalar first-derivative estimate.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

private theorem horizontal_hasDerivAt_of_jet_for_phi {B : ℝ}
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

/-- The incoming scalar derivative is the regular quotient `ζ/r` at every
strict interior point of a finite old solution. -/
theorem phi_hasDerivAt_u_of_c1
    {b : ℝ} {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hp : (u, v) ∈ openDevelopment 0 b) :
    HasDerivAt (fun t => S.phi t v) (S.zeta u v / S.r u v) u := by
  obtain ⟨⟨hu, _⟩, ⟨huv, hv⟩⟩ := hp
  let B := (v + b) / 2
  have hB : 0 < B := by dsimp [B]; linarith
  have hBb : B < b := by dsimp [B]; linarith
  have hvB : v < B := by dsimp [B]; linarith
  have hpK : (u, v) ∈ openCoordTriangle 0 B := ⟨hu, huv, hvB⟩
  have hpKC : (u, v) ∈ closedCoordTriangle 0 B :=
    ⟨hu.le, huv.le, hvB.le⟩
  have hr0 : S.r u v ≠ 0 :=
    ne_of_gt (H.solution.radius_pos (u, v) ⟨hu.le, huv, hv⟩)
  have hphiJet := C1Solution.zeta_eq_canonicalRadius_mul_phi_horizontal_jet
    hB hBb H hpKC
  rw [C1Solution.canonicalRadius_eq_radius hB hBb H
    hu.le huv hvB.le] at hphiJet
  have hphi0 := horizontal_hasDerivAt_of_jet_for_phi hB
    (C1Solution.five_fields_contDiffOn hB hBb H).2.2.1 hpK (g :=
      (fderivWithin ℝ (fun q : ℝ × ℝ => S.phi q.1 q.2)
        (closedCoordTriangle 0 B) (u, v)) (1, 0)) rfl
  convert hphi0 using 1
  field_simp [hr0]
  linarith only [hphiJet]

/-- The incoming scalar quotient is bounded uniformly over every strict old
solution, independently of the family cutoff. -/
theorem exists_uniform_zeta_over_radius_bound_before_star
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε1 : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 < u → u < v → v < b →
          |(S b).zeta u v / (S b).r u v| ≤ C := by
  obtain ⟨M, hM, hζ⟩ :=
    exists_uniform_zeta_linear_bound_before_star hu₀ hα hfamily hε1 htail
  obtain ⟨c, hc, hrFloor⟩ :=
    exists_uniform_radius_floor_before_star hu₀ hα hfamily hε1 htail
  refine ⟨M / c, div_nonneg hM hc.le, ?_⟩
  intro b hb u v hu huv hvb
  have hr : 0 < (S b).r u v :=
    (hfamily b hb).1.solution.radius_pos (u, v) ⟨hu.le, huv, hvb⟩
  have hζ' := hζ b hb u v hu huv hvb
  have hr' := hrFloor b hb u v hu.le huv hvb
  rw [abs_div, abs_of_pos hr]
  apply (div_le_iff₀ hr).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).2
  nlinarith [mul_nonneg (sub_pos.mpr huv).le hM]

/-- The incoming first derivative of `φ` is uniformly bounded on the
strict old union, independently of the family cutoff. -/
theorem exists_uniform_scalar_incoming_derivative_bound_before_star
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε1 : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u v : ℝ, 0 < u → u < v → v < b →
          |deriv (fun t => (S b).phi t v) u| ≤ C := by
  obtain ⟨C, hC, hquot⟩ :=
    exists_uniform_zeta_over_radius_bound_before_star
      hu₀ hα hfamily hε1 htail
  refine ⟨C, hC, ?_⟩
  intro b hb u v hu huv hvb
  have hp : (u, v) ∈ openDevelopment 0 b :=
    ⟨⟨hu, huv.trans hvb⟩, ⟨huv, hvb⟩⟩
  rw [(phi_hasDerivAt_u_of_c1 (hfamily b hb).1 hp).deriv]
  exact hquot b hb u v hu huv hvb

end ChristodoulouBV.Uniqueness

end
