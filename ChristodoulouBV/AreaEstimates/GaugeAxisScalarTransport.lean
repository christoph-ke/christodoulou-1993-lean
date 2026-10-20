module

public import ChristodoulouBV.C1Solution.ExtractionJets
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Pointwise scalar amplitude transports for C¹ solutions

The frozen integral equations and extracted first jets imply (1.16a,b)
at every strict point. These identities use only first derivatives of the
five C¹ fields.
-/

public section

open Set

namespace ChristodoulouBV

/-- Equation (1.16a), pointwise off the axis on a closed C¹ subtriangle,
including the initial edge by relative differentiation. -/
theorem theta_incoming_pointwise {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B)
    (huv : p.1 < p.2) :
    (fderivWithin ℝ (fun q : ℝ × ℝ => S.theta q.1 q.2)
      (closedCoordTriangle 0 B) p) (1, 0) +
      S.lam p.1 p.2 / S.r p.1 p.2 * S.zeta p.1 p.2 = 0 := by
  let K := closedCoordTriangle 0 B
  let alpha : ℝ × ℝ → ℝ := fun q => S.alpha q.1 q.2
  let lam : ℝ × ℝ → ℝ := fun q => S.lam q.1 q.2
  let phi : ℝ × ℝ → ℝ := fun q => S.phi q.1 q.2
  have hparts : 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ B :=
    ⟨hp.1, huv, hp.2.2⟩
  have hpK : p ∈ K := hp
  have hUnique : UniqueDiffWithinAt ℝ K p :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB) p hpK
  have hAlphaDiff : DifferentiableWithinAt ℝ alpha K p :=
    (C1Solution.alpha_contDiffOn hB hBb H).differentiableOn (by norm_num) p hpK
  have hLamDiff : DifferentiableWithinAt ℝ lam K p :=
    ((C1Solution.five_fields_contDiffOn hB hBb H).1.differentiableOn
      (by norm_num)) p hpK
  have hPhiDiff : DifferentiableWithinAt ℝ phi K p :=
    ((C1Solution.five_fields_contDiffOn hB hBb H).2.2.1.differentiableOn
      (by norm_num)) p hpK
  have hEq : EqOn (fun q : ℝ × ℝ => S.theta q.1 q.2)
      (alpha - lam * phi) K := by
    intro q hq
    rfl
  have hDerivative :
      (fderivWithin ℝ (fun q : ℝ × ℝ => S.theta q.1 q.2) K p) (1, 0) =
        (fderivWithin ℝ alpha K p) (1, 0) -
          ((fderivWithin ℝ lam K p) (1, 0) * phi p +
            lam p * (fderivWithin ℝ phi K p) (1, 0)) := by
    rw [fderivWithin_congr' hEq hpK]
    rw [fderivWithin_sub hUnique hAlphaDiff (hLamDiff.mul hPhiDiff)]
    rw [fderivWithin_mul hUnique hLamDiff hPhiDiff]
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
    ring
  obtain ⟨hLamJet, _, hAlphaJet, _⟩ :=
    C1Solution.four_mixed_coordinate_jets hB hBb H hpK
  have hZeta := C1Solution.zeta_eq_canonicalRadius_mul_phi_horizontal_jet
    hB hBb H hpK
  rw [C1Solution.canonicalRadius_eq_radius hB hBb H
    hparts.1 hparts.2.1 hparts.2.2] at hZeta
  have hr : S.r p.1 p.2 ≠ 0 := ne_of_gt
    (H.solution.radius_pos p ⟨hparts.1, hparts.2.1, hparts.2.2.trans_lt hBb⟩)
  change S.zeta p.1 p.2 = S.r p.1 p.2 *
    (fderivWithin ℝ phi K p) (1, 0) at hZeta
  dsimp [alpha, lam, phi] at hDerivative hLamJet hAlphaJet hZeta
  rw [hAlphaJet, hLamJet] at hDerivative
  rw [hDerivative, hZeta]
  field_simp [hr]
  ring

/-- Equation (1.16b), pointwise off the axis on a closed C¹ subtriangle,
including the initial edge by relative differentiation. -/
theorem zeta_outgoing_pointwise {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B)
    (huv : p.1 < p.2) :
    (fderivWithin ℝ (fun q : ℝ × ℝ => S.zeta q.1 q.2)
      (closedCoordTriangle 0 B) p) (0, 1) +
      S.nu p.1 p.2 / S.r p.1 p.2 * S.theta p.1 p.2 = 0 := by
  let K := closedCoordTriangle 0 B
  let beta : ℝ × ℝ → ℝ := fun q => S.beta q.1 q.2
  let nu : ℝ × ℝ → ℝ := fun q => S.nu q.1 q.2
  let phi : ℝ × ℝ → ℝ := fun q => S.phi q.1 q.2
  have hparts : 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ B :=
    ⟨hp.1, huv, hp.2.2⟩
  have hpK : p ∈ K := hp
  have hUnique : UniqueDiffWithinAt ℝ K p :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB) p hpK
  have hBetaDiff : DifferentiableWithinAt ℝ beta K p :=
    (C1Solution.beta_contDiffOn hB hBb H).differentiableOn (by norm_num) p hpK
  have hNuDiff : DifferentiableWithinAt ℝ nu K p :=
    ((C1Solution.five_fields_contDiffOn hB hBb H).2.1.differentiableOn
      (by norm_num)) p hpK
  have hPhiDiff : DifferentiableWithinAt ℝ phi K p :=
    ((C1Solution.five_fields_contDiffOn hB hBb H).2.2.1.differentiableOn
      (by norm_num)) p hpK
  have hEq : EqOn (fun q : ℝ × ℝ => S.zeta q.1 q.2)
      (beta - nu * phi) K := by
    intro q hq
    rfl
  have hDerivative :
      (fderivWithin ℝ (fun q : ℝ × ℝ => S.zeta q.1 q.2) K p) (0, 1) =
        (fderivWithin ℝ beta K p) (0, 1) -
          ((fderivWithin ℝ nu K p) (0, 1) * phi p +
            nu p * (fderivWithin ℝ phi K p) (0, 1)) := by
    rw [fderivWithin_congr' hEq hpK]
    rw [fderivWithin_sub hUnique hBetaDiff (hNuDiff.mul hPhiDiff)]
    rw [fderivWithin_mul hUnique hNuDiff hPhiDiff]
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
    ring
  obtain ⟨_, hNuJet, _, hBetaJet⟩ :=
    C1Solution.four_mixed_coordinate_jets hB hBb H hpK
  have hTheta := C1Solution.theta_eq_canonicalRadius_mul_phi_vertical_jet
    hB hBb H hpK
  rw [C1Solution.canonicalRadius_eq_radius hB hBb H
    hparts.1 hparts.2.1 hparts.2.2] at hTheta
  have hr : S.r p.1 p.2 ≠ 0 := ne_of_gt
    (H.solution.radius_pos p ⟨hparts.1, hparts.2.1, hparts.2.2.trans_lt hBb⟩)
  change S.theta p.1 p.2 = S.r p.1 p.2 *
    (fderivWithin ℝ phi K p) (0, 1) at hTheta
  dsimp [beta, nu, phi] at hDerivative hNuJet hBetaJet hTheta
  rw [hBetaJet, hNuJet] at hDerivative
  rw [hDerivative, hTheta]
  field_simp [hr]
  ring

end ChristodoulouBV

end
