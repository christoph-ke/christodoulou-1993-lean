module

public import ChristodoulouBV.Uniqueness.RouteBGluingClassicalJet
public import ChristodoulouBV.Uniqueness.RouteBGluingIdentificationSeam
public import ChristodoulouBV.C1Solution.ExtractionJets
public import ChristodoulouBV.C1Solution.ExtractionMass
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Classical equations on a finite old cutoff

The canonical radius and mass have closed relative jets. At a point of the
open development these agree with the frozen fields, so the classical
equations hold on every strict closed cutoff.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The ten primitive equations of a canonical old family member hold as
relative jets on every strict finite triangle. -/
theorem routeBCanonicalOldFields_primitive_jets
    {e d b : ℝ} (he : 0 < e) (hed : e < d)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge d) S) :
    (RouteBLocalJetEquation b (closedCoordTriangle 0 e)
      (routeBCanonicalOldFields d S) (routeBSelector .radius)
      (routeBSelector .expansion) (0, 1)) ∧
    (RouteBLocalJetEquation b (closedCoordTriangle 0 e)
      (routeBCanonicalOldFields d S) (routeBSelector .radius)
      (routeBSelector .contraction) (1, 0)) ∧
    (RouteBLocalJetEquation b (closedCoordTriangle 0 e)
      (routeBCanonicalOldFields d S) routeBScalarRadiusExpr
      (routeBSelector .outgoing) (0, 1)) ∧
    (RouteBLocalJetEquation b (closedCoordTriangle 0 e)
      (routeBCanonicalOldFields d S) routeBScalarRadiusExpr
      (routeBSelector .incoming) (1, 0)) ∧
    (RouteBLocalJetEquation b (closedCoordTriangle 0 e)
      (routeBCanonicalOldFields d S) (routeBSelector .mass)
      routeBMassOutgoingExpr (0, 1)) ∧
    (RouteBLocalJetEquation b (closedCoordTriangle 0 e)
      (routeBCanonicalOldFields d S) (routeBSelector .mass)
      routeBMassIncomingExpr (1, 0)) ∧
    (RouteBLocalJetEquation b (closedCoordTriangle 0 e)
      (routeBCanonicalOldFields d S) (routeBSelector .expansion)
      routeBMixedExpr (1, 0)) ∧
    (RouteBLocalJetEquation b (closedCoordTriangle 0 e)
      (routeBCanonicalOldFields d S) (routeBSelector .contraction)
      routeBMixedExpr (0, 1)) ∧
    (RouteBLocalJetEquation b (closedCoordTriangle 0 e)
      (routeBCanonicalOldFields d S) (routeBSelector .outgoing)
      routeBMixedScalarExpr (1, 0)) ∧
    (RouteBLocalJetEquation b (closedCoordTriangle 0 e)
      (routeBCanonicalOldFields d S) (routeBSelector .incoming)
      routeBMixedScalarExpr (0, 1)) := by
  let F := routeBCanonicalOldFields d S
  have hUnique : UniqueDiffOn ℝ (closedCoordTriangle 0 e) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 e) (by
      rw [interior_closedCoordTriangle]
      exact openCoordTriangle_nonempty he)
  have hPsiEq : EqOn (routeBScalarExpression routeBScalarRadiusExpr F)
      (C1Solution.canonicalScalarRadius S) (closedCoordTriangle 0 e) := by
    intro p hp
    change C1Solution.canonicalRadius S p * S.phi p.1 p.2 =
      C1Solution.canonicalScalarRadius S p
    exact (C1Solution.canonicalScalarRadius_eq_canonicalRadius_mul_phi
      he hed H hp).symm
  repeat' constructor
  · intro p hp hpD
    change (fderivWithin ℝ (C1Solution.canonicalRadius S)
      (closedCoordTriangle 0 e) p) (0, 1) = S.lam p.1 p.2
    exact C1Solution.canonicalRadius_vertical_jet he hed H hp
  · intro p hp hpD
    change (fderivWithin ℝ (C1Solution.canonicalRadius S)
      (closedCoordTriangle 0 e) p) (1, 0) = S.nu p.1 p.2
    exact C1Solution.canonicalRadius_horizontal_jet he hed H hp
  · intro p hp hpD
    rw [fderivWithin_congr' hPsiEq hp]
    change (fderivWithin ℝ (C1Solution.canonicalScalarRadius S)
      (closedCoordTriangle 0 e) p) (0, 1) = S.alpha p.1 p.2
    exact C1Solution.canonicalScalarRadius_vertical_jet he hed H hp
  · intro p hp hpD
    rw [fderivWithin_congr' hPsiEq hp]
    change (fderivWithin ℝ (C1Solution.canonicalScalarRadius S)
      (closedCoordTriangle 0 e) p) (1, 0) = S.beta p.1 p.2
    exact C1Solution.canonicalScalarRadius_horizontal_jet he hed H hp
  · intro p hp hpD
    change (fderivWithin ℝ (C1Solution.canonicalMass d S)
      (closedCoordTriangle 0 e) p) (0, 1) = _
    rw [(C1Solution.canonicalMass_coordinate_jets he hed H hp).2]
    rw [C1Solution.canonicalMassOutgoingDensity]
    rfl
  · intro p hp hpD
    change (fderivWithin ℝ (C1Solution.canonicalMass d S)
      (closedCoordTriangle 0 e) p) (1, 0) = _
    rw [(C1Solution.canonicalMass_coordinate_jets he hed H hp).1]
    rw [C1Solution.canonicalMassIncomingDensity]
    rfl
  · intro p hp hpD
    change (fderivWithin ℝ (fun q : ℝ × ℝ => S.lam q.1 q.2)
      (closedCoordTriangle 0 e) p) (1, 0) = _
    rw [(C1Solution.four_mixed_coordinate_jets he hed H hp).1]
    rw [C1Solution.canonicalMixedCoefficient_eq_frozen he hed H
      hp.1 hpD.2.1 hp.2.2]
    rw [← C1Solution.canonicalMass_eq_mass
      (show p ∈ developmentWithInitialEdge d from
        ⟨hp.1, hpD.2.1, hp.2.2.trans_lt hed⟩),
      ← C1Solution.canonicalRadius_eq_radius he hed H
        hp.1 hpD.2.1 hp.2.2]
    rfl
  · intro p hp hpD
    change (fderivWithin ℝ (fun q : ℝ × ℝ => S.nu q.1 q.2)
      (closedCoordTriangle 0 e) p) (0, 1) = _
    rw [(C1Solution.four_mixed_coordinate_jets he hed H hp).2.1]
    rw [C1Solution.canonicalMixedCoefficient_eq_frozen he hed H
      hp.1 hpD.2.1 hp.2.2]
    rw [← C1Solution.canonicalMass_eq_mass
      (show p ∈ developmentWithInitialEdge d from
        ⟨hp.1, hpD.2.1, hp.2.2.trans_lt hed⟩),
      ← C1Solution.canonicalRadius_eq_radius he hed H
        hp.1 hpD.2.1 hp.2.2]
    rfl
  · intro p hp hpD
    change (fderivWithin ℝ (fun q : ℝ × ℝ => S.alpha q.1 q.2)
      (closedCoordTriangle 0 e) p) (1, 0) = _
    rw [(C1Solution.four_mixed_coordinate_jets he hed H hp).2.2.1]
    rw [C1Solution.canonicalMixedCoefficient_eq_frozen he hed H
      hp.1 hpD.2.1 hp.2.2]
    rw [← C1Solution.canonicalMass_eq_mass
      (show p ∈ developmentWithInitialEdge d from
        ⟨hp.1, hpD.2.1, hp.2.2.trans_lt hed⟩),
      ← C1Solution.canonicalRadius_eq_radius he hed H
        hp.1 hpD.2.1 hp.2.2]
    rfl
  · intro p hp hpD
    change (fderivWithin ℝ (fun q : ℝ × ℝ => S.beta q.1 q.2)
      (closedCoordTriangle 0 e) p) (0, 1) = _
    rw [(C1Solution.four_mixed_coordinate_jets he hed H hp).2.2.2]
    rw [C1Solution.canonicalMixedCoefficient_eq_frozen he hed H
      hp.1 hpD.2.1 hp.2.2]
    rw [← C1Solution.canonicalMass_eq_mass
      (show p ∈ developmentWithInitialEdge d from
        ⟨hp.1, hpD.2.1, hp.2.2.trans_lt hed⟩),
      ← C1Solution.canonicalRadius_eq_radius he hed H
        hp.1 hpD.2.1 hp.2.2]
    rfl

/-- The two scalar-amplitude transport equations on a strict finite
canonical old cutoff, including its initial edge and top edge. -/
theorem routeBCanonicalOldFields_amplitude_jets
    {e d b : ℝ} (he : 0 < e) (hed : e < d)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge d) S) :
    RouteBLocalJetEquation b (closedCoordTriangle 0 e)
      (routeBCanonicalOldFields d S) routeBThetaExpr
      routeBThetaIncomingExpr (1, 0) ∧
    RouteBLocalJetEquation b (closedCoordTriangle 0 e)
      (routeBCanonicalOldFields d S) routeBZetaExpr
      routeBZetaOutgoingExpr (0, 1) := by
  let K := closedCoordTriangle 0 e
  let R : ℝ × ℝ → ℝ := C1Solution.canonicalRadius S
  let P : ℝ × ℝ → ℝ := fun q => S.phi q.1 q.2
  let L : ℝ × ℝ → ℝ := fun q => S.lam q.1 q.2
  let N : ℝ × ℝ → ℝ := fun q => S.nu q.1 q.2
  let A : ℝ × ℝ → ℝ := fun q => S.alpha q.1 q.2
  let B : ℝ × ℝ → ℝ := fun q => S.beta q.1 q.2
  have hUnique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 e) (by
      rw [interior_closedCoordTriangle]
      exact openCoordTriangle_nonempty he)
  have hLam := (C1Solution.five_fields_contDiffOn he hed H).1
  have hNu := (C1Solution.five_fields_contDiffOn he hed H).2.1
  have hPhi := (C1Solution.five_fields_contDiffOn he hed H).2.2.1
  have hAlpha := C1Solution.alpha_contDiffOn he hed H
  have hBeta := C1Solution.beta_contDiffOn he hed H
  constructor
  · intro p hp hpD
    have hLdiff : DifferentiableWithinAt ℝ L K p :=
      hLam.differentiableOn (by norm_num) p hp
    have hPdiff : DifferentiableWithinAt ℝ P K p :=
      hPhi.differentiableOn (by norm_num) p hp
    have hAdiff : DifferentiableWithinAt ℝ A K p :=
      hAlpha.differentiableOn (by norm_num) p hp
    have hFour := C1Solution.four_mixed_coordinate_jets he hed H hp
    have hZeta := C1Solution.zeta_eq_canonicalRadius_mul_phi_horizontal_jet
      he hed H hp
    have hDev : p ∈ developmentWithInitialEdge d :=
      ⟨hp.1, hpD.2.1, hp.2.2.trans_lt hed⟩
    have hR0 : R p ≠ 0 := by
      change C1Solution.canonicalRadius S p ≠ 0
      rw [C1Solution.canonicalRadius_eq_radius he hed H
        hp.1 hpD.2.1 hp.2.2]
      exact ne_of_gt (H.solution.radius_pos p hDev)
    have hDeriv :
        (fderivWithin ℝ (A - L * P) K p) (1, 0) =
          (fderivWithin ℝ A K p) (1, 0) -
            ((fderivWithin ℝ L K p) (1, 0) * P p +
              L p * (fderivWithin ℝ P K p) (1, 0)) := by
      rw [fderivWithin_sub (hUnique p hp) hAdiff (hLdiff.mul hPdiff),
        fderivWithin_mul (hUnique p hp) hLdiff hPdiff]
      simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
      ring
    change (fderivWithin ℝ (A - L * P) K p) (1, 0) =
      -(L p / R p * S.zeta p.1 p.2)
    rw [hDeriv, hFour.2.2.1, hFour.1]
    calc
      C1Solution.canonicalMixedCoefficient d S p * P p -
          (C1Solution.canonicalMixedCoefficient d S p * P p +
            L p * (fderivWithin ℝ P K p) (1, 0)) =
        -(L p * (fderivWithin ℝ P K p) (1, 0)) := by ring
      _ = -(L p / R p * S.zeta p.1 p.2) := by
        rw [hZeta]
        field_simp
        ring
  · intro p hp hpD
    have hNdiff : DifferentiableWithinAt ℝ N K p :=
      hNu.differentiableOn (by norm_num) p hp
    have hPdiff : DifferentiableWithinAt ℝ P K p :=
      hPhi.differentiableOn (by norm_num) p hp
    have hBdiff : DifferentiableWithinAt ℝ B K p :=
      hBeta.differentiableOn (by norm_num) p hp
    have hFour := C1Solution.four_mixed_coordinate_jets he hed H hp
    have hTheta := C1Solution.theta_eq_canonicalRadius_mul_phi_vertical_jet
      he hed H hp
    have hDev : p ∈ developmentWithInitialEdge d :=
      ⟨hp.1, hpD.2.1, hp.2.2.trans_lt hed⟩
    have hR0 : R p ≠ 0 := by
      change C1Solution.canonicalRadius S p ≠ 0
      rw [C1Solution.canonicalRadius_eq_radius he hed H
        hp.1 hpD.2.1 hp.2.2]
      exact ne_of_gt (H.solution.radius_pos p hDev)
    have hDeriv :
        (fderivWithin ℝ (B - N * P) K p) (0, 1) =
          (fderivWithin ℝ B K p) (0, 1) -
            ((fderivWithin ℝ N K p) (0, 1) * P p +
              N p * (fderivWithin ℝ P K p) (0, 1)) := by
      rw [fderivWithin_sub (hUnique p hp) hBdiff (hNdiff.mul hPdiff),
        fderivWithin_mul (hUnique p hp) hNdiff hPdiff]
      simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
      ring
    change (fderivWithin ℝ (B - N * P) K p) (0, 1) =
      -(N p / R p * S.theta p.1 p.2)
    rw [hDeriv, hFour.2.2.2, hFour.2.1]
    calc
      C1Solution.canonicalMixedCoefficient d S p * P p -
          (C1Solution.canonicalMixedCoefficient d S p * P p +
            N p * (fderivWithin ℝ P K p) (0, 1)) =
        -(N p * (fderivWithin ℝ P K p) (0, 1)) := by ring
      _ = -(N p / R p * S.theta p.1 p.2) := by
        rw [hTheta]
        field_simp
        ring

/-- All twelve classical relative-jet equations hold on a strict finite
cutoff of a canonical old family member. -/
theorem routeBCanonicalOldFields_classicalJetOn
    {e d b : ℝ} (he : 0 < e) (hed : e < d)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge d) S) :
    RouteBClassicalJetOn b (closedCoordTriangle 0 e)
      (routeBCanonicalOldFields d S) := by
  obtain ⟨hrv, hru, hpsiv, hpsiu, hmv, hmu, hlamu, hnuv, halphau, hbetav⟩ :=
    routeBCanonicalOldFields_primitive_jets (b := b) he hed H
  obtain ⟨hthetau, hzetav⟩ :=
    routeBCanonicalOldFields_amplitude_jets (b := b) he hed H
  exact {
    radius_out := hrv
    radius_in := hru
    scalar_radius_out := hpsiv
    scalar_radius_in := hpsiu
    mass_out := hmv
    mass_in := hmu
    expansion_in := hlamu
    contraction_out := hnuv
    theta_in := hthetau
    zeta_out := hzetav
    outgoing_in := halphau
    incoming_out := hbetav
  }

end ChristodoulouBV.Uniqueness

end
