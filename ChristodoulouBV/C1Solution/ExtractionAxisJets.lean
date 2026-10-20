module

public import ChristodoulouBV.C1Solution.ExtractionAxisJetCore
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Remaining regular-axis first jets

The scalar amplitudes, the incoming coordinate jets, and the removable
coefficient are computed from canonical continuous fields.
-/

public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.C1Solution

/-- The incoming radial and scalar-radius coordinate derivatives on the axis
are opposite to the remaining outgoing derivatives. -/
theorem incoming_axis_coordinate_jets {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (hu : u ∈ Icc 0 B) :
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.nu p.1 p.2)
      (closedCoordTriangle 0 B) (u, u)) (1, 0) =
      -(fderivWithin ℝ (fun p : ℝ × ℝ => S.lam p.1 p.2)
        (closedCoordTriangle 0 B) (u, u)) (0, 1) ∧
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.beta p.1 p.2)
      (closedCoordTriangle 0 B) (u, u)) (1, 0) =
      -(fderivWithin ℝ (fun p : ℝ × ℝ => S.alpha p.1 p.2)
        (closedCoordTriangle 0 B) (u, u)) (0, 1) := by
  let K := closedCoordTriangle 0 B
  let lam : ℝ × ℝ → ℝ := fun p => S.lam p.1 p.2
  let nu : ℝ × ℝ → ℝ := fun p => S.nu p.1 p.2
  let alpha : ℝ × ℝ → ℝ := fun p => S.alpha p.1 p.2
  let beta : ℝ × ℝ → ℝ := fun p => S.beta p.1 p.2
  have hp : (u, u) ∈ K := ⟨hu.1, le_rfl, hu.2⟩
  obtain ⟨hlamu, hnuv, halphau, hbetav⟩ := four_mixed_axis_jets hB hBb H hu
  have hunique : UniqueDiffWithinAt ℝ K (u, u) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
      (u, u) hp
  obtain ⟨hlam, hnu, _, _, _⟩ := five_fields_contDiffOn hB hBb H
  have hsumR := diagonal_coordinate_jets_sum_zero hB (hnu.add hlam)
    (fun t ht => by change S.nu t t + S.lam t t = 0
                    rw [nu_eq_neg_lam_axis hB hBb H ht]; ring) hu
  have hsumP := diagonal_coordinate_jets_sum_zero hB
    ((beta_contDiffOn hB hBb H).add (alpha_contDiffOn hB hBb H))
    (fun t ht => by change S.beta t t + S.alpha t t = 0
                    rw [beta_eq_neg_alpha_axis hB hBb H ht]; ring) hu
  have hdiffLam := hlam.differentiableOn (by norm_num) (u, u) hp
  have hdiffNu := hnu.differentiableOn (by norm_num) (u, u) hp
  have hdiffAlpha := (alpha_contDiffOn hB hBb H).differentiableOn
    (by norm_num) (u, u) hp
  have hdiffBeta := (beta_contDiffOn hB hBb H).differentiableOn
    (by norm_num) (u, u) hp
  change (fderivWithin ℝ (nu + lam) K (u, u)) (1, 0) +
    (fderivWithin ℝ (nu + lam) K (u, u)) (0, 1) = 0 at hsumR
  change (fderivWithin ℝ (beta + alpha) K (u, u)) (1, 0) +
    (fderivWithin ℝ (beta + alpha) K (u, u)) (0, 1) = 0 at hsumP
  rw [fderivWithin_add hunique hdiffNu hdiffLam] at hsumR
  rw [fderivWithin_add hunique hdiffBeta hdiffAlpha] at hsumP
  simp only [add_apply] at hsumR hsumP
  rw [hlamu, hnuv] at hsumR
  rw [halphau, hbetav] at hsumP
  constructor <;> linarith

/-- The two scalar amplitudes have the same outgoing axis jet, equal to the
axis radius jet times the scalar's outgoing jet; their incoming jets are its
negative. -/
theorem amplitude_axis_coordinate_jets {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (hu : u ∈ Icc 0 B) :
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.theta p.1 p.2)
      (closedCoordTriangle 0 B) (u, u)) (1, 0) =
      -S.lam u u *
        (fderivWithin ℝ (fun p : ℝ × ℝ => S.phi p.1 p.2)
          (closedCoordTriangle 0 B) (u, u)) (0, 1) ∧
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.theta p.1 p.2)
      (closedCoordTriangle 0 B) (u, u)) (0, 1) =
      S.lam u u *
        (fderivWithin ℝ (fun p : ℝ × ℝ => S.phi p.1 p.2)
          (closedCoordTriangle 0 B) (u, u)) (0, 1) ∧
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.zeta p.1 p.2)
      (closedCoordTriangle 0 B) (u, u)) (1, 0) =
      -S.lam u u *
        (fderivWithin ℝ (fun p : ℝ × ℝ => S.phi p.1 p.2)
          (closedCoordTriangle 0 B) (u, u)) (0, 1) ∧
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.zeta p.1 p.2)
      (closedCoordTriangle 0 B) (u, u)) (0, 1) =
      S.lam u u *
        (fderivWithin ℝ (fun p : ℝ × ℝ => S.phi p.1 p.2)
          (closedCoordTriangle 0 B) (u, u)) (0, 1) := by
  let K := closedCoordTriangle 0 B
  let ρ := canonicalNormalizedRadius S
  let φu : ℝ × ℝ → ℝ := fun p =>
    (fderivWithin ℝ (fun q : ℝ × ℝ => S.phi q.1 q.2) K p) (1, 0)
  let φv : ℝ × ℝ → ℝ := fun p =>
    (fderivWithin ℝ (fun q : ℝ × ℝ => S.phi q.1 q.2) K p) (0, 1)
  have hφ := (five_fields_contDiffOn hB hBb H).2.2.1
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hB)
  have hjet := hφ.continuousOn_fderivWithin hunique (by norm_num)
  have hφu : ContinuousOn φu K := hjet.clm_apply continuousOn_const
  have hφv : ContinuousOn φv K := hjet.clm_apply continuousOn_const
  have hρ := (canonicalNormalizedRadius_continuousOn_and_lower_bound hB hBb H).1
  have hθfactor : ∀ p ∈ K,
      S.theta p.1 p.2 = (p.2 - p.1) * (ρ p * φv p) := by
    intro p hp
    rw [theta_eq_canonicalRadius_mul_phi_vertical_jet hB hBb H hp,
      canonicalRadius_eq_gap_mul_normalized]
    ring
  have hζfactor : ∀ p ∈ K,
      S.zeta p.1 p.2 = (p.2 - p.1) * (ρ p * φu p) := by
    intro p hp
    rw [zeta_eq_canonicalRadius_mul_phi_horizontal_jet hB hBb H hp,
      canonicalRadius_eq_gap_mul_normalized]
    ring
  obtain ⟨hθu, hθv⟩ := axis_coordinate_jets_of_gap_factor hB
    (five_fields_contDiffOn hB hBb H).2.2.2.1 (hρ.mul hφv) hθfactor hu
  obtain ⟨hζu, hζv⟩ := axis_coordinate_jets_of_gap_factor hB
    (five_fields_contDiffOn hB hBb H).2.2.2.2 (hρ.mul hφu) hζfactor hu
  have hρdiag : ρ (u, u) = S.lam u u :=
    intervalIntegral.normalizedDiagonalRadius_diag _ _
  have hφeq : φu (u, u) = φv (u, u) :=
    (outgoingQuotient_and_phi_axis_jets hB hBb H hu).2
  change canonicalNormalizedRadius S (u, u) = S.lam u u at hρdiag
  simp only [Pi.mul_apply] at hθu hθv hζu hζv
  rw [hρdiag] at hθu hθv hζu hζv
  dsimp [φu, φv] at hθu hθv hζu hζv hφeq
  rw [hφeq] at hζu hζv
  exact ⟨by simpa only [neg_mul] using hθu, hθv,
    by simpa only [neg_mul] using hζu, hζv⟩

/-- The scalar amplitude jets on the axis in the outgoing quotient coordinates. -/
theorem amplitude_axis_coordinate_jets_outgoingQuotient {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (hu : u ∈ Icc 0 B) :
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.theta p.1 p.2)
      (closedCoordTriangle 0 B) (u, u)) (1, 0) =
      -S.lam u u *
        (fderivWithin ℝ (outgoingQuotient S)
          (closedCoordTriangle 0 B) (u, u)) (0, 1) / 2 ∧
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.theta p.1 p.2)
      (closedCoordTriangle 0 B) (u, u)) (0, 1) =
      S.lam u u *
        (fderivWithin ℝ (outgoingQuotient S)
          (closedCoordTriangle 0 B) (u, u)) (0, 1) / 2 ∧
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.zeta p.1 p.2)
      (closedCoordTriangle 0 B) (u, u)) (1, 0) =
      -S.lam u u *
        (fderivWithin ℝ (outgoingQuotient S)
          (closedCoordTriangle 0 B) (u, u)) (0, 1) / 2 ∧
    (fderivWithin ℝ (fun p : ℝ × ℝ => S.zeta p.1 p.2)
      (closedCoordTriangle 0 B) (u, u)) (0, 1) =
      S.lam u u *
        (fderivWithin ℝ (outgoingQuotient S)
          (closedCoordTriangle 0 B) (u, u)) (0, 1) / 2 := by
  obtain ⟨hθu, hθv, hζu, hζv⟩ := amplitude_axis_coordinate_jets hB hBb H hu
  have hφ := (phi_axis_jets hB hBb H hu).1
  rw [hφ] at hθu hθv hζu hζv
  exact ⟨by convert hθu using 1; ring,
    by convert hθv using 1; ring,
    by convert hζu using 1; ring,
    by convert hζv using 1; ring⟩

/-- The normalized cubic mass coefficient on the axis is one third of the
normalized outgoing mass density. -/
theorem normalizedMassCubic_axis {b B : ℝ}
    (_hB : 0 < B) (_hBb : B < b)
    {S : Fields} (_H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (_hu : u ∈ Icc 0 B) :
    normalizedMassCubic b B S (u, u) =
      normalizedMassDensity b B S (u, u) / 3 := by
  rw [normalizedMassCubic]
  simp only [intervalIntegral.diagonalSegment, sub_self]
  simp only [mul_zero, add_zero]
  rw [intervalIntegral.integral_mul_const]
  rw [integral_pow]
  norm_num
  ring

/-- The linearly vanishing mass-over-radius coefficient has the scalar
outgoing jet squared as its exact axis value. -/
theorem normalizedMassOverRadiusSq_axis {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (hu : u ∈ Icc 0 B) :
    normalizedMassOverRadiusSq b B S (u, u) =
      ((fderivWithin ℝ (fun p : ℝ × ℝ => S.phi p.1 p.2)
        (closedCoordTriangle 0 B) (u, u)) (0, 1))^2 /
        (3 * S.lam u u) := by
  have hp : (u, u) ∈ closedCoordTriangle 0 B := ⟨hu.1, le_rfl, hu.2⟩
  have hlam : 0 < S.lam u u := by
    obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hBb H
    exact hc.trans_le (hcl (u, u) hp)
  have hne : S.lam u u ≠ 0 := ne_of_gt hlam
  have hθ : normalizedTheta B S (u, u) =
      S.lam u u *
        (fderivWithin ℝ (fun p : ℝ × ℝ => S.phi p.1 p.2)
          (closedCoordTriangle 0 B) (u, u)) (0, 1) := by
    have hjet := (amplitude_axis_coordinate_jets hB hBb H hu).2.1
    simpa only [normalizedTheta, intervalIntegral.verticalJetMean_diag] using hjet
  rw [normalizedMassOverRadiusSq, normalizedMassCubic_axis hB hBb H hu,
    normalizedMassDensity, canonicalMassRatio_axis,
    hθ]
  have hρ : canonicalNormalizedRadius S (u, u) = S.lam u u :=
    intervalIntegral.normalizedDiagonalRadius_diag _ _
  rw [hρ]
  field_simp [hne]
  ring

/-- Both coordinate jets of the canonical mass ratio vanish on the axis. -/
theorem canonicalMassRatio_axis_jets {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (hu : u ∈ Icc 0 B) :
    (fderivWithin ℝ (canonicalMassRatio b S)
      (closedCoordTriangle 0 B) (u, u)) (1, 0) = 0 ∧
    (fderivWithin ℝ (canonicalMassRatio b S)
      (closedCoordTriangle 0 B) (u, u)) (0, 1) = 0 := by
  let K := closedCoordTriangle 0 B
  let P : ℝ × ℝ → ℝ := fun p =>
    canonicalMassOverRadiusSq b S p * canonicalNormalizedRadius S p
  have hP : ContinuousOn P K :=
    (canonicalMassOverRadiusSq_continuousOn hB hBb H).mul
      (canonicalNormalizedRadius_continuousOn_and_lower_bound hB hBb H).1
  have hfactor : ∀ p ∈ K,
      canonicalMassRatio b S p = (p.2 - p.1) * P p := by
    intro p hp
    rcases p with ⟨a, v⟩
    rcases lt_or_eq_of_le hp.2.1 with hav | hav
    · have hrad : canonicalRadius S (a, v) ≠ 0 := by
        obtain ⟨c, hc, hcl⟩ := canonicalRadius_lower_bound hB hBb H
        exact ne_of_gt (lt_of_lt_of_le (mul_pos hc (sub_pos.mpr hav))
          (hcl (a, v) hp))
      have hρ : canonicalNormalizedRadius S (a, v) ≠ 0 := by
        obtain ⟨_, c, hc, hcl⟩ :=
          canonicalNormalizedRadius_continuousOn_and_lower_bound hB hBb H
        exact ne_of_gt (hc.trans_le (hcl (a, v) hp))
      dsimp [P, canonicalMassRatio, canonicalMassOverRadiusSq]
      rw [canonicalRadius_eq_gap_mul_normalized]
      field_simp [hrad, hρ, sub_ne_zero.mpr hav.ne']
    · change a = v at hav
      subst v
      simp [canonicalMassRatio_axis]
  obtain ⟨huJet, hvJet⟩ := axis_coordinate_jets_of_gap_factor hB
    (canonicalMassRatio_contDiffOn hB hBb H) hP hfactor hu
  have hPzero : P (u, u) = 0 := by
    simp [P, canonicalMassOverRadiusSq_axis]
  rw [hPzero] at huJet hvJet
  simpa using And.intro huJet hvJet

/-- The removable mixed coefficient has its expected opposite axis jets:
the vertical jet is `-λ h_v²/12` and the horizontal jet is its negative. -/
theorem canonicalMixedCoefficient_axis_coordinate_jets {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (hu : u ∈ Icc 0 B) :
    (fderivWithin ℝ (canonicalMixedCoefficient b S)
      (closedCoordTriangle 0 B) (u, u)) (1, 0) =
        S.lam u u *
          ((fderivWithin ℝ (outgoingQuotient S)
            (closedCoordTriangle 0 B) (u, u)) (0, 1))^2 / 12 ∧
    (fderivWithin ℝ (canonicalMixedCoefficient b S)
      (closedCoordTriangle 0 B) (u, u)) (0, 1) =
        -S.lam u u *
          ((fderivWithin ℝ (outgoingQuotient S)
            (closedCoordTriangle 0 B) (u, u)) (0, 1))^2 / 12 := by
  let K := closedCoordTriangle 0 B
  let P : ℝ × ℝ → ℝ := fun p =>
    normalizedMassOverRadiusSq b B S p * S.lam p.1 p.2 * S.nu p.1 p.2 /
      (1 - canonicalMassRatio b S p)
  have hP : ContinuousOn P K := by
    obtain ⟨ε, hε, hgap⟩ := exists_canonical_mass_gap_lower_bound hB hBb H
    obtain ⟨hlam, hnu, _, _, _⟩ := five_fields_contDiffOn hB hBb H
    exact (((normalizedMassOverRadiusSq_continuousOn hB hBb H).mul
      hlam.continuousOn).mul hnu.continuousOn).div
      (continuousOn_const.sub (canonicalMassRatio_continuousOn hB hBb H))
      (fun p hp => ne_of_gt (hε.trans_le (hgap p hp)))
  have hfactor : ∀ p ∈ K,
      canonicalMixedCoefficient b S p = (p.2 - p.1) * P p := by
    intro p hp
    rw [canonicalMixedCoefficient,
      canonicalMassOverRadiusSq_eq_gap_mul_normalized hB hBb H hp]
    dsimp [P]
    ring
  obtain ⟨hKu, hKv⟩ := axis_coordinate_jets_of_gap_factor hB
    (canonicalMixedCoefficient_contDiffOn hB hBb H) hP hfactor hu
  have hp : (u, u) ∈ K := ⟨hu.1, le_rfl, hu.2⟩
  have hlam : 0 < S.lam u u := by
    obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hBb H
    exact hc.trans_le (hcl (u, u) hp)
  have hne : S.lam u u ≠ 0 := ne_of_gt hlam
  have hφ := (phi_axis_jets hB hBb H hu).1
  have hPaxis : P (u, u) =
      -S.lam u u *
        ((fderivWithin ℝ (outgoingQuotient S) K (u, u)) (0, 1))^2 / 12 := by
    dsimp [P]
    rw [canonicalMassRatio_axis, nu_eq_neg_lam_axis hB hBb H hu,
      normalizedMassOverRadiusSq_axis hB hBb H hu]
    rw [hφ]
    field_simp [hne]
    ring
  rw [hPaxis] at hKu hKv
  constructor
  · convert hKu using 1; ring
  · exact hKv

end ChristodoulouBV.C1Solution

end
