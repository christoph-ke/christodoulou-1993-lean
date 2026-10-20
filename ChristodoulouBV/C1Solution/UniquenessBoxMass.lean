module

public import ChristodoulouBV.C1Solution.UniquenessBoxes
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBox
import ChristodoulouBV.ForMathlib.Analysis.Calculus.AttenuatedVolterraAxis
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Cubic canonical mass inputs for the uniqueness boxes

The numerator used by the removable coefficients is twice the canonical
mass. Its cubic normalization and the quadratic normalizations of its two
coordinate jets are continuous on every compact smaller triangle.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

/-- The numerator of the canonical mass ratio. -/
@[expose] noncomputable def canonicalMassNumerator (b : ℝ) (S : Fields)
    (p : ℝ × ℝ) : ℝ := 2 * canonicalMass b S p

/-- The outgoing first jet of the quotient is the axis slope in the cubic
mass expansion. -/
@[expose] noncomputable def canonicalAxisSlope (B : ℝ) (S : Fields)
    (p : ℝ × ℝ) : ℝ :=
  (fderivWithin ℝ (outgoingQuotient S)
    (closedCoordTriangle 0 B) p) (0, 1)

/-- The axis slope is continuous on the smaller closed triangle. -/
theorem canonical_axis_slope_continuousOn {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContinuousOn (canonicalAxisSlope B S) (closedCoordTriangle 0 B) := by
  let K := closedCoordTriangle 0 B
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hB)
  exact ((alpha_div_lam_contDiffOn hB hBb H).continuousOn_fderivWithin
    hunique (by norm_num)).clm_apply continuousOn_const

/-- The canonical mass numerator has a continuous cubic coefficient. -/
theorem canonical_mass_numerator_cubic_factor {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContDiffOn ℝ 1 (canonicalMassNumerator b S)
      (closedCoordTriangle 0 B) ∧
    ContinuousOn (fun p => 2 * normalizedMassCubic b B S p)
      (closedCoordTriangle 0 B) ∧
    (∀ p ∈ closedCoordTriangle 0 B,
      canonicalMassNumerator b S p =
        (p.2 - p.1)^3 * (2 * normalizedMassCubic b B S p)) := by
  constructor
  · exact (contDiffOn_const.mul (canonicalMass_contDiffOn hB hBb H))
  constructor
  · exact continuousOn_const.mul (normalizedMassCubic_continuousOn hB hBb H)
  · intro p hp
    rw [canonicalMassNumerator,
      canonicalMass_eq_gap_cubed_mul_normalizedMassCubic hB hBb H hp]
    ring

/-- Both coordinate jets of the mass numerator have continuous quadratic
coefficients. -/
theorem canonical_mass_numerator_coordinate_jet_factors {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    ContinuousOn (fun p => 2 * normalizedIncomingMassDensity b B S p)
      (closedCoordTriangle 0 B) ∧
    ContinuousOn (fun p => 2 * normalizedMassDensity b B S p)
      (closedCoordTriangle 0 B) ∧
    (∀ p ∈ closedCoordTriangle 0 B,
      (fderivWithin ℝ (canonicalMassNumerator b S)
        (closedCoordTriangle 0 B) p) (1, 0) =
          (p.2 - p.1)^2 * (2 * normalizedIncomingMassDensity b B S p) ∧
      (fderivWithin ℝ (canonicalMassNumerator b S)
        (closedCoordTriangle 0 B) p) (0, 1) =
          (p.2 - p.1)^2 * (2 * normalizedMassDensity b B S p)) := by
  constructor
  · exact continuousOn_const.mul
      (normalizedIncomingMassDensity_continuousOn hB hBb H)
  constructor
  · exact continuousOn_const.mul (normalizedMassDensity_continuousOn hB hBb H)
  · intro p hp
    have hmass := canonicalMass_coordinate_jets hB hBb H hp
    have hunique : UniqueDiffWithinAt ℝ (closedCoordTriangle 0 B) p :=
      (uniqueDiffOn_convex (convex_closedCoordTriangle 0 B)
        (by rw [interior_closedCoordTriangle]
            exact openCoordTriangle_nonempty hB)) p hp
    have hjet : fderivWithin ℝ (canonicalMassNumerator b S)
        (closedCoordTriangle 0 B) p =
          (2 : ℝ) • fderivWithin ℝ (canonicalMass b S)
            (closedCoordTriangle 0 B) p := by
      change fderivWithin ℝ (fun q => 2 * canonicalMass b S q)
        (closedCoordTriangle 0 B) p = _
      exact fderivWithin_const_mul hunique
        ((canonicalMass_contDiffOn hB hBb H).differentiableOn
          (by norm_num) p hp) 2
    constructor
    · have hu := congrArg
        (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1, 0)) hjet
      simp only [smul_apply] at hu
      rw [hmass.1, canonicalMassIncomingDensity_eq_gap_sq_mul_normalized
        hB hBb H hp] at hu
      convert hu using 1
      ring
    · have hv := congrArg
        (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1)) hjet
      simp only [smul_apply] at hv
      rw [hmass.2, canonicalMassOutgoingDensity_eq_gap_sq_mul_normalized
        hB hBb H hp] at hv
      convert hv using 1
      ring

/-- The normalized outgoing and incoming amplitudes have the same axis
coefficient in outgoing quotient coordinates. -/
theorem normalized_amplitudes_axis_slope {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (hu : u ∈ Icc 0 B) :
    normalizedTheta B S (u, u) =
      S.lam u u * canonicalAxisSlope B S (u, u) / 2 ∧
    normalizedZeta B S (u, u) =
      S.lam u u * canonicalAxisSlope B S (u, u) / 2 := by
  have haxis := amplitude_axis_coordinate_jets_outgoingQuotient hB hBb H hu
  constructor
  · simpa only [normalizedTheta, intervalIntegral.verticalJetMean_diag,
      canonicalAxisSlope] using haxis.2.1
  · simpa only [normalizedZeta, intervalIntegral.verticalJetMean_diag,
      canonicalAxisSlope] using haxis.2.2.2

/-- The three continuous cubic-axis coefficients match the coefficients
specified by the removable rational single-input box. -/
theorem canonical_mass_numerator_axis_coefficients {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u : ℝ} (hu : u ∈ Icc 0 B) :
    2 * normalizedMassCubic b B S (u, u) =
      S.lam u u * (canonicalAxisSlope B S (u, u))^2 / 12 ∧
    2 * normalizedIncomingMassDensity b B S (u, u) =
      -(S.lam u u * (canonicalAxisSlope B S (u, u))^2 / 4) ∧
    2 * normalizedMassDensity b B S (u, u) =
      S.lam u u * (canonicalAxisSlope B S (u, u))^2 / 4 := by
  have hp : (u, u) ∈ closedCoordTriangle 0 B :=
    ⟨hu.1, le_rfl, hu.2⟩
  obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hBb H
  have hlam : S.lam u u ≠ 0 := ne_of_gt (hc.trans_le (hcl (u, u) hp))
  have hnu : S.nu u u = -S.lam u u :=
    nu_eq_neg_lam_axis hB hBb H hu
  have hθζ := normalized_amplitudes_axis_slope hB hBb H hu
  have hplus : 2 * normalizedMassDensity b B S (u, u) =
      S.lam u u * (canonicalAxisSlope B S (u, u))^2 / 4 := by
    rw [normalizedMassDensity, canonicalMassRatio_axis, hθζ.1]
    field_simp [hlam]
    ring
  have hminus : 2 * normalizedIncomingMassDensity b B S (u, u) =
      -(S.lam u u * (canonicalAxisSlope B S (u, u))^2 / 4) := by
    rw [normalizedIncomingMassDensity, canonicalMassRatio_axis,
      hnu, hθζ.2]
    field_simp [hlam]
    ring
  refine ⟨?_, hminus, hplus⟩
  rw [normalizedMassCubic_axis hB hBb H hu]
  linear_combination hplus / 3

/-- An exact gap-power factorization with a continuous coefficient gives
the uniform diagonal expansion used in each cubic box axis field. -/
theorem uniform_axis_expansion_of_gap_factor {B : ℝ} {n : ℕ}
    {F C : ℝ × ℝ → ℝ}
    (hC : ContinuousOn C (closedCoordTriangle 0 B))
    (hfactor : ∀ p ∈ closedCoordTriangle 0 B,
      F p = (p.2 - p.1) ^ n * C p) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ B → v - u < δ →
        |F (u, v) - C (u, u) * (v - u)^n| ≤ ε * (v - u)^n := by
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ :=
    intervalIntegral.uniform_diagonal_continuity hC ε hε
  refine ⟨δ, hδ, ?_⟩
  intro u v hu huv hv hgap
  have hp : (u, v) ∈ closedCoordTriangle 0 B := ⟨hu, huv, hv⟩
  have hd : 0 ≤ v - u := sub_nonneg.mpr huv
  have hpow : 0 ≤ (v - u)^n := pow_nonneg hd n
  rw [hfactor (u, v) hp]
  have hid : (v - u)^n * C (u, v) - C (u, u) * (v - u)^n =
      (C (u, v) - C (u, u)) * (v - u)^n := by ring
  rw [hid, abs_mul, abs_of_nonneg hpow]
  exact mul_le_mul_of_nonneg_right
    (le_of_lt (hclose u v hu huv hv hgap)) hpow

/-- The canonical mass numerator has all three uniform diagonal
expansions required by the cubic removable-coefficient input box. -/
theorem canonical_mass_numerator_uniform_axis_expansions {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ B → v - u < δ →
        |canonicalMassNumerator b S (u, v) -
          (S.lam u u * (canonicalAxisSlope B S (u, u)) ^ 2 / 12) *
            (v - u) ^ 3| ≤ ε * (v - u) ^ 3) ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ B → v - u < δ →
        |(fderivWithin ℝ (canonicalMassNumerator b S)
          (closedCoordTriangle 0 B) (u, v)) (1, 0) -
          (-(S.lam u u * (canonicalAxisSlope B S (u, u)) ^ 2 / 4)) *
            (v - u) ^ 2| ≤ ε * (v - u) ^ 2) ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ B → v - u < δ →
        |(fderivWithin ℝ (canonicalMassNumerator b S)
          (closedCoordTriangle 0 B) (u, v)) (0, 1) -
          (S.lam u u * (canonicalAxisSlope B S (u, u)) ^ 2 / 4) *
            (v - u) ^ 2| ≤ ε * (v - u) ^ 2) := by
  have hvalue := canonical_mass_numerator_cubic_factor hB hBb H
  have hjets := canonical_mass_numerator_coordinate_jet_factors hB hBb H
  have hvalUniform := uniform_axis_expansion_of_gap_factor
    hvalue.2.1 hvalue.2.2
  have huUniform := uniform_axis_expansion_of_gap_factor
    hjets.1 (fun p hp => (hjets.2.2 p hp).1)
  have hvUniform := uniform_axis_expansion_of_gap_factor
    hjets.2.1 (fun p hp => (hjets.2.2 p hp).2)
  constructor
  · intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := hvalUniform ε hε
    refine ⟨δ, hδ, ?_⟩
    intro u v hu huv hv hgap
    have h := hbound u v hu huv hv hgap
    rw [(canonical_mass_numerator_axis_coefficients hB hBb H
      ⟨hu, huv.trans hv⟩).1] at h
    exact h
  constructor
  · intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := huUniform ε hε
    refine ⟨δ, hδ, ?_⟩
    intro u v hu huv hv hgap
    have h := hbound u v hu huv hv hgap
    rw [(canonical_mass_numerator_axis_coefficients hB hBb H
      ⟨hu, huv.trans hv⟩).2.1] at h
    exact h
  · intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := hvUniform ε hε
    refine ⟨δ, hδ, ?_⟩
    intro u v hu huv hv hgap
    have h := hbound u v hu huv hv hgap
    rw [(canonical_mass_numerator_axis_coefficients hB hBb H
      ⟨hu, huv.trans hv⟩).2.2] at h
    exact h

/-- A canonical frozen C¹ solution supplies every structural hypothesis
of the single-input cubic rational box, at any compact triangle width. -/
@[expose] noncomputable def canonicalCubicRationalTriangleBox
    {b B c : ℝ} (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hcl : ∀ p ∈ closedCoordTriangle 0 B, c ≤ S.lam p.1 p.2) :
    intervalIntegral.CubicRationalTriangleBox 0 B c := by
  have hrad := canonical_radius_box_inputs hB hBb H hcl
  have hregular := (five_fields_contDiffOn hB hBb H)
  have hmass := canonical_mass_numerator_cubic_factor hB hBb H
  have haxis := canonical_mass_numerator_uniform_axis_expansions hB hBb H
  refine {
    J := canonicalMassNumerator b S
    r := canonicalRadius S
    ρ := canonicalNormalizedRadius S
    w := fun p => S.lam p.1 p.2
    z := fun p => S.nu p.1 p.2
    H := canonicalSourceFactor S
    h := canonicalAxisSlope B S
    J_c1 := hmass.1
    r_c1 := hrad.1
    ρ_cont := hrad.2.1
    w_c1 := hregular.1
    z_c1 := hregular.2.1
    H_c1 := (canonical_source_factor_box_inputs hB hBb H).1
    h_cont := canonical_axis_slope_continuousOn hB hBb H
    ρ_lower := fun p hp => (hrad.2.2.1 p hp).1
    w_lower := hcl
    r_factor := fun p hp => (hrad.2.2.1 p hp).2
    J_diag := ?_
    H_diag := (canonical_source_factor_box_inputs hB hBb H).2
    ρ_diag := ?_
    z_diag := fun u hu => nu_eq_neg_lam_axis hB hBb H hu
    r_u_diag := ?_
    r_v_diag := ?_
    J_axis := haxis.1
    J_u_axis := haxis.2.1
    J_v_axis := haxis.2.2 }
  · intro u hu
    simp [canonicalMassNumerator, canonicalMass_axis]
  · intro u hu
    exact (hrad.2.2.2 u hu).1
  · intro u hu
    exact (hrad.2.2.2 u hu).2.1
  · intro u hu
    exact (hrad.2.2.2 u hu).2.2

end ChristodoulouBV.C1Solution

end
