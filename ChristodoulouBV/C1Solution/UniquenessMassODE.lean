module

public import ChristodoulouBV.C1Solution.UniquenessQuadratic
public import ChristodoulouBV.C1Solution.UniquenessBoxMass
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Canonical mass as a vertical linear equation

The double mass numerator `J=2m̄` obeys `Jᵥ=j-kJ` on each outgoing ray,
where `j=λ(h-φ)²` and `k=j/r̄`. This equation supplies the Volterra
representation used in the uniqueness estimates.
-/

public section

namespace ChristodoulouBV.C1Solution

/-- The scalar source is the expansion times the canonical source factor. -/
theorem theta_eq_lam_mul_canonical_source_factor {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    S.theta p.1 p.2 = S.lam p.1 p.2 * canonicalSourceFactor S p := by
  obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hBb H
  have hne : S.lam p.1 p.2 ≠ 0 := ne_of_gt (hc.trans_le (hcl p hp))
  rw [Fields.theta, canonicalSourceFactor, outgoingQuotient]
  field_simp [hne]

/-- The vertical jet of the double canonical mass is twice the outgoing
mass density, including on the closed axis. -/
theorem canonical_mass_numerator_vertical_jet_eq_density {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 B) :
    (fderivWithin ℝ (canonicalMassNumerator b S)
      (closedCoordTriangle 0 B) p) (0, 1) =
      2 * canonicalMassOutgoingDensity b S p := by
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
  have hv := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1)) hjet
  simpa only [smul_apply, smul_eq_mul,
    (canonicalMass_coordinate_jets hB hBb H hp).2] using hv

/-- The canonical double mass solves the linear outgoing equation driven
by the weighted quadratic source, on the full closed triangle. -/
theorem canonical_mass_numerator_vertical_ode {b B : ℝ}
    (hB : 0 < B) (hBb : B < b)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ B) :
    (fderivWithin ℝ (canonicalMassNumerator b S)
      (closedCoordTriangle 0 B) (u, v)) (0, 1) =
      intervalIntegral.weightedDiagonalQuadraticKernel
        (fun p => S.lam p.1 p.2) (outgoingQuotient S) (u, v) -
      intervalIntegral.weightedDiagonalQuotientKernel
        (fun p => S.lam p.1 p.2) (outgoingQuotient S) (u, v) *
        canonicalMassNumerator b S (u, v) := by
  have hp : (u, v) ∈ closedCoordTriangle 0 B := ⟨hu, huv, hv⟩
  rw [canonical_mass_numerator_vertical_jet_eq_density hB hBb H hp]
  have htheta := theta_eq_lam_mul_canonical_source_factor hB hBb H hp
  have hsource := canonical_source_factor_eq_weightedDiagonalError hB hBb H hp
  obtain ⟨c, hc, hcl⟩ := exists_lam_lower_bound hB hBb H
  have hlam : S.lam u v ≠ 0 := ne_of_gt (hc.trans_le (hcl (u, v) hp))
  rcases eq_or_lt_of_le huv with heq | hlt
  · subst v
    have haxis := (canonical_source_factor_box_inputs hB hBb H).2
      u ⟨hu, hv⟩
    have hθ : S.theta u u = 0 := by
      simpa only [Prod.fst, Prod.snd, haxis, mul_zero] using htheta
    rw [intervalIntegral.weightedDiagonalQuadraticKernel_diag hlam,
      intervalIntegral.weightedDiagonalQuotientKernel_diag]
    simp [canonicalMassOutgoingDensity, hθ]
  · obtain ⟨cr, hcr, hrbound⟩ := canonicalRadius_lower_bound hB hBb H
    have hr : canonicalRadius S (u, v) ≠ 0 := by
      have h := hrbound (u, v) hp
      exact ne_of_gt ((mul_pos hcr (sub_pos.mpr hlt)).trans_le h)
    rw [canonicalMassOutgoingDensity, htheta, hsource]
    simp only [intervalIntegral.weightedDiagonalQuadraticKernel,
      intervalIntegral.weightedDiagonalQuotientKernel,
      canonicalMassRatio, canonicalMassNumerator, canonicalRadius,
      hlt, ↓reduceIte]
    field_simp [hlam, hr]

end ChristodoulouBV.C1Solution

end
