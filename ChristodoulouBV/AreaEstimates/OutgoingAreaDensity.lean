module

public import ChristodoulouBV.AreaEstimates.OutgoingAreaWeighted
public import ChristodoulouBV.AreaEstimates.OutgoingAreaMajorants
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import ChristodoulouBV.Uniqueness.ExtensionIncomingSigns
import Mathlib.Tactic

/-!
# Pointwise densities for (4.21) and corrected (4.26)

The incoming logarithmic residual has the corrected `- f*` sign from the
sign correction of (4.11b)–(4.13b) and its extension to the area estimates;
see ERRATA.md, ERR-23.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace ChristodoulouBV

/-- The remaining `ρ/r³` density in the two Jacobian estimates. -/
noncomputable def sourceRhoDensity (S : Fields) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (|sourceRho S p.1 p.2| / S.r p.1 p.2 ^ 3)

private theorem rho_area_coefficient_bounds
    {r lam nu theta zeta D : ℝ}
    (hr : 0 < r) (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 2)
    (hnu0 : nu ≤ 0) (hnu : -(2 / 3) ≤ nu)
    (_hD : 0 ≤ D)
    (hdiff : |theta / lam - zeta / nu| ≤ 39 * D) :
    |-(lam * zeta / r)| ≤ |zeta| / r ∧
      |lam * (theta / lam - zeta / nu)| ≤ 39 * D ∧
      |nu * theta / r| ≤ |theta| / r ∧
      |nu * (theta / lam - zeta / nu)| ≤ 39 * D := by
  have hlam1 : lam ≤ 1 := by linarith only [hlam]
  have hnu1 : |nu| ≤ 1 := by
    rw [abs_of_nonpos hnu0]
    linarith only [hnu]
  have hz : 0 ≤ |zeta| / r := div_nonneg (abs_nonneg _) hr.le
  have ht : 0 ≤ |theta| / r := div_nonneg (abs_nonneg _) hr.le
  have hd : 0 ≤ |theta / lam - zeta / nu| := abs_nonneg _
  have h1 : lam * (|zeta| / r) ≤ |zeta| / r :=
    mul_le_of_le_one_left hz hlam1
  have h2 : lam * |theta / lam - zeta / nu| ≤ 39 * D :=
    (mul_le_of_le_one_left hd hlam1).trans hdiff
  have h3 : |nu| * (|theta| / r) ≤ |theta| / r :=
    mul_le_of_le_one_left ht hnu1
  have h4 : |nu| * |theta / lam - zeta / nu| ≤ 39 * D :=
    (mul_le_of_le_one_left hd hnu1).trans hdiff
  constructor
  · rw [abs_neg, abs_div, abs_mul, abs_of_pos hr, abs_of_nonneg hlam0]
    simpa only [mul_div_assoc] using h1
  constructor
  · simpa only [abs_mul, abs_of_nonneg hlam0] using h2
  constructor
  · rw [abs_div, abs_mul, abs_of_pos hr]
    simpa only [mul_div_assoc, mul_comm] using h3
  · simpa only [abs_mul] using h4

/-- Pointwise absolute Jacobian estimate underlying (4.21).
The universal coefficient of the rho term is `39`. -/
theorem sourceLamPhi_area_density_le {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {p : ℝ × ℝ} (hp : p ∈ openCoordTriangle 0 1) :
    ENNReal.ofReal |(fderiv ℝ (sourceLamPhiMap S) p).det| ≤
      sourceIncomingWeight S p * sourceOutgoingLogMajorant S p.2 +
        (39 * ENNReal.ofReal (sourceD S).toReal) * sourceRhoDensity S p := by
  rcases p with ⟨u, v⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hp.1.le, hp.2.1, hp.2.2⟩
  have hrpos := H.solution.radius_pos (u, v) hpU
  have hlam0 : 0 ≤ S.lam u v := (H.solution.lam_pos (u, v) hpU).le
  have hlam := Uniqueness.lam_le_half_of_initial_gauge H hr
    hp.1.le hp.2.1 hp.2.2
  have hnu0 : S.nu u v ≤ 0 := (sourceNu_le_neg_third H hboot hp).trans (by norm_num)
  have hnu := hboot.2.1 (u, v) hpU
  have hdiff := source_log_quotient_difference_bound H hr hcenter hboot hpU
  obtain ⟨h1, h2, _, _⟩ := rho_area_coefficient_bounds
    hrpos hlam0 hlam hnu0 hnu ENNReal.toReal_nonneg hdiff
  have h1e := ENNReal.ofReal_le_ofReal h1
  have h2e := ENNReal.ofReal_le_ofReal h2
  have hweight : sourceIncomingWeight S (u, v) =
      ENNReal.ofReal (|S.zeta u v| / S.r u v) := by
    change ENNReal.ofReal
      (|S.zeta u v| / C1Solution.canonicalRadius S (u, v)) = _
    rw [sourceCanonicalRadius_eq_radius H hp.1 hp.2.1 hp.2.2]
  have hJac := sourceLamPhi_jacobian_rho H hr hcenter hboot hp
  have hRes := eq4_19a H hr hcenter hboot hp
  have hpoint := scalar_jacobian_density_bound
    (q := (fderiv ℝ (sourceLamPhiMap S) (u, v)).det)
    (a := -(S.lam u v * S.zeta u v / S.r u v))
    (b := S.lam u v *
      (S.theta u v / S.lam u v - S.zeta u v / S.nu u v))
    (R := sourceOutgoingLogResidual S u v)
    (J := sourceRho S u v / S.r u v ^ 3)
    (w := sourceIncomingWeight S (u, v))
    (f := sourceOutgoingLogMajorant S v)
    (m := 1) (c := 1)
    (d := 39 * ENNReal.ofReal (sourceD S).toReal)
    (by convert hJac using 1; ring)
    (by simpa only [one_mul, hweight] using h1e)
    hRes
    (by simpa only [one_mul, mul_one, ENNReal.ofReal_ofNat,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 39)]
        using h2e)
  have hRho : |sourceRho S u v / S.r u v ^ 3| =
      |sourceRho S u v| / S.r u v ^ 3 := by
    rw [abs_div, abs_of_pos (pow_pos hrpos 3)]
  simpa only [one_mul, hRho, sourceRhoDensity] using hpoint

/-- Pointwise absolute Jacobian estimate underlying corrected (4.26).
The residual uses the `-f*` sign from the sign correction described in ERRATA.md, ERR-23. -/
theorem sourceNuPhi_area_density_le_corrected {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    {p : ℝ × ℝ} (hp : p ∈ openCoordTriangle 0 1) :
    ENNReal.ofReal |(fderiv ℝ (sourceNuPhiMap S) p).det| ≤
      sourceOutgoingWeight S p * sourceIncomingLogMajorant S p.1 +
        (39 * ENNReal.ofReal (sourceD S).toReal) * sourceRhoDensity S p := by
  rcases p with ⟨u, v⟩
  have hpU : (u, v) ∈ developmentWithInitialEdge 1 :=
    ⟨hp.1.le, hp.2.1, hp.2.2⟩
  have hrpos := H.solution.radius_pos (u, v) hpU
  have hlam0 : 0 ≤ S.lam u v := (H.solution.lam_pos (u, v) hpU).le
  have hlam := Uniqueness.lam_le_half_of_initial_gauge H hr
    hp.1.le hp.2.1 hp.2.2
  have hnu0 : S.nu u v ≤ 0 := (sourceNu_le_neg_third H hboot hp).trans (by norm_num)
  have hnu := hboot.2.1 (u, v) hpU
  have hdiff := source_log_quotient_difference_bound H hr hcenter hboot hpU
  obtain ⟨_, _, h1, h2⟩ := rho_area_coefficient_bounds
    hrpos hlam0 hlam hnu0 hnu ENNReal.toReal_nonneg hdiff
  have h1e := ENNReal.ofReal_le_ofReal h1
  have h2e := ENNReal.ofReal_le_ofReal h2
  have hweight : sourceOutgoingWeight S (u, v) =
      ENNReal.ofReal (|S.theta u v| / S.r u v) := by
    change ENNReal.ofReal
      (|S.theta u v| / C1Solution.canonicalRadius S (u, v)) = _
    rw [sourceCanonicalRadius_eq_radius H hp.1 hp.2.1 hp.2.2]
  have hJac := sourceNuPhi_jacobian_rho_corrected H hr hcenter hboot hp
  have hRes := eq4_25a H hr hcenter hboot hp
  have hpoint := scalar_jacobian_density_bound
    (q := (fderiv ℝ (sourceNuPhiMap S) (u, v)).det)
    (a := S.nu u v * S.theta u v / S.r u v)
    (b := S.nu u v *
      (S.theta u v / S.lam u v - S.zeta u v / S.nu u v))
    (R := sourceIncomingLogResidual S u v)
    (J := sourceRho S u v / S.r u v ^ 3)
    (w := sourceOutgoingWeight S (u, v))
    (f := sourceIncomingLogMajorant S u)
    (m := 1) (c := 1)
    (d := 39 * ENNReal.ofReal (sourceD S).toReal)
    (by convert hJac using 1; ring)
    (by simpa only [one_mul, hweight] using h1e)
    hRes
    (by simpa only [one_mul, mul_one, ENNReal.ofReal_ofNat,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 39)]
        using h2e)
  have hRho : |sourceRho S u v / S.r u v ^ 3| =
      |sourceRho S u v| / S.r u v ^ 3 := by
    rw [abs_div, abs_of_pos (pow_pos hrpos 3)]
  simpa only [one_mul, hRho, sourceRhoDensity] using hpoint

end ChristodoulouBV

end
