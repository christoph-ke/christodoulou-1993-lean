module

public import ChristodoulouBV.AreaEstimates.SmallDataAxis
import Mathlib.Tactic

/-!
# The first incoming coupled inequality

The fixed threshold below is chosen before the solution.  Equation (4.30)
itself is valid without its smallness hypotheses; they are retained in the
public statement for use in the small-data estimates.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

/-- A universal smallness threshold used throughout the two absorptions. -/
noncomputable def s4Epsilon0 : ℝ≥0∞ := 1 / 1000000000000

/-- The universal threshold is strictly positive. -/
theorem s4Epsilon0_pos : 0 < s4Epsilon0 := by
  unfold s4Epsilon0
  norm_num

/-- The universal threshold does not exceed one. -/
theorem s4Epsilon0_le_one : s4Epsilon0 ≤ 1 := by
  unfold s4Epsilon0
  norm_num

private theorem first_incoming_algebra
    {D X Z A B N V : ℝ≥0∞} (hXZ : X ≤ Z)
    (hN : N ≤ 39 * X * V + 39 * (D + X) * A)
    (hV : V ≤ 108 * D ^ 2 + B) :
    N ≤ 5000 * D ^ 2 * Z + 5000 * Z * B + 5000 * (D + Z) * A := by
  calc
    N ≤ 39 * X * V + 39 * (D + X) * A := hN
    _ ≤ 39 * X * (108 * D ^ 2 + B) + 39 * (D + X) * A := by
      gcongr
    _ = 4212 * D ^ 2 * X + 39 * X * B + 39 * (D + X) * A := by ring
    _ ≤ 4212 * D ^ 2 * Z + 39 * Z * B + 39 * (D + Z) * A := by
      gcongr
    _ ≤ 5000 * D ^ 2 * Z + 5000 * Z * B + 5000 * (D + Z) * A := by
      gcongr <;> norm_num

/-- Equation (4.30), with the universal coefficient `5000`. -/
theorem eq4_30 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    (_hD : sourceD S ≤ s4Epsilon0) (_hZ : sourceZ S ≤ s4Epsilon0) :
    smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 1) ≤
      5000 * sourceD S ^ 2 * sourceZ S +
        5000 * sourceZ S *
          smoothAnalyticArea (sourcePhiBetaNuMap S) (openCoordTriangle 0 1) +
        5000 * (sourceD S + sourceZ S) *
          smoothAnalyticArea (sourcePhiAlphaLamMap S) (openCoordTriangle 0 1) := by
  have hD2 : ENNReal.ofReal (108 * (sourceD S).toReal ^ 2) =
      108 * sourceD S ^ 2 := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 108),
      ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (sourceD_ne_top_unit H)]
    norm_num
  have hN := eq4_29 H hr hcenter hboot
  rw [s4_axis_log_nu_variation_eq_lam H] at hN
  have hV := eq4_14 H hr hcenter hboot
  rw [hD2] at hV
  exact first_incoming_algebra (le_max_left _ _) hN hV

end ChristodoulouBV

end
