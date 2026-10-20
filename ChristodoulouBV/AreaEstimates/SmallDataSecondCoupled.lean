module

public import ChristodoulouBV.AreaEstimates.SmallDataFirstCoupled
import ChristodoulouBV.AreaEstimates.FieldTransport
import Mathlib.Tactic

/-!
# The first small-data absorption

The regular-axis transport estimates give a self-term in the incoming
scalar-quotient area.  The universal threshold makes its coefficient at most
one half; compact C¹ area finiteness then permits cancellation.
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

/-- The first universal coefficient is at most one half under the fixed
smallness threshold. -/
theorem s4_first_coefficient_le_half {D Z : ℝ≥0∞}
    (hD : D ≤ s4Epsilon0) (hZ : Z ≤ s4Epsilon0) :
    864 * D * Z ≤ 1 / 2 := by
  calc
    864 * D * Z ≤ 864 * s4Epsilon0 * s4Epsilon0 := by gcongr
    _ ≤ 1 / 2 := by
      unfold s4Epsilon0
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

/-- The first absorption of the `cDZ` area self-term, using a finite area. -/
theorem s4_smallness_initial {D Z B R : ℝ≥0∞}
    (hD : D ≤ s4Epsilon0) (hZ : Z ≤ s4Epsilon0)
    (hB : B ≠ ∞) (h : B ≤ R + 864 * D * Z * B) :
    B ≤ 2 * R := by
  have hcoeff : 864 * D * Z * B ≤ (1 / 2) * B := by
    calc
      864 * D * Z * B = (864 * D * Z) * B := by ring
      _ ≤ (1 / 2) * B :=
        mul_le_mul_of_nonneg_right (s4_first_coefficient_le_half hD hZ) bot_le
  have hraw : B ≤ R + (1 / 2) * B :=
    h.trans (add_le_add_right hcoeff R)
  have hhalfB : (1 / 2 : ℝ≥0∞) * B ≤ B := by
    calc
      (1 / 2 : ℝ≥0∞) * B ≤ 1 * B := by gcongr; norm_num
      _ = B := one_mul B
  have hhalfFinite : (1 / 2 : ℝ≥0∞) * B ≠ ∞ :=
    ne_top_of_le_ne_top hB hhalfB
  have hhalf : (1 / 2 : ℝ≥0∞) + (1 / 2) = 1 := by
    rw [div_eq_mul_inv, one_mul, ← two_mul,
      ENNReal.mul_inv_cancel (by norm_num) (by finiteness)]
  have hsplit : B = (1 / 2 : ℝ≥0∞) * B + (1 / 2) * B := by
    calc
      B = 1 * B := (one_mul B).symm
      _ = ((1 / 2 : ℝ≥0∞) + (1 / 2)) * B := by rw [hhalf]
      _ = _ := add_mul _ _ _
  have hshift : (1 / 2 : ℝ≥0∞) * B + (1 / 2) * B ≤
      R + (1 / 2) * B := by
    simpa only [← hsplit] using hraw
  have hhalfLe : (1 / 2 : ℝ≥0∞) * B ≤ R :=
    ENNReal.le_of_add_le_add_right hhalfFinite hshift
  have htwohalf : (2 : ℝ≥0∞) * (1 / 2) = 1 := by
    simpa only [two_mul] using hhalf
  calc
    B = 2 * ((1 / 2 : ℝ≥0∞) * B) := by
      rw [← mul_assoc, htwohalf, one_mul]
    _ ≤ 2 * R := by gcongr

private theorem second_area_algebra
    {D X Z P T V W L N B : ℝ≥0∞}
    (hD : D ≤ 1) (hXZ : X ≤ Z) (hP : P ≤ 6 * D)
    (hT : T ≤ V) (hV : V ≤ 108 * D ^ 2 + B)
    (hW : W ≤ D + P * T + L)
    (hB : B ≤ 72 * X * (W + 6 * D * T) + 72 * (X + D) * N) :
    B ≤ (100000 * D * Z + 100 * Z * L + 100 * (D + Z) * N) +
      864 * D * Z * B := by
  have hW' : W ≤ D + 6 * D * V + L := by
    calc
      W ≤ D + P * T + L := hW
      _ ≤ D + (6 * D) * V + L := by gcongr
  have hWT : W + 6 * D * T ≤ D + 12 * D * V + L := by
    calc
      W + 6 * D * T ≤ (D + 6 * D * V + L) + 6 * D * V := by
        exact add_le_add hW' (by gcongr)
      _ = D + 12 * D * V + L := by ring
  have hD2 : D ^ 2 ≤ D := by
    calc
      D ^ 2 = D * D := pow_two D
      _ ≤ D * 1 := mul_le_mul_of_nonneg_left hD bot_le
      _ = D := mul_one D
  have hD3 : D ^ 3 ≤ D := by
    calc
      D ^ 3 = D ^ 2 * D := by ring
      _ ≤ D * D := mul_le_mul_of_nonneg_right hD2 bot_le
      _ ≤ D := by simpa only [pow_two] using hD2
  calc
    B ≤ 72 * X * (W + 6 * D * T) + 72 * (X + D) * N := hB
    _ ≤ 72 * X * (D + 12 * D * V + L) + 72 * (X + D) * N := by
      gcongr
    _ ≤ 72 * X * (D + 12 * D * (108 * D ^ 2 + B) + L) +
          72 * (X + D) * N := by gcongr
    _ = 72 * X * D + 93312 * X * D ^ 3 + 864 * D * X * B +
          72 * X * L + 72 * (X + D) * N := by ring
    _ ≤ 72 * Z * D + 93312 * Z * D + 864 * D * Z * B +
          72 * Z * L + 72 * (Z + D) * N := by
      gcongr
    _ ≤ (100000 * D * Z + 100 * Z * L + 100 * (D + Z) * N) +
          864 * D * Z * B := by
      have hDZ : 72 * Z * D + 93312 * Z * D ≤ 100000 * D * Z := by
        calc
          72 * Z * D + 93312 * Z * D = 93384 * (D * Z) := by ring
          _ ≤ 100000 * (D * Z) := by gcongr; norm_num
          _ = 100000 * D * Z := by ring
      have hL : 72 * Z * L ≤ 100 * Z * L := by gcongr; norm_num
      have hN : 72 * (Z + D) * N ≤ 100 * (D + Z) * N := by
        rw [add_comm Z D]
        gcongr
        norm_num
      calc
        72 * Z * D + 93312 * Z * D + 864 * D * Z * B +
            72 * Z * L + 72 * (Z + D) * N ≤
            100000 * D * Z + 864 * D * Z * B +
              100 * Z * L + 100 * (D + Z) * N := by
          gcongr
        _ = _ := by ring

/-- Equation (4.31), with one fixed threshold and universal coefficient
`200000`. -/
theorem eq4_31 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    (hD : sourceD S ≤ s4Epsilon0) (hZ : sourceZ S ≤ s4Epsilon0) :
    smoothAnalyticArea (sourcePhiBetaNuMap S) (openCoordTriangle 0 1) ≤
      200000 * (sourceD S * sourceZ S) +
        200000 * sourceZ S *
          smoothAnalyticArea (sourceLamPhiMap S) (openCoordTriangle 0 1) +
        200000 * (sourceD S + sourceZ S) *
          smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 1) := by
  let D := sourceD S
  let Z := sourceZ S
  let P := ENNReal.ofReal (sourceP S)
  let T := eVariationOn (fun t => S.lam t t) (Ioo 0 1)
  let V := eVariationOn (fun t => Real.log (S.lam t t)) (Ioo 0 1)
  let W := eVariationOn (fun t => S.alpha t t) (Ioo 0 1)
  let L := smoothAnalyticArea (sourceLamPhiMap S) (openCoordTriangle 0 1)
  let N := smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 1)
  let B := smoothAnalyticArea (sourcePhiBetaNuMap S) (openCoordTriangle 0 1)
  have hP : P ≤ 6 * D := by
    have h := (lemma4_2 H hr hcenter hboot).2.2
    calc
      P ≤ ENNReal.ofReal (6 * (sourceD S).toReal) :=
        ENNReal.ofReal_le_ofReal h
      _ = 6 * D := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6),
          ENNReal.ofReal_toReal (sourceD_ne_top_unit H)]
        simp only [ENNReal.ofReal_ofNat, D]
  have hT : T ≤ V := s4_axis_lam_variation_le_log H hr
  have hD2 : ENNReal.ofReal (108 * (sourceD S).toReal ^ 2) =
      108 * D ^ 2 := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 108),
      ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (sourceD_ne_top_unit H)]
    simp only [ENNReal.ofReal_ofNat, D]
  have hV : V ≤ 108 * D ^ 2 + B := by
    simpa only [V, D, B, hD2] using eq4_14 H hr hcenter hboot
  have hW : W ≤ D + P * T + L :=
    eq4_6 H hr hcenter hboot
  have hArea : B ≠ ∞ := (s4_four_areas_ne_top H hboot).2.1
  have h18 := eq4_18 H hr hcenter hboot
  rw [s4_axis_beta_variation_eq_alpha H,
    s4_axis_nu_variation_eq_lam H] at h18
  have hXZ : sourceX S ≤ Z := by
    change sourceX S ≤ sourceZ S
    exact le_max_left _ _
  have hD1 : D ≤ 1 := hD.trans s4Epsilon0_le_one
  have hraw : B ≤ (100000 * D * Z + 100 * Z * L + 100 * (D + Z) * N) +
      864 * D * Z * B :=
    second_area_algebra hD1 hXZ hP hT hV hW h18
  have hAbs := s4_smallness_initial hD hZ hArea hraw
  change B ≤ 200000 * (D * Z) + 200000 * Z * L +
    200000 * (D + Z) * N
  calc
    B ≤ 2 * (100000 * D * Z + 100 * Z * L + 100 * (D + Z) * N) := hAbs
    _ = 200000 * (D * Z) + 200 * Z * L + 200 * (D + Z) * N := by ring
    _ ≤ 200000 * (D * Z) + 200000 * Z * L +
          200000 * (D + Z) * N := by gcongr <;> norm_num

end ChristodoulouBV

end
