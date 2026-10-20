module

public import ChristodoulouBV.AreaEstimates.SmallDataFourAreas
import Mathlib.Tactic

/-!
# Small-data logarithmic variation on the axis and null slices

Equation (4.35) follows from the two scalar-quotient area bounds and the
sign-corrected incoming log transport estimate.
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

private theorem log_variation_algebra
    {D X Y Z A B V O I : ℝ≥0∞}
    (hX : X ≤ Z) (hY : Y ≤ Z)
    (hA : A ≤ 30000000000 * (D * Z))
    (hB : B ≤ 30000000000 * (D * Z))
    (hV : V ≤ 108 * D ^ 2 + B)
    (hO : O ≤ 108 * D ^ 2 + 54 * D * X + B)
    (hI : I ≤ 63 * D * Y + V + A) :
    V ≤ 3000000000000 * D * (D + Z) ∧
      O ≤ 3000000000000 * D * (D + Z) ∧
      I ≤ 3000000000000 * D * (D + Z) := by
  let Q := D * (D + Z)
  have hD2 : D ^ 2 ≤ Q := by
    calc
      D ^ 2 = D * D := pow_two D
      _ ≤ D * (D + Z) := by
        gcongr
        exact le_add_right le_rfl
  have hDZ : D * Z ≤ Q := by
    dsimp [Q]
    gcongr
    exact le_add_left le_rfl
  have hDX : D * X ≤ Q := by
    calc
      D * X ≤ D * Z := by gcongr
      _ ≤ Q := hDZ
  have hDY : D * Y ≤ Q := by
    calc
      D * Y ≤ D * Z := by gcongr
      _ ≤ Q := hDZ
  have hA' : A ≤ 30000000000 * Q := hA.trans (by gcongr)
  have hB' : B ≤ 30000000000 * Q := hB.trans (by gcongr)
  have hV' : V ≤ 1000000000000 * Q := by
    calc
      V ≤ 108 * D ^ 2 + B := hV
      _ ≤ 108 * Q + 30000000000 * Q :=
        add_le_add (by gcongr) hB'
      _ = 30000000108 * Q := by ring
      _ ≤ 1000000000000 * Q := by gcongr; norm_num
  have hO' : O ≤ 1000000000000 * Q := by
    calc
      O ≤ 108 * D ^ 2 + 54 * D * X + B := hO
      _ ≤ 108 * Q + 54 * Q + 30000000000 * Q := by
        apply add_le_add
        · exact add_le_add (by gcongr) (by
            calc
              54 * D * X = 54 * (D * X) := by ring
              _ ≤ 54 * Q := by gcongr)
        · exact hB'
      _ = 30000000162 * Q := by ring
      _ ≤ 1000000000000 * Q := by gcongr; norm_num
  have hI' : I ≤ 3000000000000 * Q := by
    calc
      I ≤ 63 * D * Y + V + A := hI
      _ ≤ 63 * Q + 1000000000000 * Q + 30000000000 * Q := by
        apply add_le_add
        · apply add_le_add
          · calc
              63 * D * Y = 63 * (D * Y) := by ring
              _ ≤ 63 * Q := by gcongr
          · exact hV'
        · exact hA'
      _ = 1030000000063 * Q := by ring
      _ ≤ 3000000000000 * Q := by gcongr; norm_num
  have hVfinal : V ≤ 3000000000000 * Q :=
    hV'.trans (by gcongr; norm_num)
  have hOfinal : O ≤ 3000000000000 * Q :=
    hO'.trans (by gcongr; norm_num)
  dsimp [Q] at hVfinal hOfinal hI'
  simpa only [mul_assoc] using And.intro hVfinal (And.intro hOfinal hI')

/-- Equation (4.35): one universal constant controls the axis and both
families of logarithmic null-slice variations. -/
theorem eq4_35 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    (hD : sourceD S ≤ s4Epsilon0) (hZ : sourceZ S ≤ s4Epsilon0) :
    eVariationOn (fun t => Real.log (S.lam t t)) (Ioo 0 1) ≤
        3000000000000 * sourceD S * (sourceD S + sourceZ S) ∧
      (⨆ u ∈ Ioo (0 : ℝ) 1,
        eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1)) ≤
        3000000000000 * sourceD S * (sourceD S + sourceZ S) ∧
      (⨆ v ∈ Ioo (0 : ℝ) 1,
        eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo 0 v)) ≤
        3000000000000 * sourceD S * (sourceD S + sourceZ S) := by
  let D := sourceD S
  let X := sourceX S
  let Y := sourceY S
  let Z := sourceZ S
  let A := smoothAnalyticArea (sourcePhiAlphaLamMap S) (openCoordTriangle 0 1)
  let B := smoothAnalyticArea (sourcePhiBetaNuMap S) (openCoordTriangle 0 1)
  let V := eVariationOn (fun t => Real.log (S.lam t t)) (Ioo 0 1)
  let O := ⨆ u ∈ Ioo (0 : ℝ) 1,
    eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1)
  let I := ⨆ v ∈ Ioo (0 : ℝ) 1,
    eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo 0 v)
  have hDof : ENNReal.ofReal D.toReal = D :=
    ENNReal.ofReal_toReal (sourceD_ne_top_unit H)
  have hD2 : ENNReal.ofReal (108 * D.toReal ^ 2) = 108 * D ^ 2 := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 108),
      ENNReal.ofReal_pow ENNReal.toReal_nonneg, hDof]
    norm_num
  have hD54 : ENNReal.ofReal (54 * D.toReal) = 54 * D := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 54), hDof]
    norm_num
  have hD63 : ENNReal.ofReal (63 * D.toReal) = 63 * D := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 63), hDof]
    norm_num
  obtain ⟨hA, hB⟩ := eq4_33 H hr hcenter hboot hD hZ
  have hV : V ≤ 108 * D ^ 2 + B := by
    simpa only [V, D, B, hD2] using eq4_14 H hr hcenter hboot
  have hO : O ≤ 108 * D ^ 2 + 54 * D * X + B := by
    simpa only [O, D, X, B, hD2, hD54] using
      eq4_12c H hr hcenter hboot
  have hI : I ≤ 63 * D * Y + V + A := by
    have h := eq4_13c H hr hcenter hboot
    rw [s4_axis_log_nu_variation_eq_lam H, hD63] at h
    exact h
  exact log_variation_algebra (le_max_left _ _) (le_max_right _ _)
    hA hB hV hO hI

end ChristodoulouBV

end
