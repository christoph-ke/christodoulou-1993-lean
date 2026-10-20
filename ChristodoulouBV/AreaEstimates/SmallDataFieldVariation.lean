module

public import ChristodoulouBV.AreaEstimates.SmallDataExpansionVariation
import ChristodoulouBV.AreaEstimates.FieldTransport
import Mathlib.Tactic

/-!
# Small-data variation of the scalar flux fields

The logarithmic bounds control ordinary expansion variation.  Substitution
in the three field transport inequalities gives (4.36).
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

private theorem field_variation_algebra
    {D P T O I W F G L N : ℝ≥0∞}
    (hP : P ≤ 6)
    (hT : T ≤ 6000000000000 * D)
    (hO : O ≤ 6000000000000 * D)
    (hI : I ≤ 6000000000000 * D)
    (hL : L ≤ 2000000000000000 * D)
    (hN : N ≤ 2000000000000000 * D)
    (hW : W ≤ D + P * T + L)
    (hF : F ≤ D + P * O + L)
    (hG : G ≤ W + P * (T + I) + N) :
    W ≤ 10000000000000000 * D ∧
      F ≤ 10000000000000000 * D ∧
      G ≤ 10000000000000000 * D := by
  have hPT : P * T ≤ 36000000000000 * D := by
    calc
      P * T ≤ 6 * (6000000000000 * D) := by gcongr
      _ = 36000000000000 * D := by ring
  have hPO : P * O ≤ 36000000000000 * D := by
    calc
      P * O ≤ 6 * (6000000000000 * D) := by gcongr
      _ = 36000000000000 * D := by ring
  have hPTI : P * (T + I) ≤ 72000000000000 * D := by
    calc
      P * (T + I) ≤ 6 *
          (6000000000000 * D + 6000000000000 * D) := by gcongr
      _ = 72000000000000 * D := by ring
  have hW' : W ≤ 3000000000000000 * D := by
    calc
      W ≤ D + P * T + L := hW
      _ ≤ D + 36000000000000 * D + 2000000000000000 * D := by
        exact add_le_add (add_le_add le_rfl hPT) hL
      _ = 2036000000000001 * D := by ring
      _ ≤ 3000000000000000 * D := by gcongr; norm_num
  have hF' : F ≤ 3000000000000000 * D := by
    calc
      F ≤ D + P * O + L := hF
      _ ≤ D + 36000000000000 * D + 2000000000000000 * D := by
        exact add_le_add (add_le_add le_rfl hPO) hL
      _ = 2036000000000001 * D := by ring
      _ ≤ 3000000000000000 * D := by gcongr; norm_num
  have hG' : G ≤ 10000000000000000 * D := by
    calc
      G ≤ W + P * (T + I) + N := hG
      _ ≤ 3000000000000000 * D + 72000000000000 * D +
            2000000000000000 * D :=
        add_le_add (add_le_add hW' hPTI) hN
      _ = 5072000000000000 * D := by ring
      _ ≤ 10000000000000000 * D := by gcongr; norm_num
  have hWfinal : W ≤ 10000000000000000 * D :=
    hW'.trans (by gcongr; norm_num)
  have hFfinal : F ≤ 10000000000000000 * D :=
    hF'.trans (by gcongr; norm_num)
  exact ⟨hWfinal, hFfinal, hG'⟩

/-- Equation (4.36): axis and outgoing `α` variation, and incoming `β`
variation, have one universal `O(D)` bound. -/
theorem eq4_36 {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    (hD : sourceD S ≤ s4Epsilon0) (hZ : sourceZ S ≤ s4Epsilon0) :
    eVariationOn (fun t => S.alpha t t) (Ioo 0 1) ≤
        10000000000000000 * sourceD S ∧
      (⨆ u ∈ Ioo (0 : ℝ) 1,
        eVariationOn (S.alpha u) (Ioo u 1)) ≤
        10000000000000000 * sourceD S ∧
      (⨆ v ∈ Ioo (0 : ℝ) 1,
        eVariationOn (fun u => S.beta u v) (Ioo 0 v)) ≤
        10000000000000000 * sourceD S := by
  let D := sourceD S
  let Z := sourceZ S
  let P := ENNReal.ofReal (sourceP S)
  let T := eVariationOn (fun t => S.lam t t) (Ioo 0 1)
  let O := ⨆ u ∈ Ioo (0 : ℝ) 1, eVariationOn (S.lam u) (Ioo u 1)
  let I := ⨆ v ∈ Ioo (0 : ℝ) 1,
    eVariationOn (fun u => S.nu u v) (Ioo 0 v)
  let W := eVariationOn (fun t => S.alpha t t) (Ioo 0 1)
  let F := ⨆ u ∈ Ioo (0 : ℝ) 1,
    eVariationOn (S.alpha u) (Ioo u 1)
  let G := ⨆ v ∈ Ioo (0 : ℝ) 1,
    eVariationOn (fun u => S.beta u v) (Ioo 0 v)
  let L := smoothAnalyticArea (sourceLamPhiMap S) (openCoordTriangle 0 1)
  let N := smoothAnalyticArea (sourceNuPhiMap S) (openCoordTriangle 0 1)
  have hD1 : D ≤ 1 := hD.trans s4Epsilon0_le_one
  have hZ1 : Z ≤ 1 := hZ.trans s4Epsilon0_le_one
  have hsum : D + Z ≤ 2 := by
    calc
      D + Z ≤ 1 + 1 := add_le_add hD1 hZ1
      _ = 2 := by norm_num
  have hDsum : D * (D + Z) ≤ 2 * D := by
    calc
      D * (D + Z) ≤ D * 2 := by gcongr
      _ = 2 * D := by ring
  have hAreaBase : D * Z * (D + Z) ≤ 2 * D := by
    calc
      D * Z * (D + Z) ≤ D * 1 * 2 := by gcongr
      _ = 2 * D := by ring
  have hP : P ≤ 6 := by
    have h := (lemma4_2 H hr hcenter hboot).2.2
    have hDof : ENNReal.ofReal D.toReal = D :=
      ENNReal.ofReal_toReal (sourceD_ne_top_unit H)
    calc
      P ≤ ENNReal.ofReal (6 * D.toReal) := ENNReal.ofReal_le_ofReal h
      _ = 6 * D := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6), hDof]
        norm_num
      _ ≤ 6 * 1 := by gcongr
      _ = 6 := mul_one _
  obtain ⟨hLogAxis, hLogOut, hLogIn⟩ :=
    eq4_35 H hr hcenter hboot hD hZ
  have hT : T ≤ 6000000000000 * D := by
    calc
      T ≤ eVariationOn (fun t => Real.log (S.lam t t)) (Ioo 0 1) :=
        s4_axis_lam_variation_le_log H hr
      _ ≤ 3000000000000 * D * (D + Z) := hLogAxis
      _ ≤ 6000000000000 * D := by
        calc
          3000000000000 * D * (D + Z) =
              3000000000000 * (D * (D + Z)) := by ring
          _ ≤ 3000000000000 * (2 * D) := by gcongr
          _ = 6000000000000 * D := by ring
  have hO : O ≤ 6000000000000 * D := by
    calc
      O ≤ (⨆ u ∈ Ioo (0 : ℝ) 1,
        eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1)) :=
          s4_outgoing_lam_variation_le_log H hr hboot
      _ ≤ 3000000000000 * D * (D + Z) := hLogOut
      _ ≤ 6000000000000 * D := by
        calc
          3000000000000 * D * (D + Z) =
              3000000000000 * (D * (D + Z)) := by ring
          _ ≤ 3000000000000 * (2 * D) := by gcongr
          _ = 6000000000000 * D := by ring
  have hI : I ≤ 6000000000000 * D := by
    calc
      I ≤ (⨆ v ∈ Ioo (0 : ℝ) 1,
        eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo 0 v)) :=
          s4_incoming_nu_variation_le_log H hboot
      _ ≤ 3000000000000 * D * (D + Z) := hLogIn
      _ ≤ 6000000000000 * D := by
        calc
          3000000000000 * D * (D + Z) =
              3000000000000 * (D * (D + Z)) := by ring
          _ ≤ 3000000000000 * (2 * D) := by gcongr
          _ = 6000000000000 * D := by ring
  obtain ⟨hL0, hN0⟩ := eq4_34 H hr hcenter hboot hD hZ
  have hL : L ≤ 2000000000000000 * D := by
    calc
      L ≤ 1000000000000000 * (D * Z) * (D + Z) := hL0
      _ = 1000000000000000 * (D * Z * (D + Z)) := by ring
      _ ≤ 1000000000000000 * (2 * D) := by gcongr
      _ = 2000000000000000 * D := by ring
  have hN : N ≤ 2000000000000000 * D := by
    calc
      N ≤ 1000000000000000 * (D * Z) * (D + Z) := hN0
      _ = 1000000000000000 * (D * Z * (D + Z)) := by ring
      _ ≤ 1000000000000000 * (2 * D) := by gcongr
      _ = 2000000000000000 * D := by ring
  have hW : W ≤ D + P * T + L := eq4_6 H hr hcenter hboot
  have hF : F ≤ D + P * O + L := eq4_4c H hr hcenter hboot
  have hG : G ≤ W + P * (T + I) + N := by
    have h5 := eq4_5c H hr hcenter hboot
    rw [s4_axis_beta_variation_eq_alpha H,
      s4_axis_nu_variation_eq_lam H] at h5
    exact h5
  exact field_variation_algebra hP hT hO hI hL hN hW hF hG

end ChristodoulouBV

end
