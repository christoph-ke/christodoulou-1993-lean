module

public import ChristodoulouBV.AreaEstimates.SmallDataQuotientVariation
import Mathlib.Tactic

/-!
# Closing the null integral size

Lemma 4.1 bounds `X` and `Y` by quotient variation.  The preceding field
and expansion estimates therefore make `Z` linear in the initial variation.
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

/-- The two null integral suprema are bounded by the respective quotient
variation suprema. -/
theorem s4_XY_le_quotient_variations {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    sourceX S ≤ (⨆ u ∈ Ioo (0 : ℝ) 1,
        eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u 1)) ∧
      sourceY S ≤ (⨆ v ∈ Ioo (0 : ℝ) 1,
        eVariationOn (fun u => S.beta u v / S.nu u v) (Ioo 0 v)) := by
  obtain ⟨hOut, hIn⟩ := lemma4_1 H
  constructor
  · unfold sourceX
    apply iSup_le
    intro u
    apply iSup_le
    intro hu
    exact (hOut u hu).trans
      (le_iSup_of_le u (le_iSup_of_le hu le_rfl))
  · unfold sourceY
    apply iSup_le
    intro v
    apply iSup_le
    intro hv
    exact (hIn v hv).trans
      (le_iSup_of_le v (le_iSup_of_le hv le_rfl))

private theorem z_algebra
    {D X Y O I F G : ℝ≥0∞} (hD : D ≤ 1)
    (hO : O ≤ 6000000000000 * D)
    (hI : I ≤ 6000000000000 * D)
    (hF : F ≤ 10000000000000000 * D)
    (hG : G ≤ 10000000000000000 * D)
    (hX : X ≤ 18 * D * O + 3 * F)
    (hY : Y ≤ 36 * D * I + 3 * G) :
    max X Y ≤ 100000000000000000 * D := by
  have hD2 : D ^ 2 ≤ D := by
    calc
      D ^ 2 = D * D := pow_two D
      _ ≤ D * 1 := mul_le_mul_of_nonneg_left hD bot_le
      _ = D := mul_one D
  apply max_le
  · calc
      X ≤ 18 * D * O + 3 * F := hX
      _ ≤ 18 * D * (6000000000000 * D) +
            3 * (10000000000000000 * D) := by gcongr
      _ = 108000000000000 * D ^ 2 + 30000000000000000 * D := by ring
      _ ≤ 108000000000000 * D + 30000000000000000 * D := by gcongr
      _ = 30108000000000000 * D := by ring
      _ ≤ 100000000000000000 * D := by gcongr; norm_num
  · calc
      Y ≤ 36 * D * I + 3 * G := hY
      _ ≤ 36 * D * (6000000000000 * D) +
            3 * (10000000000000000 * D) := by gcongr
      _ = 216000000000000 * D ^ 2 + 30000000000000000 * D := by ring
      _ ≤ 216000000000000 * D + 30000000000000000 * D := by gcongr
      _ = 30216000000000000 * D := by ring
      _ ≤ 100000000000000000 * D := by gcongr; norm_num

/-- The conclusion `Z ≤ cD` of Lemma 4.3, with an explicit universal
coefficient. -/
theorem s4_Z_le_sourceD {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    (hD : sourceD S ≤ s4Epsilon0) (hZ : sourceZ S ≤ s4Epsilon0) :
    sourceZ S ≤ 100000000000000000 * sourceD S := by
  let D := sourceD S
  let Z := sourceZ S
  let O := ⨆ u ∈ Ioo (0 : ℝ) 1, eVariationOn (S.lam u) (Ioo u 1)
  let I := ⨆ v ∈ Ioo (0 : ℝ) 1,
    eVariationOn (fun u => S.nu u v) (Ioo 0 v)
  let F := ⨆ u ∈ Ioo (0 : ℝ) 1,
    eVariationOn (S.alpha u) (Ioo u 1)
  let G := ⨆ v ∈ Ioo (0 : ℝ) 1,
    eVariationOn (fun u => S.beta u v) (Ioo 0 v)
  let QO := ⨆ u ∈ Ioo (0 : ℝ) 1,
    eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u 1)
  let QI := ⨆ v ∈ Ioo (0 : ℝ) 1,
    eVariationOn (fun u => S.beta u v / S.nu u v) (Ioo 0 v)
  have hD1 : D ≤ 1 := hD.trans s4Epsilon0_le_one
  have hZ1 : Z ≤ 1 := hZ.trans s4Epsilon0_le_one
  have hsum : D + Z ≤ 2 := by
    calc
      D + Z ≤ 1 + 1 := add_le_add hD1 hZ1
      _ = 2 := by norm_num
  obtain ⟨_, hLogOut, hLogIn⟩ := eq4_35 H hr hcenter hboot hD hZ
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
          _ ≤ 3000000000000 * (D * 2) := by gcongr
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
          _ ≤ 3000000000000 * (D * 2) := by gcongr
          _ = 6000000000000 * D := by ring
  obtain ⟨_, hF, hG⟩ := eq4_36 H hr hcenter hboot hD hZ
  have hQO : QO ≤ 18 * D * O + 3 * F :=
    s4_outgoing_quotient_variation_le H hr hcenter hboot
  have hQI : QI ≤ 36 * D * I + 3 * G :=
    s4_incoming_quotient_variation_le H hr hcenter hboot
  obtain ⟨hX, hY⟩ := s4_XY_le_quotient_variations H
  exact z_algebra hD1 hO hI hF hG (hX.trans hQO) (hY.trans hQI)

end ChristodoulouBV

end
