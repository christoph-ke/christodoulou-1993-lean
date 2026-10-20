module

public import ChristodoulouBV.AreaEstimates.SmallDataSliceTV
import Mathlib.Tactic

/-!
# Uniform complete slice variation bounds

These estimates combine the three variations for quantitative existence with
one real numerical coefficient for outgoing and incoming slices.
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

private theorem slice_tv_algebra {D O I F G LO LI QO QI : ℝ≥0∞}
    (hD : D ≤ 1)
    (hF : F ≤ s4UniversalC * D) (hG : G ≤ s4UniversalC * D)
    (hLO : LO ≤ s4UniversalC * D ^ 2)
    (hLI : LI ≤ s4UniversalC * D ^ 2)
    (hO : O ≤ LO) (hI : I ≤ LI)
    (hQO : QO ≤ 18 * D * O + 3 * F)
    (hQI : QI ≤ 36 * D * I + 3 * G) :
    QO + QO + LO ≤ 100 * s4UniversalC * D ∧
      QI + QI + LI ≤ 100 * s4UniversalC * D := by
  have hD2 : D ^ 2 ≤ D := by
    calc
      D ^ 2 = D * D := pow_two D
      _ ≤ D * 1 := by gcongr
      _ = D := by ring
  have hLO' : LO ≤ s4UniversalC * D :=
    hLO.trans (by gcongr)
  have hLI' : LI ≤ s4UniversalC * D :=
    hLI.trans (by gcongr)
  have hQO' : QO ≤ 39 * s4UniversalC * D := by
    calc
      QO ≤ 18 * D * O + 3 * F := hQO
      _ ≤ 18 * D * (s4UniversalC * D) +
            3 * (s4UniversalC * D) := by
        gcongr
        exact hO.trans hLO'
      _ = 18 * s4UniversalC * D ^ 2 +
            3 * s4UniversalC * D := by ring
      _ ≤ 18 * s4UniversalC * D +
            3 * s4UniversalC * D := by gcongr
      _ ≤ 39 * s4UniversalC * D := by
        ring_nf
        gcongr
        norm_num
  have hQI' : QI ≤ 39 * s4UniversalC * D := by
    calc
      QI ≤ 36 * D * I + 3 * G := hQI
      _ ≤ 36 * D * (s4UniversalC * D) +
            3 * (s4UniversalC * D) := by
        gcongr
        exact hI.trans hLI'
      _ = 36 * s4UniversalC * D ^ 2 +
            3 * s4UniversalC * D := by ring
      _ ≤ 36 * s4UniversalC * D +
            3 * s4UniversalC * D := by gcongr
      _ = 39 * s4UniversalC * D := by ring
  constructor
  · calc
      QO + QO + LO ≤ 39 * s4UniversalC * D +
          39 * s4UniversalC * D + s4UniversalC * D := by
            exact add_le_add (add_le_add hQO' hQO') hLO'
      _ = 79 * s4UniversalC * D := by ring
      _ ≤ 100 * s4UniversalC * D := by gcongr; norm_num
  · calc
      QI + QI + LI ≤ 39 * s4UniversalC * D +
          39 * s4UniversalC * D + s4UniversalC * D := by
            exact add_le_add (add_le_add hQI' hQI') hLI'
      _ = 79 * s4UniversalC * D := by ring
      _ ≤ 100 * s4UniversalC * D := by gcongr; norm_num

/-- The three-term TV bound holds uniformly on every interior outgoing
slice and every incoming slice, with the same coefficient. -/
theorem s4_interior_three_term_slice_tv {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    (hD : sourceD S ≤ s4Epsilon0) (hZ : sourceZ S ≤ s4Epsilon0) :
    (∀ u ∈ Ioo (0 : ℝ) 1,
      eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u 1) +
        eVariationOn (S.phi u) (Ioo u 1) +
        eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1) ≤
          ENNReal.ofReal (s4SliceTVK * (sourceD S).toReal)) ∧
    (∀ v ∈ Ioo (0 : ℝ) 1,
      eVariationOn (fun u => S.beta u v / S.nu u v) (Ioo 0 v) +
        eVariationOn (fun u => S.phi u v) (Ioo 0 v) +
        eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo 0 v) ≤
          ENNReal.ofReal (s4SliceTVK * (sourceD S).toReal)) := by
  let D := sourceD S
  let O := ⨆ u ∈ Ioo (0 : ℝ) 1, eVariationOn (S.lam u) (Ioo u 1)
  let I := ⨆ v ∈ Ioo (0 : ℝ) 1,
    eVariationOn (fun u => S.nu u v) (Ioo 0 v)
  let F := ⨆ u ∈ Ioo (0 : ℝ) 1,
    eVariationOn (S.alpha u) (Ioo u 1)
  let G := ⨆ v ∈ Ioo (0 : ℝ) 1,
    eVariationOn (fun u => S.beta u v) (Ioo 0 v)
  let LO := ⨆ u ∈ Ioo (0 : ℝ) 1,
    eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1)
  let LI := ⨆ v ∈ Ioo (0 : ℝ) 1,
    eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo 0 v)
  let QO := ⨆ u ∈ Ioo (0 : ℝ) 1,
    eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u 1)
  let QI := ⨆ v ∈ Ioo (0 : ℝ) 1,
    eVariationOn (fun u => S.beta u v / S.nu u v) (Ioo 0 v)
  obtain ⟨_, ⟨_, hF, hG⟩, ⟨_, hLO, hLI⟩, _, _⟩ :=
    lemma4_3 H hr hcenter hboot hD hZ
  have hO : O ≤ LO := s4_outgoing_lam_variation_le_log H hr hboot
  have hI : I ≤ LI := s4_incoming_nu_variation_le_log H hboot
  have hQO : QO ≤ 18 * D * O + 3 * F :=
    s4_outgoing_quotient_variation_le H hr hcenter hboot
  have hQI : QI ≤ 36 * D * I + 3 * G :=
    s4_incoming_quotient_variation_le H hr hcenter hboot
  have hK : ENNReal.ofReal (s4SliceTVK * D.toReal) =
      100 * s4UniversalC * D := by
    rw [ENNReal.ofReal_mul (le_of_lt s4SliceTVK_pos),
      ENNReal.ofReal_toReal (sourceD_ne_top_unit H)]
    norm_num [s4SliceTVK_eq, s4UniversalC, D]
  obtain ⟨hOut, hIn⟩ := slice_tv_algebra
    (hD.trans s4Epsilon0_le_one) hF hG hLO hLI hO hI hQO hQI
  constructor
  · intro u hu
    have hPhi : eVariationOn (S.phi u) (Ioo u 1) ≤ QO := by
      rw [source_outgoing_phi_variation_eq_weight H hu]
      exact (outgoing_scalar_variation_bound_unit hu H).trans
        (le_iSup_of_le u (le_iSup_of_le hu le_rfl))
    have hQ : eVariationOn (fun v => S.alpha u v / S.lam u v)
        (Ioo u 1) ≤ QO := le_iSup_of_le u (le_iSup_of_le hu le_rfl)
    have hL : eVariationOn (fun v => Real.log (S.lam u v))
        (Ioo u 1) ≤ LO := le_iSup_of_le u (le_iSup_of_le hu le_rfl)
    calc
      _ ≤ QO + QO + LO := add_le_add (add_le_add hQ hPhi) hL
      _ ≤ _ := by rw [hK]; exact hOut
  · intro v hv
    have hPhi : eVariationOn (fun u => S.phi u v) (Ioo 0 v) ≤ QI := by
      rw [source_incoming_phi_variation_eq_weight H hv]
      exact (incoming_scalar_variation_bound_unit hv H).trans
        (le_iSup_of_le v (le_iSup_of_le hv le_rfl))
    have hQ : eVariationOn (fun u => S.beta u v / S.nu u v)
        (Ioo 0 v) ≤ QI := le_iSup_of_le v (le_iSup_of_le hv le_rfl)
    have hL : eVariationOn (fun u => Real.log (-S.nu u v))
        (Ioo 0 v) ≤ LI := le_iSup_of_le v (le_iSup_of_le hv le_rfl)
    calc
      _ ≤ QI + QI + LI := add_le_add (add_le_add hQ hPhi) hL
      _ ≤ _ := by rw [hK]; exact hIn

/-- The same three-term bound on the initial outgoing characteristic. -/
theorem s4_initial_three_term_slice_tv {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2) :
    eVariationOn (fun v => S.alpha 0 v / S.lam 0 v) (Ioo 0 1) +
      eVariationOn (S.phi 0) (Ioo 0 1) +
      eVariationOn (fun v => Real.log (S.lam 0 v)) (Ioo 0 1) ≤
        ENNReal.ofReal (s4SliceTVK * (sourceD S).toReal) := by
  have hlog : eVariationOn (fun v => Real.log (S.lam 0 v))
      (Ioo (0 : ℝ) 1) = 0 := by
    have hEq : EqOn (fun v => Real.log (S.lam 0 v))
        (fun _ => Real.log (1 / 2 : ℝ)) (Ioo (0 : ℝ) 1) := by
      intro v hv
      change Real.log (S.lam 0 v) = Real.log (1 / 2 : ℝ)
      rw [initial_lam_eq_of_gauge H hr hv]
    rw [eVariationOn.congr hEq]
    apply eVariationOn.constant_on
    rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩
    rfl
  have hK : ENNReal.ofReal (s4SliceTVK * (sourceD S).toReal) =
      100 * s4UniversalC * sourceD S := by
    rw [ENNReal.ofReal_mul (le_of_lt s4SliceTVK_pos),
      ENNReal.ofReal_toReal (sourceD_ne_top_unit H)]
    norm_num [s4SliceTVK_eq, s4UniversalC]
  calc
    _ ≤ 2 * sourceD S + 2 * sourceD S + 0 := by
      exact add_le_add (add_le_add
        (s4_initial_quotient_variation_le_sourceD H hr)
        (s4_initial_phi_variation_le_sourceD H hr)) (le_of_eq hlog)
    _ = 4 * sourceD S := by ring
    _ ≤ 100 * s4UniversalC * sourceD S := by
      gcongr
      norm_num [s4UniversalC]
    _ = _ := hK.symm

/-- Both complete three-term TV sums are bounded by one universal real
constant on every unit outgoing and incoming slice.  The outgoing statement
includes `u = 0`; the incoming logarithm uses `log (-ν)`. -/
theorem s4_three_term_slice_tv_unit {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S)
    (hD : sourceD S ≤ s4Epsilon0) (hZ : sourceZ S ≤ s4Epsilon0) :
    (∀ u ∈ Ico (0 : ℝ) 1,
      eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u 1) +
        eVariationOn (S.phi u) (Ioo u 1) +
        eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1) ≤
          ENNReal.ofReal (s4SliceTVK * (sourceD S).toReal)) ∧
    (∀ v ∈ Ioo (0 : ℝ) 1,
      eVariationOn (fun u => S.beta u v / S.nu u v) (Ioo 0 v) +
        eVariationOn (fun u => S.phi u v) (Ioo 0 v) +
        eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo 0 v) ≤
          ENNReal.ofReal (s4SliceTVK * (sourceD S).toReal)) := by
  obtain ⟨hOut, hIn⟩ :=
    s4_interior_three_term_slice_tv H hr hcenter hboot hD hZ
  constructor
  · intro u hu
    rcases eq_or_lt_of_le hu.1 with rfl | hu0
    · exact s4_initial_three_term_slice_tv H hr
    · exact hOut u ⟨hu0, hu.2⟩
  · exact hIn

end ChristodoulouBV

end
