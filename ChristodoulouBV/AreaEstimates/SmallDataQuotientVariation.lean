module

public import ChristodoulouBV.AreaEstimates.SmallDataFieldVariation
import all ChristodoulouBV.AreaEstimates.BasicEstimatesAmplitude
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Quotient variation on normalized null slices

The expansion floor gives a uniform Lipschitz bound for inversion.  This
turns the field and expansion variation estimates into the quotient
variations required by Lemma 4.1.
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

private theorem inverse_lipschitzOnWith_third :
    LipschitzOnWith 9 (fun x : ℝ => x⁻¹) (Ici (1 / 3 : ℝ)) := by
  apply (convex_Ici (1 / 3 : ℝ)).lipschitzOnWith_of_nnnorm_deriv_le
  · intro x hx
    have hxpos : 0 < x := (by norm_num : (0 : ℝ) < 1 / 3).trans_le hx
    exact differentiableAt_inv hxpos.ne'
  · intro x hx
    have hxpos : 0 < x := (by norm_num : (0 : ℝ) < 1 / 3).trans_le hx
    have hsq : (1 / 9 : ℝ) ≤ x ^ 2 := by
      nlinarith only [mul_self_le_mul_self
        (by norm_num : (0 : ℝ) ≤ 1 / 3) hx]
    have hsqpos : 0 < x ^ 2 := sq_pos_of_pos hxpos
    have hinv : (x ^ 2)⁻¹ ≤ (9 : ℝ) := by
      apply (inv_le_iff_one_le_mul₀' hsqpos).2
      nlinarith only [hsq]
    have hnorm : ‖deriv (fun y : ℝ => y⁻¹) x‖ ≤ (9 : ℝ) := by
      rw [deriv_inv, norm_neg, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hsqpos)]
      exact hinv
    exact_mod_cast hnorm

private theorem quotient_variation_le
    {ι : Type*} [LinearOrder ι] {s : Set ι}
    {f g : ι → ℝ} {M : ℝ≥0∞}
    (hf : ∀ x ∈ s, ‖f x‖ₑ ≤ M)
    (hg : ∀ x ∈ s, (1 / 3 : ℝ) ≤ g x) :
    eVariationOn (fun x => f x / g x) s ≤
      9 * M * eVariationOn g s + 3 * eVariationOn f s := by
  have hmap : MapsTo g s (Ici (1 / 3 : ℝ)) := hg
  have hinvVar := inverse_lipschitzOnWith_third.comp_eVariationOn_le hmap
  have hinvNorm : ∀ x ∈ s, ‖(g x)⁻¹‖ₑ ≤ (3 : ℝ≥0∞) := by
    intro x hx
    have hgpos : 0 < g x := (by norm_num : (0 : ℝ) < 1 / 3).trans_le (hg x hx)
    have hreal : |(g x)⁻¹| ≤ (3 : ℝ) := by
      rw [abs_of_pos (inv_pos.mpr hgpos)]
      apply (inv_le_iff_one_le_mul₀' hgpos).2
      nlinarith only [hg x hx]
    rw [Real.enorm_eq_ofReal_abs]
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hreal
  have hprod := eVariation_mul_le hf hinvNorm
  have hfun : (f * fun x => (g x)⁻¹) =
      (fun x => f x * (g x)⁻¹) := by
    funext x
    rfl
  rw [hfun] at hprod
  calc
    eVariationOn (fun x => f x / g x) s =
        eVariationOn (fun x => f x * (g x)⁻¹) s := by
      simp only [div_eq_mul_inv]
    _ ≤ M * eVariationOn (fun x => (g x)⁻¹) s +
          3 * eVariationOn f s := hprod
    _ ≤ M * (9 * eVariationOn g s) + 3 * eVariationOn f s := by
      have hmon : M * eVariationOn (fun x => (g x)⁻¹) s ≤
          M * (9 * eVariationOn g s) := by
        gcongr
        simpa [Function.comp_def] using hinvVar
      exact add_le_add_left hmon _
    _ = 9 * M * eVariationOn g s + 3 * eVariationOn f s := by ring

private theorem unit_abs_field_bddAbove {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle 0 1)) :
    BddAbove {x : ℝ | ∃ p ∈ developmentWithInitialEdge 1, x = |f p|} := by
  have hcont : ContinuousOn (fun p => |f p|) (closedCoordTriangle 0 1) :=
    continuous_abs.comp_continuousOn hf
  obtain ⟨M, hM⟩ :=
    ((isCompact_closedCoordTriangle 0 1).image_of_continuousOn hcont).bddAbove
  refine ⟨M, ?_⟩
  rintro x ⟨p, hp, rfl⟩
  apply hM
  exact ⟨p, ⟨hp.1, hp.2.1.le, hp.2.2.le⟩, rfl⟩

/-- The centered data variation bounds the norms of `α` and `β` on the
unit C¹ development. -/
theorem s4_alpha_beta_enorm_le_sourceD {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    (∀ p ∈ developmentWithInitialEdge 1,
      ‖S.alpha p.1 p.2‖ₑ ≤ 2 * sourceD S) ∧
      (∀ p ∈ developmentWithInitialEdge 1,
        ‖S.beta p.1 p.2‖ₑ ≤ 4 * sourceD S) := by
  obtain ⟨_, _, _, hAlpha, hBeta⟩ := unit_field_contDiffOn H
  have hAbdd := unit_abs_field_bddAbove hAlpha.continuousOn
  have hBbdd := unit_abs_field_bddAbove hBeta.continuousOn
  obtain ⟨hA, hB, _⟩ := lemma4_2 H hr hcenter hboot
  have hA' : sSup {x : ℝ | ∃ p ∈ developmentWithInitialEdge 1,
      x = |S.alpha p.1 p.2|} ≤ 2 * (sourceD S).toReal := by
    simpa only [sourceA] using hA
  have hB' : sSup {x : ℝ | ∃ p ∈ developmentWithInitialEdge 1,
      x = |S.beta p.1 p.2|} ≤ 4 * (sourceD S).toReal := by
    simpa only [sourceB] using hB
  have hDof : ENNReal.ofReal (sourceD S).toReal = sourceD S :=
    ENNReal.ofReal_toReal (sourceD_ne_top_unit H)
  constructor
  · intro p hp
    have hreal : |S.alpha p.1 p.2| ≤ 2 * (sourceD S).toReal :=
      (le_csSup hAbdd ⟨p, hp, rfl⟩).trans hA'
    rw [Real.enorm_eq_ofReal_abs]
    calc
      ENNReal.ofReal |S.alpha p.1 p.2| ≤
          ENNReal.ofReal (2 * (sourceD S).toReal) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = 2 * sourceD S := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), hDof]
        norm_num
  · intro p hp
    have hreal : |S.beta p.1 p.2| ≤ 4 * (sourceD S).toReal :=
      (le_csSup hBbdd ⟨p, hp, rfl⟩).trans hB'
    rw [Real.enorm_eq_ofReal_abs]
    calc
      ENNReal.ofReal |S.beta p.1 p.2| ≤
          ENNReal.ofReal (4 * (sourceD S).toReal) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = 4 * sourceD S := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), hDof]
        norm_num

/-- Uniform outgoing variation of `α/λ` from field and expansion variation. -/
theorem s4_outgoing_quotient_variation_le {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    (⨆ u ∈ Ioo (0 : ℝ) 1,
      eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u 1)) ≤
      18 * sourceD S *
        (⨆ u ∈ Ioo (0 : ℝ) 1,
          eVariationOn (S.lam u) (Ioo u 1)) +
      3 * (⨆ u ∈ Ioo (0 : ℝ) 1,
        eVariationOn (S.alpha u) (Ioo u 1)) := by
  have hAmp := (s4_alpha_beta_enorm_le_sourceD H hr hcenter hboot).1
  apply iSup_le
  intro u
  apply iSup_le
  intro hu
  have hNum : ∀ v ∈ Ioo u 1, ‖S.alpha u v‖ₑ ≤ 2 * sourceD S := by
    intro v hv
    exact hAmp (u, v) ⟨hu.1.le, hv.1, hv.2⟩
  have hDen : ∀ v ∈ Ioo u 1, (1 / 3 : ℝ) ≤ S.lam u v := by
    intro v hv
    exact hboot.1 (u, v) ⟨hu.1.le, hv.1, hv.2⟩
  have h := quotient_variation_le hNum hDen
  calc
    eVariationOn (fun v => S.alpha u v / S.lam u v) (Ioo u 1) ≤
        9 * (2 * sourceD S) * eVariationOn (S.lam u) (Ioo u 1) +
          3 * eVariationOn (S.alpha u) (Ioo u 1) := h
    _ = 18 * sourceD S * eVariationOn (S.lam u) (Ioo u 1) +
          3 * eVariationOn (S.alpha u) (Ioo u 1) := by ring
    _ ≤ 18 * sourceD S *
          (⨆ w ∈ Ioo (0 : ℝ) 1, eVariationOn (S.lam w) (Ioo w 1)) +
        3 * (⨆ w ∈ Ioo (0 : ℝ) 1,
          eVariationOn (S.alpha w) (Ioo w 1)) := by
      gcongr
      · exact le_iSup_of_le u (le_iSup_of_le hu le_rfl)
      · exact le_iSup_of_le u (le_iSup_of_le hu le_rfl)

/-- Uniform incoming variation of `β/ν` from field and expansion variation. -/
theorem s4_incoming_quotient_variation_le {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hcenter : S.phi 0 0 = 0) (hboot : s4_bootstrap S) :
    (⨆ v ∈ Ioo (0 : ℝ) 1,
      eVariationOn (fun u => S.beta u v / S.nu u v) (Ioo 0 v)) ≤
      36 * sourceD S *
        (⨆ v ∈ Ioo (0 : ℝ) 1,
          eVariationOn (fun u => S.nu u v) (Ioo 0 v)) +
      3 * (⨆ v ∈ Ioo (0 : ℝ) 1,
        eVariationOn (fun u => S.beta u v) (Ioo 0 v)) := by
  have hAmp := (s4_alpha_beta_enorm_le_sourceD H hr hcenter hboot).2
  apply iSup_le
  intro v
  apply iSup_le
  intro hv
  have hNum : ∀ u ∈ Ioo (0 : ℝ) v,
      ‖-S.beta u v‖ₑ ≤ 4 * sourceD S := by
    intro u hu
    simpa only [enorm_neg] using
      hAmp (u, v) ⟨hu.1.le, hu.2, hv.2⟩
  have hDen : ∀ u ∈ Ioo (0 : ℝ) v,
      (1 / 3 : ℝ) ≤ -S.nu u v := by
    intro u hu
    have hp : (u, v) ∈ openCoordTriangle 0 1 := ⟨hu.1, hu.2, hv.2⟩
    have h := sourceNu_le_neg_third H hboot hp
    linarith only [h]
  have h := quotient_variation_le hNum hDen
  have hNumVar : eVariationOn (fun u => -S.beta u v) (Ioo 0 v) =
      eVariationOn (fun u => S.beta u v) (Ioo 0 v) := by
    simp only [eVariationOn, edist_neg_neg]
  have hDenVar : eVariationOn (fun u => -S.nu u v) (Ioo 0 v) =
      eVariationOn (fun u => S.nu u v) (Ioo 0 v) := by
    simp only [eVariationOn, edist_neg_neg]
  have hQuot : eVariationOn (fun u => S.beta u v / S.nu u v) (Ioo 0 v) =
      eVariationOn (fun u => -S.beta u v / -S.nu u v) (Ioo 0 v) := by
    congr 1
    funext u
    simp only [neg_div_neg_eq]
  rw [hNumVar, hDenVar] at h
  calc
    eVariationOn (fun u => S.beta u v / S.nu u v) (Ioo 0 v) =
        eVariationOn (fun u => -S.beta u v / -S.nu u v) (Ioo 0 v) := hQuot
    _ ≤ 9 * (4 * sourceD S) *
          eVariationOn (fun u => S.nu u v) (Ioo 0 v) +
          3 * eVariationOn (fun u => S.beta u v) (Ioo 0 v) := h
    _ = 36 * sourceD S * eVariationOn (fun u => S.nu u v) (Ioo 0 v) +
          3 * eVariationOn (fun u => S.beta u v) (Ioo 0 v) := by ring
    _ ≤ 36 * sourceD S *
          (⨆ w ∈ Ioo (0 : ℝ) 1,
            eVariationOn (fun u => S.nu u w) (Ioo 0 w)) +
        3 * (⨆ w ∈ Ioo (0 : ℝ) 1,
          eVariationOn (fun u => S.beta u w) (Ioo 0 w)) := by
      gcongr
      · exact le_iSup_of_le v (le_iSup_of_le hv le_rfl)
      · exact le_iSup_of_le v (le_iSup_of_le hv le_rfl)

end ChristodoulouBV

end
