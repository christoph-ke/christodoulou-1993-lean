module

public import ChristodoulouBV.AreaEstimates.SmallDataLogVariation
import ChristodoulouBV.Uniqueness.ExtensionIncomingSigns
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Expansion variation from logarithmic variation

On the normalized unit triangle, `λ` and `|ν|` lie in `(0,1]`.  The
exponential is 1-Lipschitz on nonpositive reals, so logarithmic variation
controls ordinary variation on each null slice.
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

/-- A positive function bounded by one has variation no greater than the
variation of its logarithm. -/
theorem s4_variation_le_log_of_pos_le_one
    {ι : Type*} [LinearOrder ι] {f : ι → ℝ} {s : Set ι}
    (hpos : ∀ x ∈ s, 0 < f x) (hone : ∀ x ∈ s, f x ≤ 1) :
    eVariationOn f s ≤ eVariationOn (fun x => Real.log (f x)) s := by
  have hexp : LipschitzOnWith 1 Real.exp (Iic (0 : ℝ)) := by
    apply (convex_Iic (0 : ℝ)).lipschitzOnWith_of_nnnorm_deriv_le
    · intro x _
      exact Real.differentiableAt_exp
    · intro x hx
      rw [Real.deriv_exp]
      have he : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx
      exact_mod_cast (show ‖Real.exp x‖ ≤ (1 : ℝ) by
        simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)] using he)
  have hmap : MapsTo (fun x => Real.log (f x)) s (Iic 0) :=
    fun x hx => Real.log_nonpos (hpos x hx).le (hone x hx)
  have h := hexp.comp_eVariationOn_le hmap
  have heq : EqOn (fun x => Real.exp (Real.log (f x))) f s :=
    fun x hx => Real.exp_log (hpos x hx)
  calc
    eVariationOn f s =
        eVariationOn (fun x => Real.exp (Real.log (f x))) s :=
      (eVariationOn.congr heq).symm
    _ ≤ eVariationOn (fun x => Real.log (f x)) s := by
      simpa [Function.comp_def] using h

/-- Uniform outgoing variation of `λ` is bounded by uniform outgoing
variation of `log λ`. -/
theorem s4_outgoing_lam_variation_le_log {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2)
    (hboot : s4_bootstrap S) :
    (⨆ u ∈ Ioo (0 : ℝ) 1, eVariationOn (S.lam u) (Ioo u 1)) ≤
      (⨆ u ∈ Ioo (0 : ℝ) 1,
        eVariationOn (fun v => Real.log (S.lam u v)) (Ioo u 1)) := by
  apply iSup_le
  intro u
  apply iSup_le
  intro hu
  have hpos : ∀ v ∈ Ioo u 1, 0 < S.lam u v := by
    intro v hv
    have hp : (u, v) ∈ developmentWithInitialEdge 1 :=
      ⟨hu.1.le, hv.1, hv.2⟩
    exact (by norm_num : (0 : ℝ) < 1 / 3).trans_le (hboot.1 (u, v) hp)
  have hone : ∀ v ∈ Ioo u 1, S.lam u v ≤ 1 := by
    intro v hv
    exact (Uniqueness.lam_le_half_of_initial_gauge H hr hu.1.le hv.1 hv.2).trans
      (by norm_num)
  exact (s4_variation_le_log_of_pos_le_one hpos hone).trans
    (le_iSup_of_le u (le_iSup_of_le hu le_rfl))

/-- Uniform incoming variation of `ν` is bounded by uniform incoming
variation of `log|ν|`, with the sign of `ν` fixed by the bootstrap. -/
theorem s4_incoming_nu_variation_le_log {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hboot : s4_bootstrap S) :
    (⨆ v ∈ Ioo (0 : ℝ) 1,
      eVariationOn (fun u => S.nu u v) (Ioo 0 v)) ≤
      (⨆ v ∈ Ioo (0 : ℝ) 1,
        eVariationOn (fun u => Real.log (-S.nu u v)) (Ioo 0 v)) := by
  apply iSup_le
  intro v
  apply iSup_le
  intro hv
  have hpos : ∀ u ∈ Ioo (0 : ℝ) v, 0 < -S.nu u v := by
    intro u hu
    have hp : (u, v) ∈ openCoordTriangle 0 1 := ⟨hu.1, hu.2, hv.2⟩
    have hnu := sourceNu_le_neg_third H hboot hp
    linarith only [hnu]
  have hone : ∀ u ∈ Ioo (0 : ℝ) v, -S.nu u v ≤ 1 := by
    intro u hu
    have hp : (u, v) ∈ developmentWithInitialEdge 1 :=
      ⟨hu.1.le, hu.2, hv.2⟩
    have hnu := hboot.2.1 (u, v) hp
    linarith only [hnu]
  have hvar := s4_variation_le_log_of_pos_le_one hpos hone
  have hneg : eVariationOn (fun u => S.nu u v) (Ioo 0 v) =
      eVariationOn (fun u => -S.nu u v) (Ioo 0 v) := by
    simp only [eVariationOn, edist_neg_neg]
  rw [hneg]
  exact hvar.trans (le_iSup_of_le v (le_iSup_of_le hv le_rfl))

end ChristodoulouBV

end
