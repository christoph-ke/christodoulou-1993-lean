module

public import ChristodoulouBV.AreaEstimates.SmallDataFirstArea
public import ChristodoulouBV.AreaEstimates.LogTransportSlice
import ChristodoulouBV.Uniqueness.ExtensionStarTraceNu
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Regular-axis variation identities for the small-data estimates

The incoming traces are the negatives of the outgoing traces.  We also
compare variation of an expansion with variation of its logarithm on the
range supplied by the normalized gauge and bootstrap.
-/

public section

open Set
open scoped ENNReal

namespace ChristodoulouBV

/-- The two axis logarithms agree on the open unit axis. -/
theorem s4_axis_log_nu_variation_eq_lam {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    eVariationOn (fun t => Real.log (-S.nu t t)) (Ioo 0 1) =
      eVariationOn (fun t => Real.log (S.lam t t)) (Ioo 0 1) := by
  apply eVariationOn.congr
  intro t ht
  let B : ℝ := (t + 1) / 2
  have hB : 0 < B := by dsimp [B]; linarith only [ht.1]
  have hB1 : B < 1 := by dsimp [B]; linarith only [ht.2]
  have htB : t ≤ B := by dsimp [B]; linarith only [ht.2]
  have hnu := C1Solution.nu_eq_neg_lam_axis hB hB1 H
    (show t ∈ Icc (0 : ℝ) B from ⟨ht.1.le, htB⟩)
  change Real.log (-S.nu t t) = Real.log (S.lam t t)
  rw [hnu, neg_neg]

/-- The regular-axis `β` variation equals the `α` variation. -/
theorem s4_axis_beta_variation_eq_alpha {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    eVariationOn (fun t => S.beta t t) (Ioo 0 1) =
      eVariationOn (fun t => S.alpha t t) (Ioo 0 1) := by
  have htrace : EqOn (fun t => S.beta t t)
      (fun t => -S.alpha t t) (Ioo (0 : ℝ) 1) := by
    intro t ht
    let B : ℝ := (t + 1) / 2
    have hB : 0 < B := by dsimp [B]; linarith only [ht.1]
    have hB1 : B < 1 := by dsimp [B]; linarith only [ht.2]
    have htB : t ≤ B := by dsimp [B]; linarith only [ht.2]
    exact C1Solution.beta_eq_neg_alpha_axis hB hB1 H
      (show t ∈ Icc (0 : ℝ) B from ⟨ht.1.le, htB⟩)
  rw [eVariationOn.congr htrace]
  simp only [eVariationOn, edist_neg_neg]

/-- The regular-axis `ν` variation equals the `λ` variation. -/
theorem s4_axis_nu_variation_eq_lam {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S) :
    eVariationOn (fun t => S.nu t t) (Ioo 0 1) =
      eVariationOn (fun t => S.lam t t) (Ioo 0 1) := by
  have htrace : EqOn (fun t => S.nu t t)
      (fun t => -S.lam t t) (Ioo (0 : ℝ) 1) := by
    intro t ht
    let B : ℝ := (t + 1) / 2
    have hB : 0 < B := by dsimp [B]; linarith only [ht.1]
    have hB1 : B < 1 := by dsimp [B]; linarith only [ht.2]
    have htB : t ≤ B := by dsimp [B]; linarith only [ht.2]
    exact C1Solution.nu_eq_neg_lam_axis hB hB1 H
      (show t ∈ Icc (0 : ℝ) B from ⟨ht.1.le, htB⟩)
  rw [eVariationOn.congr htrace]
  simp only [eVariationOn, edist_neg_neg]

/-- The exponential is 1-Lipschitz on the nonpositive half-line. -/
private theorem exp_lipschitzOnWith_nonpos :
    LipschitzOnWith 1 Real.exp (Iic (0 : ℝ)) := by
  apply (convex_Iic (0 : ℝ)).lipschitzOnWith_of_nnnorm_deriv_le
  · intro x _
    exact Real.differentiableAt_exp
  · intro x hx
    rw [Real.deriv_exp]
    have he : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx
    exact_mod_cast (show ‖Real.exp x‖ ≤ (1 : ℝ) by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)] using he)

/-- On the regular axis the gauge bound `λ ≤ 1/2` allows its variation to be
controlled by variation of `log λ`. -/
theorem s4_axis_lam_variation_le_log {S : Fields}
    (H : IsC1Solution (developmentWithInitialEdge 1) S)
    (hr : ∀ v ∈ Ioo (0 : ℝ) 1, S.r 0 v = v / 2) :
    eVariationOn (fun t => S.lam t t) (Ioo 0 1) ≤
      eVariationOn (fun t => Real.log (S.lam t t)) (Ioo 0 1) := by
  have hpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < S.lam t t := by
    intro t ht
    let B : ℝ := (t + 1) / 2
    have hB : 0 < B := by dsimp [B]; linarith only [ht.1]
    have hB1 : B < 1 := by dsimp [B]; linarith only [ht.2]
    obtain ⟨c, hc, hcl⟩ := C1Solution.exists_lam_lower_bound hB hB1 H
    have htB : t ≤ B := by dsimp [B]; linarith only [ht.2]
    exact hc.trans_le (hcl (t, t) ⟨ht.1.le, le_rfl, htB⟩)
  have hmap : MapsTo (fun t => Real.log (S.lam t t))
      (Ioo (0 : ℝ) 1) (Iic 0) := by
    intro t ht
    let v : ℝ := (t + 1) / 2
    have htv : t < v := by dsimp [v]; linarith only [ht.2]
    have hv1 : v < 1 := by dsimp [v]; linarith only [ht.2]
    have hle : S.lam t t ≤ 1 :=
      (Uniqueness.lam_axis_le_half_of_initial_gauge H hr ht.1 htv hv1).trans
        (by norm_num)
    exact Real.log_nonpos (hpos t ht).le hle
  have h := exp_lipschitzOnWith_nonpos.comp_eVariationOn_le hmap
  have heq : EqOn (fun t => Real.exp (Real.log (S.lam t t)))
      (fun t => S.lam t t) (Ioo (0 : ℝ) 1) :=
    fun t ht => Real.exp_log (hpos t ht)
  calc
    eVariationOn (fun t => S.lam t t) (Ioo 0 1) =
        eVariationOn (fun t => Real.exp (Real.log (S.lam t t))) (Ioo 0 1) :=
      (eVariationOn.congr heq).symm
    _ ≤ eVariationOn (fun t => Real.log (S.lam t t)) (Ioo 0 1) := by
      simpa [Function.comp_def] using h

end ChristodoulouBV

end
