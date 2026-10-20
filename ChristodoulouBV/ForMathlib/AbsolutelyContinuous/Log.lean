module

public import ChristodoulouBV.ForMathlib.AbsolutelyContinuous.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Logarithms of positive absolutely continuous functions

A positive uniform gap makes the real logarithm Lipschitz on the image of a
compact interval. The resulting chain rule holds almost everywhere.
-/

public section

open Set MeasureTheory

namespace AbsolutelyContinuousOnInterval

/-- The logarithm of an absolutely continuous real function bounded below by
a positive constant is absolutely continuous, with the usual almost-everywhere
derivative. -/
theorem log_and_ae_deriv {g : ℝ → ℝ} {a b δ : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b) (hδ : 0 < δ)
    (hgap : ∀ x ∈ uIcc a b, δ ≤ g x) :
    AbsolutelyContinuousOnInterval (fun x => Real.log (g x)) a b ∧
      ∀ᵐ x ∂volume, x ∈ uIcc a b →
        deriv (fun t => Real.log (g t)) x = deriv g x / g x := by
  have hlog : LipschitzOnWith ⟨δ⁻¹, by positivity⟩ Real.log (Ici δ) := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro x hx y hy
    have hdiff : ∀ z ∈ Ici δ, DifferentiableAt ℝ Real.log z := by
      intro z hz
      exact Real.differentiableAt_log (ne_of_gt (hδ.trans_le hz))
    have hbound : ∀ z ∈ Ici δ, ‖deriv Real.log z‖ ≤ δ⁻¹ := by
      intro z hz
      rw [Real.deriv_log, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hδ.trans_le hz))]
      simpa only [one_div] using one_div_le_one_div_of_le hδ hz
    have hh := (convex_Ici δ).norm_image_sub_le_of_norm_deriv_le hdiff hbound hx hy
    calc
      dist (Real.log x) (Real.log y) ≤ δ⁻¹ * dist x y := by
        simpa [Real.dist_eq, Real.norm_eq_abs, abs_sub_comm] using hh
      _ = (⟨δ⁻¹, by positivity⟩ : NNReal) * dist x y := by
        simp
  have hcomp := hg.ae_deriv_comp_of_lipschitzOnWith hlog
    (fun x hx => hgap x hx) (fun x hx =>
      Real.differentiableAt_log (ne_of_gt (hδ.trans_le hx)))
  constructor
  · simpa only [Function.comp_def] using hcomp.1
  · filter_upwards [hcomp.2] with x hx hxu
    simpa only [Function.comp_def, Real.deriv_log, inv_mul_eq_div] using hx hxu

end AbsolutelyContinuousOnInterval

end
