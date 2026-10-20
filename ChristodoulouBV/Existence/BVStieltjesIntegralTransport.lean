module

public import ChristodoulouBV.Existence.BVStieltjesRectangle
public import ChristodoulouBV.ForMathlib.BoundedVariation.AbsolutelyContinuous
import Mathlib.Tactic

/-!
# Variation transport from ordinary integral increments

The logarithmic rectangles integrate in the variation coordinate.
Compact interior sections suffice, so no endpoint integrability is
assumed when bounding the variation on an open interval.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Local integral increments control open-interval variation by a
majorant lower integral. Every jump remains in the endpoint increments. -/
theorem stieltjes_variation_transport_integral
    {f g q : ℝ → ℝ} {K : ℝ → ℝ≥0∞} {A B : ℝ}
    (hq : ∀ x ∈ Ioo A B, ∀ y ∈ Ioo A B, x ≤ y → IntervalIntegrable q volume x y)
    (hfg : ∀ x ∈ Ioo A B, ∀ y ∈ Ioo A B, x ≤ y →
      (f y - f x) - (g y - g x) = ∫ t in x..y, q t)
    (hbound : ∀ᵐ t ∂volume, t ∈ Ioo A B → ENNReal.ofReal |q t| ≤ K t) :
    eVariationOn f (Ioo A B) ≤ eVariationOn g (Ioo A B) + ∫⁻ t in Ioo A B, K t := by
  rw [eVariationOn.eq_biSup_inter_Icc]
  simp only [iSup_le_iff, mem_ofPred_eq, Prod.forall, and_imp]
  intro x y hx hy hxy
  have hs : Icc x y ⊆ Ioo A B := fun _ ht => ⟨hx.1.trans_le ht.1, ht.2.trans_lt hy.2⟩
  rw [inter_eq_right.mpr hs]
  let F := fun t => f t - g t
  have heq : EqOn f (g + F) (Icc x y) := by
    intro t _
    dsimp only [Pi.add_apply, F]
    ring
  rw [eVariationOn.eq_of_eqOn heq]
  have hqi := hq x hx y hy hxy
  have hev : eVariationOn F (Icc x y) = ENNReal.ofReal (∫ t in x..y, |q t|) := by
    apply hqi.eVariationOn_eq_integral_abs hxy
    intro t ht
    have hi := hfg x hx t (hs ht) ht.1
    dsimp only [F]
    linarith only [hi]
  refine (eVariationOn.add_le g F (Icc x y)).trans (add_le_add
    (eVariationOn.mono _ hs) ?_)
  rw [hev, intervalIntegral.integral_of_le hxy,
    ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hxy).mp hqi.abs)
      (Eventually.of_forall fun _ => abs_nonneg _)]
  calc
    (∫⁻ t in Ioc x y, ENNReal.ofReal |q t|) ≤ ∫⁻ t in Ioc x y, K t := by
      apply lintegral_mono_ae
      filter_upwards [hbound.filter_mono (ae_mono Measure.restrict_le_self),
        ae_restrict_mem measurableSet_Ioc] with t ht htI
      exact ht (hs (Ioc_subset_Icc_self htI))
    _ ≤ _ := lintegral_mono_set (Ioc_subset_Icc_self.trans hs)

end ChristodoulouBV

end
