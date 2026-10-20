module

public import ChristodoulouBV.Existence.BVStieltjesLogResidual
public import ChristodoulouBV.Existence.BVStieltjesLogFlux
public import ChristodoulouBV.Existence.BVStieltjesRectangle
import Mathlib.Tactic

/-!
# Logarithmic rectangle identities

The scalar product and square-flux primitives allow Fubini to be applied
only to ordinary integrable densities. The BV quotient remains in its
pointwise endpoint product, preserving its jumps.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Integrating the logarithmic transverse primitive and its square-flux
identity gives the rectangular identity with the Stieltjes endpoint product. -/
theorem stieltjes_log_rectangle_increment
    {U K W V Q H : ℝ → ℝ → ℝ} {a b x y : ℝ} (hab : a ≤ b) (hxy : x ≤ y)
    (hU₁ : U b x - U a x = ∫ w in a..b, K w x)
    (hU₂ : U b y - U a y = ∫ w in a..b, K w y)
    (hK : ∀ w ∈ Icc a b, K w y - K w x = ∫ t in x..y, H w t)
    (hW : ∀ t ∈ Icc x y, W b t - W a t = ∫ w in a..b, Q w t - H w t)
    (hK₁ : IntervalIntegrable (fun w => K w x) volume a b)
    (hK₂ : IntervalIntegrable (fun w => K w y) volume a b)
    (hW₁ : IntervalIntegrable (W a) volume x y)
    (hW₂ : IntervalIntegrable (W b) volume x y)
    (hV₁ : IntervalIntegrable (V a) volume x y)
    (hV₂ : IntervalIntegrable (V b) volume x y)
    (hQ : Integrable (fun p : ℝ × ℝ => Q p.1 p.2)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc x y))))
    (hH : Integrable (fun p : ℝ × ℝ => H p.1 p.2)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc x y)))) :
    (U b y - U b x + ∫ t in x..y, W b t - V b t) -
      (U a y - U a x + ∫ t in x..y, W a t - V a t) =
        -(∫ t in x..y, V b t - V a t - ∫ w in a..b, Q w t) := by
  have hKH : (∫ w in a..b, K w y) - (∫ w in a..b, K w x) =
      ∫ t in x..y, ∫ w in a..b, H w t := by
    rw [← intervalIntegral.integral_sub hK₂ hK₁]
    calc
      _ = ∫ w in a..b, ∫ t in x..y, H w t := by
        apply intervalIntegral.integral_congr
        intro w hw
        exact hK w (by simpa only [uIcc_of_le hab] using hw)
      _ = _ := by
        simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hxy]
        exact integral_integral_swap hH
  have hQi : IntervalIntegrable (fun t => ∫ w in a..b, Q w t) volume x y := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hxy]
    simpa only [intervalIntegral.integral_of_le hab, Function.uncurry, IntegrableOn]
      using hQ.integral_prod_right
  have hHi : IntervalIntegrable (fun t => ∫ w in a..b, H w t) volume x y := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hxy]
    simpa only [intervalIntegral.integral_of_le hab, Function.uncurry, IntegrableOn]
      using hH.integral_prod_right
  have hWQ : (∫ t in x..y, W b t) - (∫ t in x..y, W a t) =
      (∫ t in x..y, ∫ w in a..b, Q w t) -
        ∫ t in x..y, ∫ w in a..b, H w t := by
    rw [← intervalIntegral.integral_sub hW₂ hW₁,
      ← intervalIntegral.integral_sub hQi hHi]
    rw [intervalIntegral.integral_of_le hxy, intervalIntegral.integral_of_le hxy]
    apply integral_congr_ae
    filter_upwards [hQ.prod_left_ae, hH.prod_left_ae,
      ae_restrict_mem measurableSet_Ioc] with t hQt hHt ht
    rw [hW t (Ioc_subset_Icc_self ht), intervalIntegral.integral_sub
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hQt)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hHt)]
  rw [intervalIntegral.integral_sub hW₂ hV₂,
    intervalIntegral.integral_sub hW₁ hV₁,
    intervalIntegral.integral_sub (hV₂.sub hV₁) hQi,
    intervalIntegral.integral_sub hV₂ hV₁]
  linarith only [hU₁, hU₂, hKH, hWQ]

end ChristodoulouBV

end
