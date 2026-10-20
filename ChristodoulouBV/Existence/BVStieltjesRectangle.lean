module

public import ChristodoulouBV.Existence.BVStieltjesRepresentatives
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Rectangular integration of scalar transport primitives

This calculation keeps the Stieltjes variable in the endpoint increments.
Fubini is used only on the ordinary, locally bounded correction density.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Integrating the two transverse primitives gives the rectangular
Stieltjes increment identity. There is no longitudinal differentiability
assumption on `U` or `G`. -/
theorem stieltjes_rectangle_increment
    {U G H Q : ℝ → ℝ → ℝ} {v b x₁ x₂ : ℝ}
    (hvb : v ≤ b) (hxx : x₁ ≤ x₂)
    (hU₁ : U b x₁ - U v x₁ = -(∫ w in v..b, G w x₁))
    (hU₂ : U b x₂ - U v x₂ = -(∫ w in v..b, G w x₂))
    (hH : ∀ x ∈ Icc x₁ x₂, H b x - H v x = ∫ w in v..b, Q w x)
    (hG₁ : IntervalIntegrable (fun w => G w x₁) volume v b)
    (hG₂ : IntervalIntegrable (fun w => G w x₂) volume v b)
    (hHv : IntervalIntegrable (H v) volume x₁ x₂)
    (hHb : IntervalIntegrable (H b) volume x₁ x₂)
    (hQ : Integrable (fun p : ℝ × ℝ => Q p.1 p.2)
      ((volume.restrict (Ioc v b)).prod (volume.restrict (Ioc x₁ x₂)))) :
    (U v x₂ - U v x₁ + ∫ x in x₁..x₂, H v x) -
        (U b x₂ - U b x₁ + ∫ x in x₁..x₂, H b x) =
      ∫ w in v..b, G w x₂ - G w x₁ - ∫ x in x₁..x₂, Q w x := by
  have hswap : (∫ x in x₁..x₂, ∫ w in v..b, Q w x) =
      ∫ w in v..b, ∫ x in x₁..x₂, Q w x := by
    simp_rw [intervalIntegral.integral_of_le hvb, intervalIntegral.integral_of_le hxx]
    exact (integral_integral_swap hQ).symm
  have hQi : IntervalIntegrable (fun w => ∫ x in x₁..x₂, Q w x) volume v b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hvb]
    simpa only [intervalIntegral.integral_of_le hxx, Function.uncurry, IntegrableOn]
      using hQ.integral_prod_left
  have hHi : (∫ x in x₁..x₂, H b x) - (∫ x in x₁..x₂, H v x) =
      ∫ w in v..b, ∫ x in x₁..x₂, Q w x := by
    rw [← intervalIntegral.integral_sub hHb hHv]
    calc
      _ = ∫ x in x₁..x₂, ∫ w in v..b, Q w x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hH x (by simpa only [uIcc_of_le hxx] using hx)
      _ = _ := hswap
  rw [intervalIntegral.integral_sub (hG₂.sub hG₁) hQi,
    intervalIntegral.integral_sub hG₂ hG₁]
  linarith only [hU₁, hU₂, hHi]

/-- Integrating Stieltjes increments and summing a monotone partition
gives the transport inequality for total variation. Only the ordinary
increment integrands need to be measurable. -/
theorem stieltjes_variation_transport
    {Y α : Type*} [MeasurableSpace Y] [LinearOrder α] {μ : Measure Y}
    {f g : α → ℝ} {P : Y → α → ℝ} {s : Set α}
    (hP : ∀ x ∈ s, ∀ y ∈ s,
      AEStronglyMeasurable (fun z => P z y - P z x) μ)
    (hfg : ∀ x ∈ s, ∀ y ∈ s, x ≤ y →
      (f y - f x) - (g y - g x) = ∫ z, P z y - P z x ∂μ) :
    eVariationOn f s ≤ eVariationOn g s + ∫⁻ z, eVariationOn (P z) s ∂μ := by
  apply iSup_le
  rintro ⟨n, u, hu, hs⟩
  have hterm (i : ℕ) : edist (f (u (i + 1))) (f (u i)) ≤
      edist (g (u (i + 1))) (g (u i)) +
        ∫⁻ z, edist (P z (u (i + 1))) (P z (u i)) ∂μ := by
    have he : f (u (i + 1)) - f (u i) =
        (g (u (i + 1)) - g (u i)) +
          ∫ z, P z (u (i + 1)) - P z (u i) ∂μ := by
      linarith only [hfg _ (hs _) _ (hs _) (hu (Nat.le_succ i))]
    simp only [edist_eq_enorm_sub]
    rw [he]
    exact (enorm_add_le _ _).trans
      (add_le_add le_rfl (enorm_integral_le_lintegral_enorm _))
  calc
    _ ≤ ∑ i ∈ Finset.range n, (edist (g (u (i + 1))) (g (u i)) +
        ∫⁻ z, edist (P z (u (i + 1))) (P z (u i)) ∂μ) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i))) +
        ∫⁻ z, ∑ i ∈ Finset.range n,
          edist (P z (u (i + 1))) (P z (u i)) ∂μ := by
      rw [Finset.sum_add_distrib]
      congr 1
      symm
      apply lintegral_finsetSum'
      intro i _
      simpa only [edist_eq_enorm_sub] using (hP _ (hs _) _ (hs _)).enorm
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu hs)
      (lintegral_mono fun z => eVariationOn.sum_le hu hs)

end ChristodoulouBV

end
