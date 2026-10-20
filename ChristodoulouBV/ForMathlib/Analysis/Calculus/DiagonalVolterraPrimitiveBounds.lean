module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraPrimitiveJet
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Bounds for first-coordinate Volterra primitive jets

A uniform bound on a continuous horizontal kernel jet integrates with the
exact length of the Volterra interval. The same estimate applies to the
difference of two jets.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

private theorem abs_integral_le_const_mul_interval
    {w v A : ℝ} {g : ℝ → ℝ} (hwv : w ≤ v)
    (hg : ∀ s ∈ Icc w v, |g s| ≤ A) :
    |∫ s in w..v, g s| ≤ A * (v - w) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := w) (b := v) (C := A) (f := g) (by
      intro s hs
      have hs' : s ∈ Icc w v := by
        rw [uIoc_of_le hwv] at hs
        exact ⟨hs.1.le, hs.2⟩
      simpa only [Real.norm_eq_abs] using hg s hs')
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hwv)] using h

/-- The first-coordinate primitive jet is bounded by the kernel-jet bound
times the exact integration length. -/
theorem abs_verticalVolterraFirstJet_le_of_bounds
    {a b A u w v : ℝ}
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hG : ∀ p ∈ closedCoordTriangle a b, |G p (1, 0)| ≤ A)
    (hu : a ≤ u) (huw : u ≤ w) (hwv : w ≤ v) (hv : v ≤ b) :
    |verticalVolterraFirstJet G ((u, w), v)| ≤ A * (v - w) := by
  change |∫ s in w..v, G (u, s) (1, 0)| ≤ _
  apply abs_integral_le_const_mul_interval hwv
  intro s hs
  exact hG (u, s) ⟨hu, huw.trans hs.1, hs.2.trans hv⟩

/-- The difference of two first-coordinate primitive jets has the same
exact interval-length factor as the pointwise kernel-jet difference. -/
theorem abs_verticalVolterraFirstJet_sub_le_of_bounds
    {a b A D u w v : ℝ}
    {G₁ G₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hG₁ : ContinuousOn G₁ (closedCoordTriangle a b))
    (hG₂ : ContinuousOn G₂ (closedCoordTriangle a b))
    (hGdiff : ∀ p ∈ closedCoordTriangle a b,
      |G₁ p (1, 0) - G₂ p (1, 0)| ≤ A * D)
    (hu : a ≤ u) (huw : u ≤ w) (hwv : w ≤ v) (hv : v ≤ b) :
    |verticalVolterraFirstJet G₁ ((u, w), v) -
      verticalVolterraFirstJet G₂ ((u, w), v)| ≤
        A * (v - w) * D := by
  have hG₁i : IntervalIntegrable (fun s => G₁ (u, s) (1, 0)) volume w v := by
    apply ContinuousOn.intervalIntegrable_of_Icc hwv
    exact (hG₁.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hu, huw.trans hs.1, hs.2.trans hv⟩))
      |>.clm_apply continuousOn_const
  have hG₂i : IntervalIntegrable (fun s => G₂ (u, s) (1, 0)) volume w v := by
    apply ContinuousOn.intervalIntegrable_of_Icc hwv
    exact (hG₂.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hu, huw.trans hs.1, hs.2.trans hv⟩))
      |>.clm_apply continuousOn_const
  change |(∫ s in w..v, G₁ (u, s) (1, 0)) -
    (∫ s in w..v, G₂ (u, s) (1, 0))| ≤ _
  rw [← intervalIntegral.integral_sub hG₁i hG₂i]
  have h := abs_integral_le_const_mul_interval hwv (g := fun s =>
      G₁ (u, s) (1, 0) - G₂ (u, s) (1, 0)) (A := A * D) (by
    intro s hs
    exact hGdiff (u, s) ⟨hu, huw.trans hs.1, hs.2.trans hv⟩)
  nlinarith only [h]

/-- A linearly growing nonnegative kernel and a bounded horizontal jet give
all three Volterra-primitive coordinate bounds, including the exact
half-square value coefficient and the sharper `v-w` factor in the horizontal
jet. The second kernel is used only for the difference estimates. -/
theorem verticalVolterraPrimitive_jet_bounds_of_bounds
    {a b K₀ K₁ KΔ₀ KΔ₁ D u w v : ℝ}
    {k₁ k₂ : ℝ × ℝ → ℝ}
    {G₁ G₂ : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hk₁ : ContinuousOn k₁ (closedCoordTriangle a b))
    (hk₂ : ContinuousOn k₂ (closedCoordTriangle a b))
    (hG₁ : ContinuousOn G₁ (closedCoordTriangle a b))
    (hG₂ : ContinuousOn G₂ (closedCoordTriangle a b))
    (hK₀ : 0 ≤ K₀) (hKΔ₀ : 0 ≤ KΔ₀) (hD : 0 ≤ D)
    (hk₁bound : ∀ p ∈ closedCoordTriangle a b,
      0 ≤ k₁ p ∧ k₁ p ≤ K₀ * (p.2 - p.1))
    (hkdiff : ∀ p ∈ closedCoordTriangle a b,
      |k₁ p - k₂ p| ≤ KΔ₀ * (p.2 - p.1) * D)
    (hG₁bound : ∀ p ∈ closedCoordTriangle a b, |G₁ p (1, 0)| ≤ K₁)
    (hGdiff : ∀ p ∈ closedCoordTriangle a b,
      |G₁ p (1, 0) - G₂ p (1, 0)| ≤ KΔ₁ * D)
    (hu : a ≤ u) (huw : u ≤ w) (hwv : w ≤ v) (hv : v ≤ b) :
    (0 ≤ (∫ s in w..v, k₁ (u, s)) ∧
      (∫ s in w..v, k₁ (u, s)) ≤ K₀ * (v - u) ^ 2 / 2) ∧
    |(∫ s in w..v, k₁ (u, s)) -
      (∫ s in w..v, k₂ (u, s))| ≤ KΔ₀ * (v - u) ^ 2 * D / 2 ∧
    |verticalVolterraFirstJet G₁ ((u, w), v)| ≤ K₁ * (v - w) ∧
    |verticalVolterraFirstJet G₁ ((u, w), v) -
      verticalVolterraFirstJet G₂ ((u, w), v)| ≤ KΔ₁ * (v - w) * D ∧
    |k₁ (u, v)| ≤ K₀ * (v - u) ∧
    |k₁ (u, v) - k₂ (u, v)| ≤ KΔ₀ * (v - u) * D ∧
    |k₁ (u, w)| ≤ K₀ * (w - u) ∧
    |k₁ (u, w) - k₂ (u, w)| ≤ KΔ₀ * (w - u) * D := by
  have hseg : ∀ s ∈ Icc w v, (u, s) ∈ closedCoordTriangle a b := by
    intro s hs
    exact ⟨hu, huw.trans hs.1, hs.2.trans hv⟩
  have hi₁ : IntervalIntegrable (fun s => k₁ (u, s)) volume w v := by
    apply ContinuousOn.intervalIntegrable_of_Icc hwv
    exact hk₁.comp (continuous_const.prodMk continuous_id).continuousOn hseg
  have hi₂ : IntervalIntegrable (fun s => k₂ (u, s)) volume w v := by
    apply ContinuousOn.intervalIntegrable_of_Icc hwv
    exact hk₂.comp (continuous_const.prodMk continuous_id).continuousOn hseg
  have hqnonneg : 0 ≤ ∫ s in w..v, k₁ (u, s) :=
    intervalIntegral.integral_nonneg hwv (fun s hs => (hk₁bound _ (hseg s hs)).1)
  have hqabs : |∫ s in w..v, k₁ (u, s)| ≤ K₀ * (v - u) ^ 2 / 2 := by
    apply abs_integral_le_half_sq_of_abs_le_linear hwv hK₀ hi₁
    intro s hs
    have h := hk₁bound _ (hseg s hs)
    simpa only [abs_of_nonneg h.1] using h.2
  have hq : (∫ s in w..v, k₁ (u, s)) ≤ K₀ * (v - u) ^ 2 / 2 := by
    simpa only [abs_of_nonneg hqnonneg] using hqabs
  have hqdiff : |(∫ s in w..v, k₁ (u, s)) -
      (∫ s in w..v, k₂ (u, s))| ≤ KΔ₀ * (v - u) ^ 2 * D / 2 := by
    rw [← intervalIntegral.integral_sub hi₁ hi₂]
    have h := abs_integral_le_half_sq_of_abs_le_linear hwv
      (mul_nonneg hKΔ₀ hD) (hi₁.sub hi₂)
      (by
        intro s hs
        simpa only [Pi.sub_apply, mul_assoc, mul_comm, mul_left_comm] using
          hkdiff _ (hseg s hs))
    calc
      _ ≤ (KΔ₀ * D) * (v - u) ^ 2 / 2 := h
      _ = KΔ₀ * (v - u) ^ 2 * D / 2 := by ring
  have hGu := abs_verticalVolterraFirstJet_le_of_bounds
    hG₁bound hu huw hwv hv
  have hGudiff := abs_verticalVolterraFirstJet_sub_le_of_bounds
    hG₁ hG₂ hGdiff hu huw hwv hv
  have hpv : (u, v) ∈ closedCoordTriangle a b :=
    ⟨hu, huw.trans hwv, hv⟩
  have hpw : (u, w) ∈ closedCoordTriangle a b :=
    ⟨hu, huw, hwv.trans hv⟩
  refine ⟨⟨hqnonneg, hq⟩, hqdiff, hGu, hGudiff, ?_, ?_, ?_, ?_⟩
  · simpa only [abs_of_nonneg (hk₁bound _ hpv).1] using (hk₁bound _ hpv).2
  · exact hkdiff _ hpv
  · simpa only [abs_of_nonneg (hk₁bound _ hpw).1] using (hk₁bound _ hpw).2
  · exact hkdiff _ hpw

end intervalIntegral

end
