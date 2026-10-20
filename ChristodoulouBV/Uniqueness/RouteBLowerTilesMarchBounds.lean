module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesFirst
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# Quantitative outgoing-edge bounds for Route B tiles

The rectangle solver bounds its outgoing vector field throughout a safe box.
Consequently the next tile's incoming edge stays close to the terminal base
for a uniformly short height.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- On a safe characteristic rectangle, the outgoing state changes by at
most the safe-box vector-field bound times the vertical distance. -/
theorem outgoing_norm_sub_base_le_of_safe_rectangle
    {u₀ u₁ vStar h : ℝ}
    (B : C1Solution.SafeRectangleBox)
    (y₀ : ℝ → C1Solution.OutgoingState)
    (X : ℝ × ℝ → C1Solution.IncomingState)
    (Y : ℝ × ℝ → C1Solution.OutgoingState)
    (hX : Continuous X) (hY : Continuous Y)
    (hball : ∀ p ∈ Goursat.rectangle u₀ u₁ vStar (vStar + h),
      (X p, Y p) ∈ B.carrier)
    (heq : ∀ p ∈ Goursat.rectangle u₀ u₁ vStar (vStar + h),
      Y p = y₀ p.1 + ∫ t in vStar..p.2,
        C1Solution.rectangleG (X (p.1, t), Y (p.1, t)))
    {u v : ℝ} (hu : u ∈ Icc u₀ u₁)
    (hv : v ∈ Icc vStar (vStar + h)) :
    ‖Y (u, v) - y₀ u‖ ≤ B.valueBound * (v - vStar) := by
  let f : ℝ → C1Solution.OutgoingState :=
    fun t => C1Solution.rectangleG (X (u, t), Y (u, t))
  have hf : ContinuousOn f (Icc vStar v) := by
    intro t ht
    have htv : t ∈ Icc vStar (vStar + h) :=
      ⟨ht.1, ht.2.trans hv.2⟩
    have hz := B.safe (hball (u, t)
      (Goursat.pair_mem_rectangle hu htv))
    have hpath : ContinuousAt (fun s : ℝ => (X (u, s), Y (u, s))) t :=
      ((hX.comp (continuous_const.prodMk continuous_id)).prodMk
        (hY.comp (continuous_const.prodMk continuous_id))).continuousAt
    have hcont : ContinuousAt f t :=
      ContinuousAt.comp' (f := fun s : ℝ => (X (u, s), Y (u, s)))
        (C1Solution.contDiffAt_rectangleG hz).continuousAt hpath
    exact hcont.continuousWithinAt
  have hint : IntervalIntegrable f MeasureTheory.volume vStar v :=
    (show ContinuousOn f (uIcc vStar v) by
      simpa only [uIcc_of_le hv.1] using hf).intervalIntegrable
  have hbound : ∀ t ∈ Set.uIoc vStar v, ‖f t‖ ≤ B.valueBound := by
    intro t ht
    have ht' : t ∈ Icc vStar v := by
      simpa only [uIcc_of_le hv.1] using (uIoc_subset_uIcc ht)
    have htv : t ∈ Icc vStar (vStar + h) :=
      ⟨ht'.1, ht'.2.trans hv.2⟩
    exact B.norm_rectangleG_le (hball (u, t)
      (Goursat.pair_mem_rectangle hu htv))
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := vStar) (b := v) (C := B.valueBound) (f := f) hbound
  have he := heq (u, v) (Goursat.pair_mem_rectangle hu hv)
  rw [he, add_sub_cancel_left]
  simpa only [abs_of_nonneg (sub_nonneg.mpr hv.1)] using hnorm

/-- A fixed short base interval and any continuous incoming trace matching
its left corner admit a positive height whose entire mixed trace has a
uniform safe-box margin. The height may be reduced after earlier tiles have
been constructed. -/
theorem exists_height_mixed_trace_margin
    {u₀ u₁ vStar H : ℝ} (hH : 0 < H)
    (B : C1Solution.SafeRectangleBox)
    (base : ℝ → C1Solution.RectangleState)
    (x₀ : ℝ → C1Solution.IncomingState)
    (hcenter : B.center = base u₀)
    (hcorner : x₀ vStar = (base u₀).1)
    (hx₀ : ContinuousAt x₀ vStar)
    (hbase : ∀ u ∈ Icc u₀ u₁,
      dist (base u) (base u₀) ≤ B.radius / 4) :
    ∃ η : ℝ, 0 < η ∧ η < H ∧
      ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc vStar (vStar + η),
        dist (x₀ v, (base u).2) B.center ≤ B.radius / 2 := by
  have hquarter : 0 < B.radius / 4 := by
    exact div_pos B.radius_pos (by norm_num)
  obtain ⟨δ, hδ, hnear⟩ :=
    (Metric.continuousAt_iff.mp hx₀) (B.radius / 4) hquarter
  let η := min (H / 2) (δ / 2)
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min (by linarith only [hH]) (by linarith only [hδ])
  have hηH : η < H := by
    have := min_le_left (H / 2) (δ / 2)
    dsimp [η]
    linarith only [this, hH]
  have hηδ : η ≤ δ / 2 := min_le_right _ _
  refine ⟨η, hη, hηH, ?_⟩
  intro u hu v hv
  have hdist : dist v vStar < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hv.1)]
    linarith only [hv.2, hηδ, hδ]
  have hx : dist (x₀ v) (base u₀).1 ≤ B.radius / 4 := by
    rw [← hcorner]
    exact (hnear hdist).le
  have hy : dist (base u).2 (base u₀).2 ≤ B.radius / 4 := by
    have hproj : dist (base u).2 (base u₀).2 ≤
        dist (base u) (base u₀) := by
      simpa only [dist_eq_norm, Prod.snd_sub] using
        (norm_snd_le ((base u) - (base u₀)))
    exact hproj.trans (hbase u hu)
  rw [hcenter, Prod.dist_eq]
  exact (max_le hx hy).trans (by linarith only [B.radius_pos])

end ChristodoulouBV.Uniqueness

end
