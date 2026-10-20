module

public import ChristodoulouBV.Existence.AreaSectionLimitCore
import Mathlib.Tactic

/-!
# Variation on moving section intervals

The physical endpoints move in the triangular area charts. To test
lower semicontinuity, a partition can be clamped to the new interval.
This keeps its interior physical points fixed near the limiting
parameter and avoids assuming continuity along every moving chart line.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem tendsto_ite_same {Y : Type*} {l : Filter Y}
    {f g : Y → ℝ} {r : ℝ} (hf : Tendsto f l (𝓝 r))
    (hg : Tendsto g l (𝓝 r)) (p : Y → Prop) [DecidablePred p] :
    Tendsto (fun y => if p y then f y else g y) l (𝓝 r) := by
  apply tendsto_def.mpr
  intro s hs
  filter_upwards [hf.eventually hs, hg.eventually hs] with y hyf hyg
  change (if p y then f y else g y) ∈ s
  split_ifs <;> assumption

private theorem continuousAt_clamped_section
    {Y : Type*} [TopologicalSpace Y] {G : Y → ℝ → ℝ} {a b : Y → ℝ} {y : Y}
    (ha : ContinuousAt a y) (hb : ContinuousAt b y) (hab : a y < b y)
    (hG : ∀ t ∈ Icc (a y) (b y), ContinuousAt (fun z => G z t) y)
    (hGa : ContinuousAt (fun z => G z (a z)) y)
    (hGb : ContinuousAt (fun z => G z (b z)) y)
    {t : ℝ} (ht : t ∈ Icc (a y) (b y)) :
    ContinuousAt (fun z => G z (max (a z) (min (b z) t))) y := by
  classical
  have hvalue : max (a y) (min (b y) t) = t :=
    max_eq_right (le_min hab.le ht.1) |>.trans (min_eq_right ht.2)
  rw [ContinuousAt, hvalue]
  rcases ht.1.eq_or_lt with hat | hat
  · have hnear : ∀ᶠ z in 𝓝 y, t < b z :=
      hb.eventually (Ioi_mem_nhds (hat ▸ hab))
    have hlim := tendsto_ite_same
      (show Tendsto (fun z => G z (a z)) (𝓝 y) (𝓝 (G y t)) by rw [← hat]; exact hGa)
      (hG t ht) (fun z => t < a z)
    apply hlim.congr'
    filter_upwards [hnear] with z hz
    rw [min_eq_right hz.le]
    by_cases hza : t < a z
    · simp only [hza, ite_true, max_eq_left hza.le]
    · simp only [hza, ite_false, max_eq_right (le_of_not_gt hza)]
  · rcases ht.2.eq_or_lt with htb | htb
    · have hnear : ∀ᶠ z in 𝓝 y, a z < t :=
        ha.eventually (Iio_mem_nhds (by simpa only [htb] using hab))
      have hlim := tendsto_ite_same
        (show Tendsto (fun z => G z (b z)) (𝓝 y) (𝓝 (G y t)) by
          rw [htb]; exact hGb)
        (hG t ht) (fun z => b z < t)
      apply hlim.congr'
      filter_upwards [hnear, ha.eventually_lt hb hab] with z hz habz
      by_cases hzb : b z < t
      · simp only [hzb, ite_true, min_eq_left hzb.le, max_eq_right habz.le]
      · simp only [hzb, ite_false, min_eq_right (le_of_not_gt hzb), max_eq_right hz.le]
    · apply (hG t ht).congr'
      filter_upwards [ha.eventually (Iio_mem_nhds hat), hb.eventually (Ioi_mem_nhds htb)]
        with z hza hzb
      rw [min_eq_right hzb.le, max_eq_right hza.le]

/-- Constant extension to a moving interval is pointwise continuous in
the parameter when its fixed physical evaluations and endpoint values
are continuous. The evaluation point may lie outside the interval. -/
theorem continuousAt_constant_extension_moving_interval
    {Y : Type*} [TopologicalSpace Y] {G : Y → ℝ → ℝ} {a b : Y → ℝ} {y : Y}
    (ha : ContinuousAt a y) (hb : ContinuousAt b y) (hab : ∀ z, a z < b z)
    (hG : ∀ t ∈ Icc (a y) (b y), ContinuousAt (fun z => G z t) y)
    (hGa : ContinuousAt (fun z => G z (a z)) y)
    (hGb : ContinuousAt (fun z => G z (b z)) y) (t : ℝ) :
    ContinuousAt (fun z => G z (max (a z) (min (b z) t))) y := by
  by_cases hta : t < a y
  · change Tendsto _ (𝓝 y) (𝓝 (G y (max (a y) (min (b y) t))))
    rw [max_eq_left ((min_le_right _ _).trans hta.le)]
    apply hGa.congr'
    filter_upwards [ha.eventually (Ioi_mem_nhds hta)] with z hz
    rw [max_eq_left ((min_le_right _ _).trans hz.le)]
  by_cases hbt : b y < t
  · change Tendsto _ (𝓝 y) (𝓝 (G y (max (a y) (min (b y) t))))
    rw [min_eq_left hbt.le, max_eq_right (hab y).le]
    apply hGb.congr'
    filter_upwards [hb.eventually (Iio_mem_nhds hbt)] with z hz
    rw [min_eq_left hz.le, max_eq_right (hab z).le]
  exact continuousAt_clamped_section ha hb (hab y) hG hGa hGb
    ⟨le_of_not_gt hta, le_of_not_gt hbt⟩

/-- Variation on a moving compact interval is lower semicontinuous at a
parameter where all fixed physical evaluations and the two endpoint
evaluations are continuous. Interior partition points need not move
with the triangular coordinate chart. -/
theorem lowerSemicontinuousAt_variation_moving_interval
    {Y : Type*} [TopologicalSpace Y] {G : Y → ℝ → ℝ} {a b : Y → ℝ} {y : Y}
    (ha : ContinuousAt a y) (hb : ContinuousAt b y)
    (hab : ∀ z, a z < b z)
    (hG : ∀ t ∈ Icc (a y) (b y), ContinuousAt (fun z => G z t) y)
    (hGa : ContinuousAt (fun z => G z (a z)) y)
    (hGb : ContinuousAt (fun z => G z (b z)) y) :
    LowerSemicontinuousAt (fun z => eVariationOn (G z) (Icc (a z) (b z))) y := by
  let H := fun z t => G z (max (a z) (min (b z) t))
  have hc : ∀ t ∈ Icc (a y) (b y), ContinuousAt (fun z => H z t) y :=
    fun _ ht => continuousAt_clamped_section ha hb (hab y) hG hGa hGb ht
  have heq : eVariationOn (H y) (Icc (a y) (b y)) =
      eVariationOn (G y) (Icc (a y) (b y)) := by
    apply eVariationOn.congr
    intro t ht
    simp only [H, min_eq_right ht.2, max_eq_right ht.1]
  have hle (z : Y) : eVariationOn (H z) (Icc (a y) (b y)) ≤
      eVariationOn (G z) (Icc (a z) (b z)) :=
    eVariationOn.comp_le_of_monotoneOn (G z) (fun t => max (a z) (min (b z) t))
      (fun _ _ _ _ hst => max_le_max_left _ (min_le_min_left _ hst))
      (fun t _ => ⟨le_max_left _ _, max_le (hab z).le (min_le_left _ _)⟩)
  intro r hr
  change r < eVariationOn (G y) (Icc (a y) (b y)) at hr
  rw [← heq] at hr
  filter_upwards [eVariationOn.lowerSemicontinuous_aux hc hr] with z hz
  exact hz.trans_le (hle z)

end ChristodoulouBV

end
