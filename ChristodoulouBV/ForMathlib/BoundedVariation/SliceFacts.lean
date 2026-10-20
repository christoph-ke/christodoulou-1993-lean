module

public import ChristodoulouBV.ForMathlib.BoundedVariation.Representatives
public import ChristodoulouBV.ForMathlib.BoundedVariation.Algebra
public import Mathlib.Analysis.BoundedVariation

/-!
# Elementary facts about bounded-variation slices

These statements use the values of a function as given. No right-continuous
representative is chosen.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace BoundedVariationOn

/-- Finite variation bounds the oscillation between two points of the carrier. -/
theorem abs_sub_le_variation {f : ℝ → ℝ} {s : Set ℝ}
    (hf : BoundedVariationOn f s) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    |f x - f y| ≤ (eVariationOn f s).toReal := by
  simpa only [Real.dist_eq] using hf.dist_le hx hy

/-- A real function of bounded variation on any carrier has a uniform absolute bound there. -/
theorem exists_bound_on {f : ℝ → ℝ} {s : Set ℝ}
    (hf : BoundedVariationOn f s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ s, |f x| ≤ C := by
  by_cases hs : s.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hs
    refine ⟨|f x₀| + (eVariationOn f s).toReal, by positivity, ?_⟩
    intro x hx
    have h := hf.abs_sub_le_variation hx hx₀
    calc
      |f x| = |(f x - f x₀) + f x₀| := by rw [sub_add_cancel]
      _ ≤ |f x - f x₀| + |f x₀| := abs_add_le _ _
      _ ≤ |f x₀| + (eVariationOn f s).toReal := by linarith
  · refine ⟨0, le_rfl, ?_⟩
    intro x hx
    exact (hs ⟨x, hx⟩).elim

/-- A BV slice has a left limit within its carrier at every point. At a point
where the carrier accumulates on the left, the filter is nontrivial. -/
theorem exists_left_limit_within {f : ℝ → ℝ} {s : Set ℝ}
    (hf : BoundedVariationOn f s) (x : ℝ)
    (_hx : x ∈ closure (s ∩ Iio x)) :
    ∃ l : ℝ, Tendsto f (𝓝[s ∩ Iio x] x) (𝓝 l) :=
  hf.exists_tendsto_left x

/-- A BV slice has a right limit within its carrier at every point. -/
theorem exists_right_limit_within {f : ℝ → ℝ} {s : Set ℝ}
    (hf : BoundedVariationOn f s) (x : ℝ)
    (_hx : x ∈ closure (s ∩ Ioi x)) :
    ∃ l : ℝ, Tendsto f (𝓝[s ∩ Ioi x] x) (𝓝 l) :=
  hf.exists_tendsto_right x

/-- A BV function is measurable after restriction to any closed interval
contained in its carrier. Values outside the interval are set to zero. -/
theorem measurable_indicator_uIcc {f : ℝ → ℝ} {s : Set ℝ}
    (hf : BoundedVariationOn f s) {a b : ℝ}
    (hab : uIcc a b ⊆ s) : Measurable ((uIcc a b).indicator f) := by
  let φ : ℝ → ℝ := fun x => (a ⊓ b) ⊔ ((a ⊔ b) ⊓ x)
  have hφ : Monotone φ := fun _ _ h =>
    sup_le_sup_left (inf_le_inf_left _ h) _
  have hmaps : MapsTo φ univ (uIcc a b) := fun _ _ =>
    ⟨le_sup_left, sup_le inf_le_sup inf_le_left⟩
  have heq : EqOn (f ∘ φ) f (uIcc a b) := by
    intro x hx
    dsimp [φ, Function.comp_def]
    rw [inf_eq_right.mpr hx.2, sup_eq_right.mpr hx.1]
  have hBV : BoundedVariationOn (f ∘ φ) univ :=
    ne_top_of_le_ne_top (hf.mono hab)
      (eVariationOn.comp_le_of_monotoneOn f φ (hφ.monotoneOn univ) hmaps)
  have hEq : (uIcc a b).indicator (f ∘ φ) = (uIcc a b).indicator f := by
    funext x
    by_cases hx : x ∈ uIcc a b
    · simp only [Set.indicator_of_mem hx, heq hx]
    · simp [Set.indicator, hx]
  rw [← hEq]
  exact hBV.measurable.indicator measurableSet_uIcc

/-- On every contained closed interval, a BV slice is strongly measurable
almost everywhere for the restricted Lebesgue measure. -/
theorem aestronglyMeasurable_restrict_uIcc {f : ℝ → ℝ} {s : Set ℝ}
    (hf : BoundedVariationOn f s) {a b : ℝ}
    (hab : uIcc a b ⊆ s) :
    AEStronglyMeasurable f (volume.restrict (uIcc a b)) := by
  rcases le_total a b with h | h
  · rw [uIcc_of_le h]
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le h).mp
      (hf.intervalIntegrable (μ := volume) hab)).aestronglyMeasurable
  · rw [uIcc_comm, uIcc_of_le h]
    have hab' : uIcc b a ⊆ s := by simpa only [uIcc_comm] using hab
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le h).mp
      (hf.intervalIntegrable (μ := volume) hab')).aestronglyMeasurable

/-- A BV function on a half-open interval is measurable there, with zero
extension outside the interval. -/
theorem measurable_indicator_Ioc {f : ℝ → ℝ} {s : Set ℝ}
    (hf : BoundedVariationOn f s) {a b : ℝ}
    (hs : Ioc a b ⊆ s) : Measurable ((Ioc a b).indicator f) := by
  by_cases hab : a < b
  · let c : ℕ → ℝ := fun n => a + (b - a) / ((n : ℝ) + 1)
    have hc (n : ℕ) : c n ∈ Ioc a b := by
      have hp : 0 < (n : ℝ) + 1 := by positivity
      have hnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hpos : 0 < (b - a) / ((n : ℝ) + 1) :=
        div_pos (sub_pos.mpr hab) hp
      have hle : (b - a) / ((n : ℝ) + 1) ≤ b - a := by
        apply (div_le_iff₀ hp).mpr
        nlinarith [mul_nonneg (sub_nonneg.mpr hab.le) hnonneg]
      exact ⟨by dsimp [c]; linarith, by dsimp [c]; linarith⟩
    have hc_lim : Tendsto c atTop (𝓝 a) := by
      have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (b - a)).const_add a
      simpa only [c, div_eq_mul_inv, one_mul, mul_zero, add_zero] using h
    have hmeas (n : ℕ) : Measurable ((Icc (c n) b).indicator f) := by
      have hsub : Icc (c n) b ⊆ s := by
        intro x hx
        exact hs ⟨(hc n).1.trans_le hx.1, hx.2⟩
      have hsubU : uIcc (c n) b ⊆ s := by
        simpa only [uIcc_of_le (hc n).2] using hsub
      simpa only [uIcc_of_le (hc n).2] using
        (hf.measurable_indicator_uIcc hsubU)
    apply measurable_of_tendsto_metrizable hmeas
    apply tendsto_pi_nhds.mpr
    intro x
    have hev : ∀ᶠ n : ℕ in atTop,
        (Icc (c n) b).indicator f x = (Ioc a b).indicator f x := by
      by_cases hx : x ∈ Ioc a b
      · filter_upwards [hc_lim.eventually (Iio_mem_nhds hx.1)] with n hn
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem
          (show x ∈ Icc (c n) b from ⟨hn.le, hx.2⟩)]
      · apply Filter.Eventually.of_forall
        intro n
        have hnot : x ∉ Icc (c n) b := by
          intro h
          exact hx ⟨(hc n).1.trans_le h.1, h.2⟩
        simp [Set.indicator, hx, hnot]
    exact tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm)
  · have he : Ioc a b = ∅ := by
      ext x
      simp only [mem_Ioc, mem_empty_iff_false, iff_false]
      intro hx
      exact (not_lt.mpr (le_of_not_gt hab)) (hx.1.trans_le hx.2)
    simp [he]

/-- A BV function on an open interval is measurable there, with zero
extension outside the interval. -/
theorem measurable_indicator_Ioo {f : ℝ → ℝ} {s : Set ℝ}
    (hf : BoundedVariationOn f s) {a b : ℝ}
    (hs : Ioo a b ⊆ s) : Measurable ((Ioo a b).indicator f) := by
  by_cases hab : a < b
  · let δ : ℕ → ℝ := fun n => ((b - a) / 2) / ((n : ℝ) + 1)
    let c : ℕ → ℝ := fun n => a + δ n
    let d : ℕ → ℝ := fun n => b - δ n
    have hδ (n : ℕ) : 0 < δ n ∧ δ n ≤ (b - a) / 2 := by
      have hp : 0 < (n : ℝ) + 1 := by positivity
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hpos : 0 < (b - a) / 2 := by positivity
      constructor
      · exact div_pos hpos hp
      · apply (div_le_iff₀ hp).mpr
        nlinarith [mul_nonneg hpos.le hn]
    have hcd (n : ℕ) : c n ≤ d n := by
      have h := (hδ n).2
      dsimp [c, d]
      linarith
    have hc (n : ℕ) : a < c n := by
      dsimp [c]
      linarith [(hδ n).1]
    have hd (n : ℕ) : d n < b := by
      dsimp [d]
      linarith [(hδ n).1]
    have hδlim : Tendsto δ atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        ((b - a) / 2)
      simpa only [δ, div_eq_mul_inv, one_mul, mul_zero] using h
    have hclim : Tendsto c atTop (𝓝 a) := by
      have h := hδlim.const_add a
      simpa only [c, add_zero] using h
    have hdlim : Tendsto d atTop (𝓝 b) := by
      have hconst : Tendsto (fun _ : ℕ => b) atTop (𝓝 b) := tendsto_const_nhds
      have h := hconst.sub hδlim
      simpa only [d, sub_zero] using h
    have hmeas (n : ℕ) : Measurable ((Icc (c n) (d n)).indicator f) := by
      have hsub : uIcc (c n) (d n) ⊆ s := by
        rw [uIcc_of_le (hcd n)]
        intro x hx
        exact hs ⟨(hc n).trans_le hx.1, hx.2.trans_lt (hd n)⟩
      simpa only [uIcc_of_le (hcd n)] using hf.measurable_indicator_uIcc hsub
    apply measurable_of_tendsto_metrizable hmeas
    apply tendsto_pi_nhds.mpr
    intro x
    have hev : ∀ᶠ n : ℕ in atTop,
        (Icc (c n) (d n)).indicator f x = (Ioo a b).indicator f x := by
      by_cases hx : x ∈ Ioo a b
      · filter_upwards [hclim.eventually (Iio_mem_nhds hx.1),
          hdlim.eventually (Ioi_mem_nhds hx.2)] with n hcn hdn
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem
          (show x ∈ Icc (c n) (d n) from ⟨hcn.le, hdn.le⟩)]
      · apply Filter.Eventually.of_forall
        intro n
        have hnot : x ∉ Icc (c n) (d n) := by
          intro h
          exact hx ⟨(hc n).trans_le h.1, h.2.trans_lt (hd n)⟩
        simp [Set.indicator, hx, hnot]
    exact tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm)
  · have he : Ioo a b = ∅ := by
      ext x
      simp only [mem_Ioo, mem_empty_iff_false, iff_false]
      intro hx
      exact hab (hx.1.trans hx.2)
    simp [he]

end BoundedVariationOn

end
