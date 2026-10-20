module

public import ChristodoulouBV.ForMathlib.BoundedVariation.Algebra
public import ChristodoulouBV.ForMathlib.BoundedVariation.Representatives
public import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Tactic

/-!
# Open fixed-edge variation tails

Shrinking open sections exclude the value at the limiting endpoint. The
statements below concern pointwise variation and do not identify it with
the variation measure of a BV representative.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- Pointwise variation on an open left tail vanishes, even when the BV
function has an arbitrary value at the limiting endpoint. -/
theorem bv_variation_left_tail_tendsto_zero
    {f : ℝ → ℝ} {l a : ℝ} (hla : l < a)
    (hf : BoundedVariationOn f (Ioo l a)) :
    Tendsto (fun u => eVariationOn f (Ioo u a)) (𝓝[<] a) (𝓝 0) := by
  have ht := hf.tendsto_eVariationOn_Ico_zero a
  have he : 𝓝[Ioo l a] a = 𝓝[<] a := by
    rw [show Ioo l a = Ioi l ∩ Iio a by ext x; rfl]
    exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hla))
  rw [he] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [Ioo_mem_nhdsLT hla] with u hu
  apply eVariationOn.mono
  intro x hx
  exact ⟨⟨hu.1.trans hx.1, hx.2⟩, ⟨hx.1.le, hx.2⟩⟩

/-- Pointwise variation on an open right tail vanishes without any
continuity convention at the limiting endpoint. -/
theorem bv_variation_right_tail_tendsto_zero
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : BoundedVariationOn f (Ioo a b)) :
    Tendsto (fun v => eVariationOn f (Ioo a v)) (𝓝[>] a) (𝓝 0) := by
  have ht := hf.tendsto_eVariationOn_Ioc_zero a
  have he : 𝓝[Ioo a b] a = 𝓝[>] a := by
    rw [show Ioo a b = Iio b ∩ Ioi a by ext x; simp only [mem_Ioo, mem_inter_iff,
      mem_Iio, mem_Ioi, and_comm]]
    exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hab))
  rw [he] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [Ioo_mem_nhdsGT hab] with v hv
  apply eVariationOn.mono
  intro x hx
  exact ⟨⟨hx.1, hx.2.trans hv.2⟩, ⟨hx.1, hx.2.le⟩⟩

/-- Both endpoint directions of the open fixed-edge shrinking rule. -/
theorem bv_fixed_edge_variation_shrink
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : BoundedVariationOn f (Ioo a b)) :
    Tendsto (fun u => eVariationOn f (Ioo u b)) (𝓝[<] b) (𝓝 0) ∧
      Tendsto (fun v => eVariationOn f (Ioo a v)) (𝓝[>] a) (𝓝 0) :=
  ⟨bv_variation_left_tail_tendsto_zero hab hf,
    bv_variation_right_tail_tendsto_zero hab hf⟩

end ChristodoulouBV

end
