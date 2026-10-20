module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic

/-!
# The outer transverse Jacobian

The affine map from the unit interval to the physical transverse
interval transports `(a-δ) dy` to Lebesgue measure. This factor is
separate from the signed inner coordinate factor in the area primitive.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

attribute [local instance] Measure.Subtype.measureSpace

namespace ChristodoulouBV

/-- The outer affine chart transports `L dy` to physical Lebesgue
measure on its open image interval. -/
theorem affine_unit_volume {L : ℝ} (hL : 0 < L) (s : ℝ) :
    ENNReal.ofReal L • (volume : Measure (Ioo (0 : ℝ) 1)).map
        (fun y : Ioo (0 : ℝ) 1 => s + L * (y : ℝ)) =
      (volume : Measure ℝ).restrict (Ioo s (s + L)) := by
  let e : ℝ ≃ₜ ℝ := (Homeomorph.mulLeft₀ L hL.ne').trans (Homeomorph.addLeft s)
  have he (x : ℝ) : e x = s + L * x := rfl
  have hpre : e ⁻¹' Ioo s (s + L) = Ioo (0 : ℝ) 1 := by
    ext x
    simp only [mem_preimage, he, mem_Ioo]
    constructor
    · rintro ⟨hx0, hx1⟩
      constructor <;> nlinarith only [hL, hx0, hx1]
    · rintro ⟨hx0, hx1⟩
      constructor <;> nlinarith only [hL, hx0, hx1]
  have hscaled : ENNReal.ofReal L • (volume : Measure ℝ).map e = volume := by
    have hm : (volume : Measure ℝ).map e =
        ((volume : Measure ℝ).map (L * ·)).map (s + ·) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    have hs := Real.smul_map_volume_mul_left hL.ne'
    rw [abs_of_pos hL] at hs
    rw [hm, ← Measure.map_smul _ (by fun_prop), hs, map_add_left_eq_self]
  have hre := e.toMeasurableEquiv.restrict_map (volume : Measure ℝ) (Ioo s (s + L))
  change ((volume : Measure ℝ).map e).restrict (Ioo s (s + L)) =
    ((volume : Measure ℝ).restrict (e ⁻¹' Ioo s (s + L))).map e at hre
  rw [hpre] at hre
  calc
    _ = ENNReal.ofReal L • ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)).map e := by
      rw [← measurableSet_Ioo.map_coe_volume,
        Measure.map_map e.measurable measurable_subtype_coe]
      rfl
    _ = ENNReal.ofReal L • ((volume : Measure ℝ).map e).restrict (Ioo s (s + L)) :=
      congrArg (fun μ : Measure ℝ => ENNReal.ofReal L • μ) hre.symm
    _ = (ENNReal.ofReal L • (volume : Measure ℝ).map e).restrict (Ioo s (s + L)) :=
      (Measure.restrict_smul _ _ _).symm
    _ = _ := by rw [hscaled]

/-- Affine transverse substitution, with the outer factor retained. -/
theorem lintegral_affine_unit {L : ℝ} (hL : 0 < L) (s : ℝ)
    {F : ℝ → ℝ≥0∞} :
    (∫⁻ z in Ioo s (s + L), F z) =
      ENNReal.ofReal L * ∫⁻ y : Ioo (0 : ℝ) 1, F (s + L * (y : ℝ)) := by
  have hm : MeasurableEmbedding (fun y : Ioo (0 : ℝ) 1 => s + L * (y : ℝ)) := by
    let e : ℝ ≃ₜ ℝ := (Homeomorph.mulLeft₀ L hL.ne').trans (Homeomorph.addLeft s)
    change MeasurableEmbedding (e ∘ ((↑) : Ioo (0 : ℝ) 1 → ℝ))
    exact e.measurableEmbedding.comp (MeasurableEmbedding.subtype_coe measurableSet_Ioo)
  rw [← affine_unit_volume hL s, lintegral_smul_measure, hm.lintegral_map F, smul_eq_mul]

end ChristodoulouBV

end
