module

public import ChristodoulouBV.Uniqueness.ExtensionStarTraceOffAxisJointRadius
public import ChristodoulouBV.Uniqueness.ExtensionStarTraceRadiusFloor
import Mathlib.Tactic.Linarith

/-!
# Positive radius floor on terminal rectangles

The cutoff-independent radial lower bound survives at the terminal edge by
continuity of the canonical radius trace.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The terminal radius has a positive floor, including its top edge. -/
theorem exists_radius_terminal_trace_with_floor_on_rectangle
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε a vBar : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ b ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge b) (S b) ∧
      (∀ v ∈ Ioo (0 : ℝ) b,
        (S b).r 0 v = v / 2 ∧ (S b).alpha 0 v = alpha₀ v))
    (hε1 : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ b ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge b,
        2 * (S b).m p.1 p.2 / (S b).r p.1 p.2 ≤ ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ rTrace : ℝ × ℝ → ℝ,
      ContinuousOn rTrace (Icc 0 a ×ˢ Icc vBar vStar) ∧
      (∀ u ∈ Icc 0 a, ∀ v ∈ Icc vBar vStar, ρ ≤ rTrace (u, v)) ∧
      ∀ b ∈ Ioo (0 : ℝ) vStar,
        ∀ u ∈ Icc 0 a, ∀ v ∈ Ico vBar b,
          rTrace (u, v) = (S b).r u v := by
  obtain ⟨R, hR, hRmatch⟩ :=
    exists_radius_terminal_trace_on_rectangle ha haBar hBarStar hfamily
  obtain ⟨c, hc, hfloor⟩ :=
    exists_uniform_radius_floor_before_star hu₀ hα hfamily hε1 htail
  have hρ : 0 < c * (vBar - a) :=
    mul_pos hc (sub_pos.mpr haBar)
  refine ⟨c * (vBar - a), hρ, R, hR, ?_, hRmatch⟩
  intro u hu v hv
  have hslice : ContinuousOn (fun w => R (u, w)) (Icc vBar vStar) :=
    hR.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun w hw => ⟨hu, hw⟩)
  have hmap : MapsTo (fun w => R (u, w))
      (Ico vBar vStar) (Ici (c * (vBar - a))) := by
    intro w hw
    let b : ℝ := (w + vStar) / 2
    have hwb : w < b := by dsimp [b]; linarith only [hw.2]
    have hbStar : b < vStar := by dsimp [b]; linarith only [hw.2]
    have hb0 : 0 < b := by dsimp [b]; linarith only [ha, haBar, hw.1, hw.2]
    have hb : b ∈ Ioo (0 : ℝ) vStar := ⟨hb0, hbStar⟩
    change c * (vBar - a) ≤ R (u, w)
    rw [hRmatch b hb u hu w ⟨hw.1, hwb⟩]
    calc
      c * (vBar - a) ≤ c * (w - u) := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        linarith only [hu.2, hw.1]
      _ ≤ (S b).r u w := hfloor b hb u w hu.1
        (hu.2.trans_lt (haBar.trans_le hw.1)) hwb
  have hclosed : closure (Ico vBar vStar) = Icc vBar vStar :=
    closure_Ico hBarStar.ne
  rw [← hclosed] at hslice hv
  have h := hmap.closure_of_continuousOn hslice hv
  simpa only [isClosed_Ici.closure_eq, Set.mem_Ici] using h

end ChristodoulouBV.Uniqueness

end
