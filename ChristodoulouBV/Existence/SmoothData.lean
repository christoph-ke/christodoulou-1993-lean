module

public import ChristodoulouBV.Existence.ArbitraryBVApproximation

/-!
# Smooth initial data below the universal threshold

The BV branch of Theorem 6.2 starts with one sequence of smooth data whose
values converge at every positive point, including prescribed values at jumps.
The sequence stays below any strict variation threshold, including the fixed
`epsilonChosen`, and has no more variation than the original datum. The
right-continuous version records the sharper one-sided approximation used by
the quantitative existence construction.
-/

public section

open Set Filter
open scoped ENNReal Topology

namespace ChristodoulouBV

/-- A datum below the universal C¹ threshold has smooth approximants with
literal pointwise convergence on the positive ray. Every variation stays below
the threshold and approaches the original variation. The source's `2D` bound
holds strictly when `D > 0`; at `D = 0` every approximant has zero variation. -/
theorem smooth_data_below_epsilon (εStar : ℝ) (alpha₀ : ℝ → ℝ)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal εStar) :
    ∃ alphaₙ : ℕ → ℝ → ℝ,
      (∀ n, ContDiffOn ℝ 1 (alphaₙ n) (Ici 0)) ∧
      (∀ v, 0 < v → Tendsto (fun n => alphaₙ n v) atTop (𝓝 (alpha₀ v))) ∧
      (∀ n, eVariationOn (alphaₙ n) (Ioi (0 : ℝ)) ≤
        eVariationOn alpha₀ (Ioi (0 : ℝ))) ∧
      (∀ n, eVariationOn (alphaₙ n) (Ioi (0 : ℝ)) <
        ENNReal.ofReal εStar) ∧
      Tendsto (fun n => eVariationOn (alphaₙ n) (Ioi (0 : ℝ))) atTop
        (𝓝 (eVariationOn alpha₀ (Ioi (0 : ℝ)))) ∧
      (0 < eVariationOn alpha₀ (Ioi (0 : ℝ)) →
        ∀ n, eVariationOn (alphaₙ n) (Ioi (0 : ℝ)) <
          2 * eVariationOn alpha₀ (Ioi (0 : ℝ))) ∧
      (eVariationOn alpha₀ (Ioi (0 : ℝ)) = 0 →
        ∀ n, eVariationOn (alphaₙ n) (Ioi (0 : ℝ)) = 0) := by
  let D := eVariationOn alpha₀ (Ioi (0 : ℝ))
  have hfin : D < ⊤ := hD.trans_le le_top
  obtain ⟨alphaₙ, hsmooth, hpoint, hvar, hvarlim⟩ :=
    exists_smooth_approx_arbitrary_values alpha₀ hfin
  refine ⟨alphaₙ, hsmooth, hpoint, hvar, fun n => (hvar n).trans_lt hD,
    hvarlim, ?_, ?_⟩
  · intro hpos n
    have hlt : D < 2 * D := by
      simpa only [two_mul] using ENNReal.lt_add_right (ne_of_lt hfin) (ne_of_gt hpos)
    exact (hvar n).trans_lt hlt
  · intro hzero n
    exact le_antisymm (hzero ▸ hvar n) bot_le

/-- For right-continuous BV data, the one-sided smoother gives the same
pointwise trace and sharp variation control under the universal threshold. -/
theorem smooth_data_below_epsilon_of_right_continuous
    (εStar : ℝ) (alpha₀ : ℝ → ℝ)
    (hrc : ∀ v ∈ Ici (0 : ℝ), ContinuousWithinAt alpha₀ (Ici v) v)
    (hD : eVariationOn alpha₀ (Ioi (0 : ℝ)) <
      ENNReal.ofReal εStar) :
    ∃ alphaₙ : ℕ → ℝ → ℝ,
      (∀ n, ContDiffOn ℝ 1 (alphaₙ n) (Ici 0)) ∧
      (∀ v, 0 < v → Tendsto (fun n => alphaₙ n v) atTop (𝓝 (alpha₀ v))) ∧
      (∀ n, eVariationOn (alphaₙ n) (Ioi (0 : ℝ)) ≤
        eVariationOn alpha₀ (Ioi (0 : ℝ))) ∧
      (∀ n, eVariationOn (alphaₙ n) (Ioi (0 : ℝ)) <
        ENNReal.ofReal εStar) ∧
      Tendsto (fun n => eVariationOn (alphaₙ n) (Ioi (0 : ℝ))) atTop
        (𝓝 (eVariationOn alpha₀ (Ioi (0 : ℝ)))) := by
  have hfin : eVariationOn alpha₀ (Ioi (0 : ℝ)) < ⊤ :=
    hD.trans_le le_top
  obtain ⟨alphaₙ, hsmooth, hpoint, hvar⟩ :=
    exists_smooth_approx_of_right_continuous alpha₀ hfin hrc
  refine ⟨alphaₙ, hsmooth, hpoint, hvar,
    fun n => (hvar n).trans_lt hD, ?_⟩
  exact tendsto_eVariationOn_of_pointwise_of_le alpha₀ alphaₙ hpoint hvar

end ChristodoulouBV

end
