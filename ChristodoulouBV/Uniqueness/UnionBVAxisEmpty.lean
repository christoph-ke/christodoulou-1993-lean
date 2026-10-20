module

public import ChristodoulouBV.Uniqueness.UnionBVAxisOutgoing

/-!
# Vacuous item-4 limits away from adjacent axis points

Every sufficiently small axis square misses a development whose closure
does not contain the diagonal point. Its four local variation terms vanish.
-/

@[expose] public section

open Set Filter
open scoped Topology ENNReal

namespace ChristodoulouBV.Uniqueness

/-- A source satisfies all four item-4 limits at every nonadjacent axis
parameter, because a small box around the diagonal misses its domain. -/
theorem axisVanishingVariation_of_not_adjacent
    {U : Set (ℝ × ℝ)} {S : Fields} {a : ℝ}
    (ha : a ∉ adjacentAxis U) : AxisVanishingVariation U S a := by
  change (a, a) ∉ closure U at ha
  have hnear : (closure U)ᶜ ∈ 𝓝 (a, a) :=
    isClosed_closure.isOpen_compl.mem_nhds ha
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hno (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) η)
      (u v : ℝ) (hu : u ∈ Icc (a - ε) (a + ε))
      (hv : v ∈ Icc (a - ε) (a + ε)) : (u, v) ∉ U := by
    intro hp
    have huη : dist u a < η := by
      rw [Real.dist_eq]
      exact (abs_le.mpr ⟨by linarith only [hu.1],
        by linarith only [hu.2]⟩).trans_lt hε.2
    have hvη : dist v a < η := by
      rw [Real.dist_eq]
      exact (abs_le.mpr ⟨by linarith only [hv.1],
        by linarith only [hv.2]⟩).trans_lt hε.2
    have hpball : (u, v) ∈ Metric.ball (a, a) η := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt huη hvη
    exact (hball hpball) (subset_closure hp)
  have hsmall : Ioo (0 : ℝ) η ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hη
  have hlimit {D : ℝ → Set ℝ} {F : ℝ → ℝ → ℝ → ℝ}
      {A : ℝ → ℝ → Set ℝ}
      (hempty : ∀ ε ∈ Ioo (0 : ℝ) η, ∀ δ ∈ D ε, A ε δ = ∅) :
      Tendsto (fun ε => ⨆ δ ∈ D ε, eVariationOn (F ε δ) (A ε δ))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ENNReal)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hsmall] with ε hε
    have hz : (⨆ δ ∈ D ε, eVariationOn (F ε δ) (A ε δ)) = 0 := by
      apply le_antisymm _ bot_le
      apply iSup_le
      intro δ
      apply iSup_le
      intro hδ
      rw [hempty ε hε δ hδ]
      simp
    exact hz.symm
  refine {
    past_outgoing := ?_
    past_incoming := ?_
    future_incoming := ?_
    future_outgoing := ?_ }
  · apply hlimit
    intro ε hε δ hδ
    ext v
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨hv, hp⟩
    apply hno ε hε (a - δ) v
      ⟨by linarith only [hδ.2], by linarith only [hδ.1, hε.1]⟩
      ⟨by linarith only [hv.1, hδ.2], by linarith only [hv.2, hε.1]⟩ hp
  · apply hlimit
    intro ε hε δ hδ
    ext u
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨hu, hp⟩
    apply hno ε hε u (a - δ)
      ⟨hu.1.le, by linarith only [hu.2, hδ.1, hε.1]⟩
      ⟨by linarith only [hδ.2], by linarith only [hδ.1, hε.1]⟩ hp
  · apply hlimit
    intro ε hε δ hδ
    ext u
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨hu, hp⟩
    apply hno ε hε u (a + δ)
      ⟨by linarith only [hu.1, hε.1], by linarith only [hu.2, hδ.2]⟩
      ⟨by linarith only [hδ.1, hε.1], by linarith only [hδ.2]⟩ hp
  · apply hlimit
    intro ε hε δ hδ
    ext v
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨hv, hp⟩
    apply hno ε hε (a + δ) v
      ⟨by linarith only [hδ.1, hε.1], by linarith only [hδ.2]⟩
      ⟨by linarith only [hv.1, hδ.1, hε.1], hv.2.le⟩ hp

/-- Item 4 of a BV solution is available at every axis parameter; away
from the adjacent axis it is vacuous. -/
theorem IsBVSolution.axisVanishingVariation_all
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    (a : ℝ) : AxisVanishingVariation U S a := by
  by_cases ha : a ∈ adjacentAxis U
  · exact h.item4 a ha
  · exact axisVanishingVariation_of_not_adjacent ha

end ChristodoulouBV.Uniqueness

end
