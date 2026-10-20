module

public import ChristodoulouBV.Uniqueness.UnionBVAxisIncoming

/-!
# Past incoming axis variation on the union

At the endpoint `δ = 0`, approximation from below uses a strictly positive
source `δ'`, which is still in the source item-4 range.
-/

@[expose] public section

open Set Filter
open scoped Topology ENNReal

namespace ChristodoulouBV.Uniqueness

/-- At each past incoming axis level, the selected scalar variation is
bounded by the two source item-4 suprema at the same scale. -/
theorem glued_past_incoming_variation_le
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    (a ε δ : ℝ) (hδ : δ ∈ Ico (0 : ℝ) ε) :
    eVariationOn (fun u => (gluedFields U₁ S₁ S₂).phi u (a - δ))
      {u | u ∈ Ioo (a - ε) (a - δ) ∧ (u, a - δ) ∈ U₁ ∪ U₂} ≤
      max
        (⨆ d ∈ Ico (0 : ℝ) ε,
          eVariationOn (fun u => S₁.phi u (a - d))
            {u | u ∈ Ioo (a - ε) (a - d) ∧ (u, a - d) ∈ U₁})
        (⨆ d ∈ Ico (0 : ℝ) ε,
          eVariationOn (fun u => S₂.phi u (a - d))
            {u | u ∈ Ioo (a - ε) (a - d) ∧ (u, a - d) ∈ U₂}) := by
  let v := a - δ
  have hlv : a - ε < v := by dsimp [v]; linarith only [hδ.2]
  let s : Set ℝ := {u | u ∈ Ioo (a - ε) v ∧ (u, v) ∈ U₁ ∪ U₂}
  let A₁ : ℝ → Set ℝ := fun t => {u | u ∈ Ioo (a - ε) t ∧ (u, t) ∈ U₁}
  let A₂ : ℝ → Set ℝ := fun t => {u | u ∈ Ioo (a - ε) t ∧ (u, t) ∈ U₂}
  have hchoose (b : ℝ) (hb : b ∈ s) : (b, v) ∈ U₁ ∪ U₂ := hb.2
  have hlim₁ ⦃b u : ℝ⦄ (hb : b ∈ s) (hb₁ : (b, v) ∈ U₁)
      (hu : u ∈ s) (hub : u ≤ b) :
      Tendsto (S₁.phi u) (𝓝[<] v)
        (𝓝 ((gluedFields U₁ S₁ S₂).phi u v)) :=
    (first_source_fields_tendsto_incoming_terminal
      h₁ h₂ hdata hb₁ hu.2 hub).2.1
  have hlim₂ ⦃b u : ℝ⦄ (hb : b ∈ s) (hb₂ : (b, v) ∈ U₂)
      (hu : u ∈ s) (hub : u ≤ b) :
      Tendsto (S₂.phi u) (𝓝[<] v)
        (𝓝 ((gluedFields U₁ S₁ S₂).phi u v)) :=
    (second_source_fields_tendsto_incoming_terminal
      h₁ h₂ hdata hb₂ hu.2 hub).2.1
  have hmem₁ ⦃b : ℝ⦄ (hb : b ∈ s) (hb₁ : (b, v) ∈ U₁) :
      ∀ᶠ t in 𝓝[<] v, ∀ u ∈ s, u ≤ b → u ∈ A₁ t := by
    filter_upwards [Ioo_mem_nhdsLT (h₁.solution.development.wedge hb₁).2]
      with t ht u hu hub
    have hu0 : 0 ≤ u := by
      rcases hu.2 with h | h
      · exact (h₁.solution.development.wedge h).1
      · exact (h₂.solution.development.wedge h).1
    exact ⟨⟨hu.1.1, hub.trans_lt ht.1⟩,
      h₁.solution.development.past_mem hb₁ hu0 hub
        (hub.trans_lt ht.1) ht.2⟩
  have hmem₂ ⦃b : ℝ⦄ (hb : b ∈ s) (hb₂ : (b, v) ∈ U₂) :
      ∀ᶠ t in 𝓝[<] v, ∀ u ∈ s, u ≤ b → u ∈ A₂ t := by
    filter_upwards [Ioo_mem_nhdsLT (h₂.solution.development.wedge hb₂).2]
      with t ht u hu hub
    have hu0 : 0 ≤ u := by
      rcases hu.2 with h | h
      · exact (h₁.solution.development.wedge h).1
      · exact (h₂.solution.development.wedge h).1
    exact ⟨⟨hu.1.1, hub.trans_lt ht.1⟩,
      h₂.solution.development.past_mem hb₂ hu0 hub
        (hub.trans_lt ht.1) ht.2⟩
  have hbound₁ : ∀ᶠ t in 𝓝[<] v,
      eVariationOn (fun u => S₁.phi u t) (A₁ t) ≤
        ⨆ d ∈ Ico (0 : ℝ) ε,
          eVariationOn (fun u => S₁.phi u (a - d))
            {u | u ∈ Ioo (a - ε) (a - d) ∧ (u, a - d) ∈ U₁} := by
    filter_upwards [Ioo_mem_nhdsLT hlv] with t ht
    have hdt : a - t ∈ Ico (0 : ℝ) ε := by
      constructor
      · dsimp [v] at ht
        linarith only [ht.2, hδ.1]
      · linarith only [ht.1]
    have hle :
        eVariationOn (fun u => S₁.phi u (a - (a - t)))
          {u | u ∈ Ioo (a - ε) (a - (a - t)) ∧
            (u, a - (a - t)) ∈ U₁} ≤
        ⨆ d ∈ Ico (0 : ℝ) ε,
          eVariationOn (fun u => S₁.phi u (a - d))
            {u | u ∈ Ioo (a - ε) (a - d) ∧ (u, a - d) ∈ U₁} :=
      le_iSup_of_le (a - t)
        (le_iSup_of_le hdt (le_refl _))
    have hta : a - (a - t) = t := by ring
    simpa only [hta, A₁] using hle
  have hbound₂ : ∀ᶠ t in 𝓝[<] v,
      eVariationOn (fun u => S₂.phi u t) (A₂ t) ≤
        ⨆ d ∈ Ico (0 : ℝ) ε,
          eVariationOn (fun u => S₂.phi u (a - d))
            {u | u ∈ Ioo (a - ε) (a - d) ∧ (u, a - d) ∈ U₂} := by
    filter_upwards [Ioo_mem_nhdsLT hlv] with t ht
    have hdt : a - t ∈ Ico (0 : ℝ) ε := by
      constructor
      · dsimp [v] at ht
        linarith only [ht.2, hδ.1]
      · linarith only [ht.1]
    have hle :
        eVariationOn (fun u => S₂.phi u (a - (a - t)))
          {u | u ∈ Ioo (a - ε) (a - (a - t)) ∧
            (u, a - (a - t)) ∈ U₂} ≤
        ⨆ d ∈ Ico (0 : ℝ) ε,
          eVariationOn (fun u => S₂.phi u (a - d))
            {u | u ∈ Ioo (a - ε) (a - d) ∧ (u, a - d) ∈ U₂} :=
      le_iSup_of_le (a - t)
        (le_iSup_of_le hdt (le_refl _))
    have hta : a - (a - t) = t := by ring
    simpa only [hta, A₂] using hle
  exact incoming_variation_union_local_le_max hchoose hlim₁ hlim₂
    hmem₁ hmem₂ hbound₁ hbound₂

end ChristodoulouBV.Uniqueness

end
