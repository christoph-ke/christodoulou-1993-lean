module

public import ChristodoulouBV.Uniqueness.UnionBVAxisTraces

/-!
# Local variation at mixed terminal incoming levels

The source controlling a finite partition may depend on its largest point.
The lower-level source interval may also depend on the level; a uniform
eventual bound still passes to the terminal partition.
-/

public section

open Set Filter
open scoped Topology ENNReal

namespace ChristodoulouBV.Uniqueness

/-- Uniform local variation bounds for either source pass through their
compatible terminal values on an arbitrary set of incoming points. -/
theorem incoming_variation_union_local_le_max
    {U₁ U₂ : Set (ℝ × ℝ)} {v : ℝ} {s : Set ℝ}
    {F₁ F₂ G : ℝ → ℝ → ℝ} {A₁ A₂ : ℝ → Set ℝ}
    {C₁ C₂ : ℝ≥0∞}
    (hchoose : ∀ b ∈ s, (b, v) ∈ U₁ ∪ U₂)
    (hlim₁ : ∀ ⦃b u⦄, b ∈ s → (b, v) ∈ U₁ → u ∈ s → u ≤ b →
      Tendsto (F₁ u) (𝓝[<] v) (𝓝 (G u v)))
    (hlim₂ : ∀ ⦃b u⦄, b ∈ s → (b, v) ∈ U₂ → u ∈ s → u ≤ b →
      Tendsto (F₂ u) (𝓝[<] v) (𝓝 (G u v)))
    (hmem₁ : ∀ ⦃b⦄, b ∈ s → (b, v) ∈ U₁ →
      ∀ᶠ t in 𝓝[<] v, ∀ u ∈ s, u ≤ b → u ∈ A₁ t)
    (hmem₂ : ∀ ⦃b⦄, b ∈ s → (b, v) ∈ U₂ →
      ∀ᶠ t in 𝓝[<] v, ∀ u ∈ s, u ≤ b → u ∈ A₂ t)
    (hbound₁ : ∀ᶠ t in 𝓝[<] v,
      eVariationOn (fun u => F₁ u t) (A₁ t) ≤ C₁)
    (hbound₂ : ∀ᶠ t in 𝓝[<] v,
      eVariationOn (fun u => F₂ u t) (A₂ t) ≤ C₂) :
    eVariationOn (fun u => G u v) s ≤ max C₁ C₂ := by
  apply iSup_le
  rintro ⟨n, ⟨w, hw, hws⟩⟩
  rcases hchoose (w n) (hws n) with hb₁ | hb₂
  · have hsum : Tendsto
        (fun t => ∑ i ∈ Finset.range n,
          edist (F₁ (w (i + 1)) t) (F₁ (w i) t))
        (𝓝[<] v)
        (𝓝 (∑ i ∈ Finset.range n,
          edist (G (w (i + 1)) v) (G (w i) v))) := by
      apply tendsto_finsetSum
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      exact (hlim₁ (hws n) hb₁ (hws (i + 1))
        (hw (Nat.succ_le_of_lt hin))).edist
        (hlim₁ (hws n) hb₁ (hws i) (hw (Nat.le_of_lt hin)))
    have hbound : ∀ᶠ t in 𝓝[<] v,
        (∑ i ∈ Finset.range n,
          edist (F₁ (w (i + 1)) t) (F₁ (w i) t)) ≤ max C₁ C₂ := by
      filter_upwards [hmem₁ (hws n) hb₁, hbound₁] with t ht hC
      exact (eVariationOn.sum_le_of_monotoneOn_Iic
        (hw.monotoneOn _) (fun i hi => ht (w i) (hws i) (hw hi))).trans
          (hC.trans (le_max_left _ _))
    exact le_of_tendsto hsum hbound
  · have hsum : Tendsto
        (fun t => ∑ i ∈ Finset.range n,
          edist (F₂ (w (i + 1)) t) (F₂ (w i) t))
        (𝓝[<] v)
        (𝓝 (∑ i ∈ Finset.range n,
          edist (G (w (i + 1)) v) (G (w i) v))) := by
      apply tendsto_finsetSum
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      exact (hlim₂ (hws n) hb₂ (hws (i + 1))
        (hw (Nat.succ_le_of_lt hin))).edist
        (hlim₂ (hws n) hb₂ (hws i) (hw (Nat.le_of_lt hin)))
    have hbound : ∀ᶠ t in 𝓝[<] v,
        (∑ i ∈ Finset.range n,
          edist (F₂ (w (i + 1)) t) (F₂ (w i) t)) ≤ max C₁ C₂ := by
      filter_upwards [hmem₂ (hws n) hb₂, hbound₂] with t ht hC
      exact (eVariationOn.sum_le_of_monotoneOn_Iic
        (hw.monotoneOn _) (fun i hi => ht (w i) (hws i) (hw hi))).trans
          (hC.trans (le_max_right _ _))
    exact le_of_tendsto hsum hbound

end ChristodoulouBV.Uniqueness

end
