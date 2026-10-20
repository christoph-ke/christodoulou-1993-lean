module

public import ChristodoulouBV.Uniqueness.UnionBVIncomingLimit

/-!
# Variation on a union incoming slice

A terminal slice need not be an interval in either source. Every finite
ordered partition is controlled by the source containing its largest point,
using that source at levels immediately below the terminal level.
-/

public section

open Set Filter
open scoped Topology ENNReal

namespace ChristodoulouBV.Uniqueness

/-- Two past-closed domains with compatible terminal limits inherit the
maximum of their uniform incoming variation bounds. -/
theorem incoming_variation_union_le_max
    {U₁ U₂ : Set (ℝ × ℝ)}
    (hdev₁ : IsDomainOfDevelopment U₁)
    (hdev₂ : IsDomainOfDevelopment U₂)
    {F₁ F₂ G : ℝ → ℝ → ℝ} {C₁ C₂ : ℝ≥0∞}
    (hvar₁ : ∀ t, eVariationOn (fun u => F₁ u t) {u | (u, t) ∈ U₁} ≤ C₁)
    (hvar₂ : ∀ t, eVariationOn (fun u => F₂ u t) {u | (u, t) ∈ U₂} ≤ C₂)
    (hlim₁ : ∀ ⦃v b s⦄, (b, v) ∈ U₁ → (s, v) ∈ U₁ ∪ U₂ → s ≤ b →
      Tendsto (F₁ s) (𝓝[<] v) (𝓝 (G s v)))
    (hlim₂ : ∀ ⦃v b s⦄, (b, v) ∈ U₂ → (s, v) ∈ U₁ ∪ U₂ → s ≤ b →
      Tendsto (F₂ s) (𝓝[<] v) (𝓝 (G s v)))
    (v : ℝ) :
    eVariationOn (fun u => G u v) {u | (u, v) ∈ U₁ ∪ U₂} ≤ max C₁ C₂ := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  have htop : (u n, v) ∈ U₁ ∪ U₂ := hus n
  rcases htop with hb₁ | hb₂
  · have huv : u n < v := (hdev₁.wedge hb₁).2
    have hsource (t : ℝ) (ht : t ∈ Ioo (u n) v)
        (i : ℕ) (hi : i ≤ n) : (u i, t) ∈ U₁ := by
      have hui : (u i, v) ∈ U₁ ∪ U₂ := hus i
      have hi0 : 0 ≤ u i := by
        rcases hui with h | h
        · exact (hdev₁.wedge h).1
        · exact (hdev₂.wedge h).1
      exact hdev₁.past_mem hb₁ hi0 (hu hi) (lt_of_le_of_lt (hu hi) ht.1) ht.2
    have hsum : Tendsto
        (fun t => ∑ i ∈ Finset.range n,
          edist (F₁ (u (i + 1)) t) (F₁ (u i) t))
        (𝓝[<] v)
        (𝓝 (∑ i ∈ Finset.range n,
          edist (G (u (i + 1)) v) (G (u i) v))) := by
      apply tendsto_finsetSum
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      exact (hlim₁ hb₁ (hus (i + 1)) (hu (Nat.succ_le_of_lt hin))).edist
        (hlim₁ hb₁ (hus i) (hu (Nat.le_of_lt hin)))
    have hbound : ∀ᶠ t in 𝓝[<] v,
        (∑ i ∈ Finset.range n,
          edist (F₁ (u (i + 1)) t) (F₁ (u i) t)) ≤ max C₁ C₂ := by
      filter_upwards [Ioo_mem_nhdsLT huv] with t ht
      exact (eVariationOn.sum_le_of_monotoneOn_Iic
        (hu.monotoneOn _) (hsource t ht)).trans ((hvar₁ t).trans (le_max_left _ _))
    exact le_of_tendsto hsum hbound
  · have huv : u n < v := (hdev₂.wedge hb₂).2
    have hsource (t : ℝ) (ht : t ∈ Ioo (u n) v)
        (i : ℕ) (hi : i ≤ n) : (u i, t) ∈ U₂ := by
      have hui : (u i, v) ∈ U₁ ∪ U₂ := hus i
      have hi0 : 0 ≤ u i := by
        rcases hui with h | h
        · exact (hdev₁.wedge h).1
        · exact (hdev₂.wedge h).1
      exact hdev₂.past_mem hb₂ hi0 (hu hi) (lt_of_le_of_lt (hu hi) ht.1) ht.2
    have hsum : Tendsto
        (fun t => ∑ i ∈ Finset.range n,
          edist (F₂ (u (i + 1)) t) (F₂ (u i) t))
        (𝓝[<] v)
        (𝓝 (∑ i ∈ Finset.range n,
          edist (G (u (i + 1)) v) (G (u i) v))) := by
      apply tendsto_finsetSum
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      exact (hlim₂ hb₂ (hus (i + 1)) (hu (Nat.succ_le_of_lt hin))).edist
        (hlim₂ hb₂ (hus i) (hu (Nat.le_of_lt hin)))
    have hbound : ∀ᶠ t in 𝓝[<] v,
        (∑ i ∈ Finset.range n,
          edist (F₂ (u (i + 1)) t) (F₂ (u i) t)) ≤ max C₁ C₂ := by
      filter_upwards [Ioo_mem_nhdsLT huv] with t ht
      exact (eVariationOn.sum_le_of_monotoneOn_Iic
        (hu.monotoneOn _) (hsource t ht)).trans ((hvar₂ t).trans (le_max_right _ _))
    exact le_of_tendsto hsum hbound

end ChristodoulouBV.Uniqueness

end
