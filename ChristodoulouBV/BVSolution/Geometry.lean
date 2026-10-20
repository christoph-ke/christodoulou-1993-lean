module

public import ChristodoulouBV.Frozen.DomainOfDevelopment
public import ChristodoulouBV.Frozen.AdjacentAxis
public import ChristodoulouBV.Frozen.OutSeg
public import ChristodoulouBV.Frozen.InSeg

/-!
# Geometry of BV developments

Past closure provides complete outgoing slices and incoming slices strictly below
the top of a causal past. No openness of the development is assumed.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.IsDomainOfDevelopment

/-- Every development point lies in the regular wedge. -/
theorem wedge {U : Set (ℝ × ℝ)} (h : IsDomainOfDevelopment U)
    {u v : ℝ} (huv : (u, v) ∈ U) : 0 ≤ u ∧ u < v := h.1 huv

/-- Every earlier outgoing point, including the chosen upper endpoint, belongs to the domain. -/
theorem outgoing_mem {U : Set (ℝ × ℝ)} (h : IsDomainOfDevelopment U)
    {u v t : ℝ} (huv : (u, v) ∈ U) (hut : u < t) (htv : t ≤ v) :
    (u, t) ∈ U := by
  rcases htv.eq_or_lt with rfl | htv
  · exact huv
  · exact h.2 (u, v) huv ⟨⟨(h.wedge huv).1, le_rfl⟩, ⟨hut, htv⟩⟩

/-- The printed causal past contains points strictly below its top. -/
theorem past_mem {U : Set (ℝ × ℝ)} (h : IsDomainOfDevelopment U)
    {u v s t : ℝ} (huv : (u, v) ∈ U) (hs : 0 ≤ s) (hsu : s ≤ u)
    (hst : s < t) (htv : t < v) : (s, t) ∈ U :=
  h.2 (u, v) huv ⟨⟨hs, hsu⟩, ⟨hst, htv⟩⟩

/-- A compact outgoing segment above the axis lies in the development. -/
theorem out_seg_subset {U : Set (ℝ × ℝ)} (h : IsDomainOfDevelopment U)
    {u v a b : ℝ} (huv : (u, v) ∈ U) (hua : u < a) (_hab : a ≤ b)
    (hbv : b ≤ v) : outSeg u a b ⊆ U := by
  intro p hp
  rcases p with ⟨s, t⟩
  have ⟨hs, ht⟩ : s = u ∧ t ∈ Icc a b := by
    simpa [outSeg] using hp
  subst s
  exact h.outgoing_mem huv (hua.trans_le ht.1) (ht.2.trans hbv)

/-- An incoming segment lies in the domain when its top coordinate is strictly
below that of a known development point. -/
theorem in_seg_subset {U : Set (ℝ × ℝ)} (h : IsDomainOfDevelopment U)
    {u v t a b : ℝ} (huv : (u, v) ∈ U) (ha : 0 ≤ a) (_hab : a ≤ b)
    (hbu : b ≤ u) (hbt : b < t) (htv : t < v) : inSeg t a b ⊆ U := by
  intro p hp
  rcases p with ⟨s, w⟩
  have ⟨hs, hw⟩ : s ∈ Icc a b ∧ w = t := by
    simpa [inSeg] using hp
  subst w
  exact h.past_mem huv (ha.trans hs.1) (hs.2.trans hbu)
    (hs.2.trans_lt hbt) htv

/-- The diagonal at the initial point of any actual outgoing slice is adjacent
to the development. -/
theorem axis_mem {U : Set (ℝ × ℝ)} (h : IsDomainOfDevelopment U)
    {u v : ℝ} (huv : (u, v) ∈ U) : u ∈ adjacentAxis U := by
  have hlt : u < v := (h.wedge huv).2
  have hslice : {t : ℝ | (u, t) ∈ U} ∈ 𝓝[>] u :=
    mem_of_superset (Ioo_mem_nhdsGT hlt) (fun t ht =>
      h.outgoing_mem huv ht.1 ht.2.le)
  change (u, u) ∈ closure U
  have hcont : Tendsto (fun t : ℝ => (u, t)) (𝓝[>] u) (𝓝 (u, u)) :=
    ((show Continuous (fun t : ℝ => (u, t)) by fun_prop).tendsto u).mono_left
      inf_le_left
  exact mem_closure_of_tendsto hcont hslice

/-- On an actual outgoing slice, the axis filter equals the ordinary right filter. -/
theorem axis_filter_eq {U : Set (ℝ × ℝ)} (h : IsDomainOfDevelopment U)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    𝓝[>] u ⊓ 𝓟 {t : ℝ | (u, t) ∈ U} = 𝓝[>] u := by
  have hlt : u < v := (h.wedge huv).2
  have hslice : {t : ℝ | (u, t) ∈ U} ∈ 𝓝[>] u :=
    mem_of_superset (Ioo_mem_nhdsGT hlt) (fun t ht =>
      h.outgoing_mem huv ht.1 ht.2.le)
  exact inf_eq_left.mpr (le_principal_iff.mpr hslice)

/-- The outgoing axis filter at an actual slice is nontrivial. -/
theorem axis_filter_ne_bot {U : Set (ℝ × ℝ)} (h : IsDomainOfDevelopment U)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    NeBot (𝓝[>] u ⊓ 𝓟 {t : ℝ | (u, t) ∈ U}) := by
  rw [h.axis_filter_eq huv]
  infer_instance

/-- Intersections of developments are developments. -/
theorem inter {U V : Set (ℝ × ℝ)} (hU : IsDomainOfDevelopment U)
    (hV : IsDomainOfDevelopment V) : IsDomainOfDevelopment (U ∩ V) := by
  constructor
  · intro p hp
    exact hU.1 hp.1
  · intro p hp q hq
    exact ⟨hU.2 p hp.1 hq, hV.2 p hp.2 hq⟩

/-- Unions of developments are developments. -/
theorem union {U V : Set (ℝ × ℝ)} (hU : IsDomainOfDevelopment U)
    (hV : IsDomainOfDevelopment V) : IsDomainOfDevelopment (U ∪ V) := by
  constructor
  · intro p hp
    rcases hp with hp | hp
    · exact hU.1 hp
    · exact hV.1 hp
  · intro p hp q hq
    rcases hp with hp | hp
    · exact Or.inl (hU.2 p hp hq)
    · exact Or.inr (hV.2 p hp hq)

end ChristodoulouBV.IsDomainOfDevelopment

end
