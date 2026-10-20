module

public import ChristodoulouBV.Uniqueness.UnionBVRegularity

/-!
# Axis traces for canonical outgoing densities

The left-trace normalization of a BV density differs from its original
values by a quantity tending to zero along an outgoing axis slice.
-/

@[expose] public section

open Set Filter
open scoped Topology ENNReal

namespace ChristodoulouBV.Uniqueness

/-- Replacing an outgoing source BV representative by its left trace
preserves a zero axis limit after adding any other function. -/
theorem source_axis_tendsto_leftLim_add
    {U : Set (ℝ × ℝ)} (hdev : IsDomainOfDevelopment U)
    {f g : ℝ → ℝ} (a : ℝ)
    (hf : BoundedVariationOn f {v | (a, v) ∈ U})
    (hlim : Tendsto (fun v => f v + g v)
      (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ U}) (𝓝 (0 : ℝ))) :
    Tendsto (fun v => f.leftLim v + g v)
      (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ U}) (𝓝 (0 : ℝ)) := by
  let s : Set ℝ := {v | (a, v) ∈ U}
  have hs : s ⊆ Ioi a := by
    intro v hv
    exact (hdev.wedge hv).2
  have hfilter : (𝓝[>] a ⊓ 𝓟 s) = 𝓝[s] a := by
    rw [nhdsWithin, nhdsWithin, inf_assoc, Filter.inf_principal,
      Set.inter_eq_right.mpr hs]
  have hvar : Tendsto (fun v => (eVariationOn f (s ∩ Ioc a v)).toReal)
      (𝓝[s] a) (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp)).comp
        (hf.tendsto_eVariationOn_Ioc_zero a)
  have hdist : Tendsto (fun v => dist (f.leftLim v) (f v))
      (𝓝[s] a) (𝓝 (0 : ℝ)) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg) ?_ hvar
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hav : a < v := hs hv
    have hsub : Ioc a v ⊆ s := by
      intro t ht
      exact hdev.outgoing_mem hv ht.1 ht.2
    have hBV : BoundedVariationOn f (Ioc a v) := hf.mono hsub
    have hleft := leftLim_tendsto_of_bv_Ioc hav hBV
    have hsmall : BoundedVariationOn f (s ∩ Ioc a v) :=
      hf.mono inter_subset_left
    have hbound : ∀ᶠ t in 𝓝[<] v,
        dist (f t) (f v) ≤ (eVariationOn f (s ∩ Ioc a v)).toReal := by
      filter_upwards [Ioo_mem_nhdsLT hav] with t ht
      have htmem : t ∈ s ∩ Ioc a v :=
        ⟨hsub ⟨ht.1, ht.2.le⟩, ⟨ht.1, ht.2.le⟩⟩
      have hvmem : v ∈ s ∩ Ioc a v := ⟨hv, ⟨hav, le_rfl⟩⟩
      exact hsmall.dist_le htmem hvmem
    exact le_of_tendsto (hleft.dist tendsto_const_nhds) hbound
  have hdiff : Tendsto (fun v => f.leftLim v - f v)
      (𝓝[s] a) (𝓝 (0 : ℝ)) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).2
    simpa only [Real.dist_eq, Function.comp_def] using hdist
  rw [hfilter] at hlim ⊢
  have hsum := hdiff.add hlim
  convert hsum using 1
  · funext v
    ring
  · simp

/-- The glued radius-density and incoming-expansion sum has zero limit at
every adjacent axis point of the union. -/
theorem glued_item2_axis
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    (a : ℝ) :
    Tendsto (fun v => (gluedFields U₁ S₁ S₂).nu a v +
      (gluedFields U₁ S₁ S₂).lam a v)
      (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ U₁ ∪ U₂}) (𝓝 (0 : ℝ)) := by
  apply tendsto_union_axis_of_source_limits h₁.solution.development
    h₂.solution.development
  · intro x hx
    have hBV : BoundedVariationOn (S₁.lam x) {v | (x, v) ∈ U₁} :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h₁.item1.choose_spec.1 x)
    have hlim : Tendsto (fun v => S₁.lam x v + S₁.nu x v)
        (𝓝[>] x ⊓ 𝓟 {v | (x, v) ∈ U₁}) (𝓝 (0 : ℝ)) := by
      convert h₁.item2 x hx using 1
      funext v
      exact add_comm _ _
    have h := source_axis_tendsto_leftLim_add h₁.solution.development
      x hBV hlim
    exact h
  · intro x hx
    have hBV : BoundedVariationOn (S₂.lam x) {v | (x, v) ∈ U₂} :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h₂.item1.choose_spec.1 x)
    have hlim : Tendsto (fun v => S₂.lam x v + S₂.nu x v)
        (𝓝[>] x ⊓ 𝓟 {v | (x, v) ∈ U₂}) (𝓝 (0 : ℝ)) := by
      convert h₂.item2 x hx using 1
      funext v
      exact add_comm _ _
    have h := source_axis_tendsto_leftLim_add h₂.solution.development
      x hBV hlim
    exact h
  · intro p hp
    rw [(gluedFields_eq_first (S₂ := S₂) hp).2.2.2.1,
      (gluedFields_lam_alpha_eq_first (S₂ := S₂) hp).1]
    exact add_comm _ _
  · intro p hp
    rw [(gluedFields_eq_second h₁ h₂ hdata hp).2.2.2.1,
      (gluedFields_lam_alpha_eq_second h₁ h₂ hdata hp).1]
    exact add_comm _ _

/-- The glued scalar-density sum also has zero limit at every adjacent
axis point of the union. -/
theorem glued_item6_axis
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    (a : ℝ) :
    Tendsto (fun v => (gluedFields U₁ S₁ S₂).alpha a v +
      (gluedFields U₁ S₁ S₂).beta a v)
      (𝓝[>] a ⊓ 𝓟 {v | (a, v) ∈ U₁ ∪ U₂}) (𝓝 (0 : ℝ)) := by
  apply tendsto_union_axis_of_source_limits h₁.solution.development
    h₂.solution.development
  · intro x hx
    have hBV := source_alpha_bv_on_slice h₁ x
    have hlim : Tendsto (fun v => S₁.alpha x v + S₁.beta x v)
        (𝓝[>] x ⊓ 𝓟 {v | (x, v) ∈ U₁}) (𝓝 (0 : ℝ)) :=
      h₁.item6 x hx
    exact source_axis_tendsto_leftLim_add h₁.solution.development
      x hBV hlim
  · intro x hx
    have hBV := source_alpha_bv_on_slice h₂ x
    have hlim : Tendsto (fun v => S₂.alpha x v + S₂.beta x v)
        (𝓝[>] x ⊓ 𝓟 {v | (x, v) ∈ U₂}) (𝓝 (0 : ℝ)) :=
      h₂.item6 x hx
    exact source_axis_tendsto_leftLim_add h₂.solution.development
      x hBV hlim
  · intro p hp
    rw [(gluedFields_eq_first (S₂ := S₂) hp).2.2.2.2,
      (gluedFields_lam_alpha_eq_first (S₂ := S₂) hp).2]
  · intro p hp
    rw [(gluedFields_eq_second h₁ h₂ hdata hp).2.2.2.2,
      (gluedFields_lam_alpha_eq_second h₁ h₂ hdata hp).2]
end ChristodoulouBV.Uniqueness

end
