module

public import ChristodoulouBV.Uniqueness.Comparison

/-!
# One-sided auxiliary-field traces on outgoing BV slices

These limits concern the given BV representatives only through their values
on the slice. They do not identify an exceptional value with either limit.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The outgoing expansion has a left limit within every outgoing BV slice. -/
theorem lam_left_limit_on_slice
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    (u x : ℝ) :
    ∃ l : ℝ, Tendsto (S.lam u)
      (𝓝[{v | (u, v) ∈ U} ∩ Iio x] x) (𝓝 l) := by
  have hBV : BoundedVariationOn (S.lam u) {v | (u, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item1.choose_spec.1 u)
  exact hBV.exists_tendsto_left x

/-- The outgoing expansion has a right limit within every outgoing BV slice. -/
theorem lam_right_limit_on_slice
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    (u x : ℝ) :
    ∃ l : ℝ, Tendsto (S.lam u)
      (𝓝[{v | (u, v) ∈ U} ∩ Ioi x] x) (𝓝 l) := by
  have hBV : BoundedVariationOn (S.lam u) {v | (u, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item1.choose_spec.1 u)
  exact hBV.exists_tendsto_right x

/-- The scalar-radius density has a left limit within every outgoing BV
slice, obtained from its `θ + λ φ` identity. -/
theorem alpha_left_limit_on_slice
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    (u x : ℝ) :
    ∃ l : ℝ, Tendsto (S.alpha u)
      (𝓝[{v | (u, v) ∈ U} ∩ Iio x] x) (𝓝 l) := by
  let F := 𝓝[{v | (u, v) ∈ U} ∩ Iio x] x
  obtain ⟨lLam, hLam⟩ := lam_left_limit_on_slice h u x
  have hBVθ : BoundedVariationOn (S.theta u) {v | (u, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item5.choose_spec.1 u)
  have hBVφ : BoundedVariationOn (S.phi u) {v | (u, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item3_variation.choose_spec.1 u)
  obtain ⟨lTheta, hTheta⟩ := hBVθ.exists_tendsto_left x
  obtain ⟨lPhi, hPhi⟩ := hBVφ.exists_tendsto_left x
  refine ⟨lTheta + lLam * lPhi, ?_⟩
  have hsum : Tendsto (fun v => S.theta u v + S.lam u v * S.phi u v)
      F (𝓝 (lTheta + lLam * lPhi)) := hTheta.add (hLam.mul hPhi)
  simpa only [F, Fields.theta, sub_add_cancel] using hsum

/-- The scalar-radius density has a right limit within every outgoing BV
slice. The given value at the base point need not equal that limit. -/
theorem alpha_right_limit_on_slice
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    (u x : ℝ) :
    ∃ l : ℝ, Tendsto (S.alpha u)
      (𝓝[{v | (u, v) ∈ U} ∩ Ioi x] x) (𝓝 l) := by
  let F := 𝓝[{v | (u, v) ∈ U} ∩ Ioi x] x
  obtain ⟨lLam, hLam⟩ := lam_right_limit_on_slice h u x
  have hBVθ : BoundedVariationOn (S.theta u) {v | (u, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item5.choose_spec.1 u)
  have hBVφ : BoundedVariationOn (S.phi u) {v | (u, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item3_variation.choose_spec.1 u)
  obtain ⟨lTheta, hTheta⟩ := hBVθ.exists_tendsto_right x
  obtain ⟨lPhi, hPhi⟩ := hBVφ.exists_tendsto_right x
  refine ⟨lTheta + lLam * lPhi, ?_⟩
  have hsum : Tendsto (fun v => S.theta u v + S.lam u v * S.phi u v)
      F (𝓝 (lTheta + lLam * lPhi)) := hTheta.add (hLam.mul hPhi)
  simpa only [F, Fields.theta, sub_add_cancel] using hsum

/-- An interior outgoing point of a full triangle has an actual neighborhood
in its BV slice. -/
theorem outgoing_slice_mem_nhds
    {U : Set (ℝ × ℝ)} {a b u x : ℝ}
    (hT : triangle a b ⊆ U) (hux : (u, x) ∈ triangle a b) :
    {v | (u, v) ∈ U} ∈ 𝓝 x := by
  have hsub : Ioo u b ⊆ {v | (u, v) ∈ U} := by
    intro v hv
    exact hT ((mem_triangle).2 ⟨hux.1, hv.1, hv.2⟩)
  exact mem_of_superset (isOpen_Ioo.mem_nhds ⟨hux.2.1, hux.2.2⟩) hsub

/-- Both auxiliary outgoing densities have ordinary one-sided limits at an
interior point of a full triangle. Their actual values there are unrestricted
by these limits. -/
theorem lam_alpha_one_sided_limits
    {U : Set (ℝ × ℝ)} {S : Fields} {a b u x : ℝ}
    (h : IsBVSolution U S) (hT : triangle a b ⊆ U)
    (hux : (u, x) ∈ triangle a b) :
    (∃ l : ℝ, Tendsto (S.lam u) (𝓝[<] x) (𝓝 l)) ∧
    (∃ l : ℝ, Tendsto (S.lam u) (𝓝[>] x) (𝓝 l)) ∧
    (∃ l : ℝ, Tendsto (S.alpha u) (𝓝[<] x) (𝓝 l)) ∧
    (∃ l : ℝ, Tendsto (S.alpha u) (𝓝[>] x) (𝓝 l)) := by
  have hmem := outgoing_slice_mem_nhds hT hux
  obtain ⟨l₁, hl₁⟩ := lam_left_limit_on_slice h u x
  obtain ⟨l₂, hl₂⟩ := lam_right_limit_on_slice h u x
  obtain ⟨l₃, hl₃⟩ := alpha_left_limit_on_slice h u x
  obtain ⟨l₄, hl₄⟩ := alpha_right_limit_on_slice h u x
  simp only [nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds hmem)]
    at hl₁ hl₂ hl₃ hl₄
  exact ⟨⟨l₁, hl₁⟩, ⟨l₂, hl₂⟩, ⟨l₃, hl₃⟩, ⟨l₄, hl₄⟩⟩

end ChristodoulouBV.Uniqueness

end
