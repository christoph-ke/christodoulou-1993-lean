module

public import ChristodoulouBV.Uniqueness.UnionRepresentativesSwap
import ChristodoulouBV.BVSolution.PrimitiveCalculus

/-!
# Almost-everywhere agreement of outgoing densities

The canonical left traces agree almost everywhere with each source density
on its complete outgoing segments.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- A BV function agrees almost everywhere with its left-limit
representative on a compact outgoing interval. -/
theorem leftLim_ae_eq_of_bv_Ioc
    {f : ℝ → ℝ} {a b : ℝ} (_hab : a ≤ b)
    (hf : BoundedVariationOn f (Ioc a b)) :
    ∀ᵐ t ∂volume, t ∈ Ioc a b → f.leftLim t = f t := by
  have hdiff := hf.locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem
  have hneq : ∀ᵐ t : ℝ ∂volume, t ≠ b := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hdiff, hneq] with t ht hne hmem
  have htb : t < b := lt_of_le_of_ne hmem.2 hne
  have hcont : ContinuousAt f t :=
    ((ht hmem).differentiableAt (Ioc_mem_nhds hmem.1 htb)).continuousAt
  exact leftLim_eq_of_tendsto (hcont.tendsto.mono_left inf_le_left)

/-- On every outgoing segment in the first source, the chosen densities
agree almost everywhere with its original representatives. -/
theorem gluedFields_lam_alpha_ae_first
    {U₁ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁)
    {u v : ℝ} (hp : (u, v) ∈ U₁) :
    ∀ᵐ t ∂volume, t ∈ Ioc u v →
      (gluedFields U₁ S₁ S₂).lam u t = S₁.lam u t ∧
      (gluedFields U₁ S₁ S₂).alpha u t = S₁.alpha u t := by
  have huv := (h₁.solution.development.wedge hp).2
  have hslice : Ioc u v ⊆ {t | (u, t) ∈ U₁} := by
    intro t ht
    exact h₁.solution.development.outgoing_mem hp ht.1 ht.2
  have hLamBV : BoundedVariationOn (S₁.lam u) (Ioc u v) := by
    have hBV : BoundedVariationOn (S₁.lam u) {t | (u, t) ∈ U₁} :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (h₁.item1.choose_spec.1 u)
    exact hBV.mono hslice
  have hAlphaBV : BoundedVariationOn (S₁.alpha u) (Ioc u v) :=
    (source_alpha_bv_on_slice h₁ u).mono hslice
  filter_upwards [leftLim_ae_eq_of_bv_Ioc huv.le hLamBV,
    leftLim_ae_eq_of_bv_Ioc huv.le hAlphaBV] with t hLam hAlpha ht
  have htU := hslice ht
  obtain ⟨hlam, halpha⟩ := gluedFields_lam_alpha_eq_first htU
  exact ⟨hlam.trans (hLam ht), halpha.trans (hAlpha ht)⟩

/-- On every outgoing segment in the second source, the chosen densities
agree almost everywhere with its original representatives. -/
theorem gluedFields_lam_alpha_ae_second
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {u v : ℝ} (hp : (u, v) ∈ U₂) :
    ∀ᵐ t ∂volume, t ∈ Ioc u v →
      (gluedFields U₁ S₁ S₂).lam u t = S₂.lam u t ∧
      (gluedFields U₁ S₁ S₂).alpha u t = S₂.alpha u t := by
  have huv := (h₂.solution.development.wedge hp).2
  have hslice : Ioc u v ⊆ {t | (u, t) ∈ U₂} := by
    intro t ht
    exact h₂.solution.development.outgoing_mem hp ht.1 ht.2
  have hLamBV : BoundedVariationOn (S₂.lam u) (Ioc u v) := by
    have hBV : BoundedVariationOn (S₂.lam u) {t | (u, t) ∈ U₂} :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (h₂.item1.choose_spec.1 u)
    exact hBV.mono hslice
  have hAlphaBV : BoundedVariationOn (S₂.alpha u) (Ioc u v) :=
    (source_alpha_bv_on_slice h₂ u).mono hslice
  filter_upwards [leftLim_ae_eq_of_bv_Ioc huv.le hLamBV,
    leftLim_ae_eq_of_bv_Ioc huv.le hAlphaBV] with t hLam hAlpha ht
  have htU := hslice ht
  obtain ⟨hlam, halpha⟩ :=
    gluedFields_lam_alpha_eq_second h₁ h₂ hdata htU
  exact ⟨hlam.trans (hLam ht), halpha.trans (hAlpha ht)⟩

end ChristodoulouBV.Uniqueness

end
