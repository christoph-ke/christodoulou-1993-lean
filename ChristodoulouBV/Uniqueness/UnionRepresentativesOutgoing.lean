module

public import ChristodoulouBV.Uniqueness.UnionRepresentativesAE

/-!
# Outgoing characteristic primitives on the union

The source containing the upper outgoing endpoint contains the entire
segment. The canonical densities agree almost everywhere with that source,
so the radius and scalar-radius primitives transfer directly.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- A closed-segment primitive transfers across pointwise equality of its
primary field and almost-everywhere equality of its density. -/
theorem IntervalPrimitive.congr_on_segment
    {F F' g g' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hprim : IntervalPrimitive F g a b)
    (hF : EqOn F F' (Icc a b))
    (hg : ∀ᵐ t ∂volume, t ∈ Ioc a b → g t = g' t) :
    IntervalPrimitive F' g' a b := by
  have hgAE : g =ᵐ[volume.restrict (Ι a b)] g' := by
    rw [uIoc_of_le hab]
    exact (ae_restrict_iff' measurableSet_Ioc).mpr hg
  have hInt : IntervalIntegrable g' volume a b := hprim.1.congr_ae hgAE
  have hIntegral : (∫ t in a..b, g t) = ∫ t in a..b, g' t := by
    apply intervalIntegral.integral_congr_ae
    simpa only [uIoc_of_le hab] using hg
  exact ⟨hInt, by rw [← hF ⟨hab, le_rfl⟩, ← hF ⟨le_rfl, hab⟩,
    ← hIntegral]; exact hprim.2⟩

/-- The selected radius and scalar-radius fields satisfy both outgoing
derivative primitives on every closed outgoing union segment. -/
theorem gluedFields_radius_scalar_out
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {u a b : ℝ} (hab : a ≤ b)
    (hseg : outSeg u a b ⊆ U₁ ∪ U₂) :
    IntervalPrimitive ((gluedFields U₁ S₁ S₂).r u)
      ((gluedFields U₁ S₁ S₂).lam u) a b ∧
    IntervalPrimitive
      (fun t => (gluedFields U₁ S₁ S₂).r u t *
        (gluedFields U₁ S₁ S₂).phi u t)
      ((gluedFields U₁ S₁ S₂).alpha u) a b := by
  have ha : (u, a) ∈ U₁ ∪ U₂ := hseg (by
    change u ∈ ({u} : Set ℝ) ∧ a ∈ Icc a b
    exact ⟨rfl, ⟨le_rfl, hab⟩⟩)
  have hua : u < a := by
    rcases ha with ha₁ | ha₂
    · exact (h₁.solution.development.wedge ha₁).2
    · exact (h₂.solution.development.wedge ha₂).2
  have hb : (u, b) ∈ U₁ ∪ U₂ := hseg (by
    change u ∈ ({u} : Set ℝ) ∧ b ∈ Icc a b
    exact ⟨rfl, ⟨hab, le_rfl⟩⟩)
  rcases hb with hb₁ | hb₂
  · have hseg₁ := h₁.solution.development.out_seg_subset hb₁ hua hab le_rfl
    have hprimR := h₁.solution.radius_out u a b hab hseg₁
    have hprimP := h₁.solution.scalar_radius_out u a b hab hseg₁
    have heq (t : ℝ) (ht : t ∈ Icc a b) :=
      gluedFields_eq_first (S₁ := S₁) (S₂ := S₂) (hseg₁ (by
        change u ∈ ({u} : Set ℝ) ∧ t ∈ Icc a b
        exact ⟨rfl, ht⟩))
    have hae := gluedFields_lam_alpha_ae_first (S₂ := S₂) h₁ hb₁
    have hae' : ∀ᵐ t ∂volume, t ∈ Ioc a b →
        (gluedFields U₁ S₁ S₂).lam u t = S₁.lam u t ∧
        (gluedFields U₁ S₁ S₂).alpha u t = S₁.alpha u t := by
      filter_upwards [hae] with t ht htab
      exact ht ⟨hua.trans htab.1, htab.2⟩
    have hLamAE : ∀ᵐ t ∂volume, t ∈ Ioc a b →
        S₁.lam u t = (gluedFields U₁ S₁ S₂).lam u t :=
      hae'.mono (fun _ ht hmem => (ht hmem).1.symm)
    have hAlphaAE : ∀ᵐ t ∂volume, t ∈ Ioc a b →
        S₁.alpha u t = (gluedFields U₁ S₁ S₂).alpha u t :=
      hae'.mono (fun _ ht hmem => (ht hmem).2.symm)
    exact ⟨IntervalPrimitive.congr_on_segment hab hprimR
      (fun t ht => (heq t ht).1.symm) hLamAE,
      IntervalPrimitive.congr_on_segment hab hprimP
        (fun t ht => by rw [(heq t ht).1, (heq t ht).2.1]) hAlphaAE⟩
  · have hseg₂ := h₂.solution.development.out_seg_subset hb₂ hua hab le_rfl
    have hprimR := h₂.solution.radius_out u a b hab hseg₂
    have hprimP := h₂.solution.scalar_radius_out u a b hab hseg₂
    have heq (t : ℝ) (ht : t ∈ Icc a b) :=
      gluedFields_eq_second h₁ h₂ hdata (hseg₂ (by
        change u ∈ ({u} : Set ℝ) ∧ t ∈ Icc a b
        exact ⟨rfl, ht⟩))
    have hae := gluedFields_lam_alpha_ae_second h₁ h₂ hdata hb₂
    have hae' : ∀ᵐ t ∂volume, t ∈ Ioc a b →
        (gluedFields U₁ S₁ S₂).lam u t = S₂.lam u t ∧
        (gluedFields U₁ S₁ S₂).alpha u t = S₂.alpha u t := by
      filter_upwards [hae] with t ht htab
      exact ht ⟨hua.trans htab.1, htab.2⟩
    have hLamAE : ∀ᵐ t ∂volume, t ∈ Ioc a b →
        S₂.lam u t = (gluedFields U₁ S₁ S₂).lam u t :=
      hae'.mono (fun _ ht hmem => (ht hmem).1.symm)
    have hAlphaAE : ∀ᵐ t ∂volume, t ∈ Ioc a b →
        S₂.alpha u t = (gluedFields U₁ S₁ S₂).alpha u t :=
      hae'.mono (fun _ ht hmem => (ht hmem).2.symm)
    exact ⟨IntervalPrimitive.congr_on_segment hab hprimR
      (fun t ht => (heq t ht).1.symm) hLamAE,
      IntervalPrimitive.congr_on_segment hab hprimP
        (fun t ht => by rw [(heq t ht).1, (heq t ht).2.1]) hAlphaAE⟩

end ChristodoulouBV.Uniqueness

end
