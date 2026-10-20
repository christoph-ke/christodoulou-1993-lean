module

public import ChristodoulouBV.Uniqueness.UnionRepresentativesIncomingPrimitives

/-!
# Outgoing mass and transport equations on the union

The primary and incoming fields agree pointwise with the source containing
the upper endpoint. The outgoing densities agree almost everywhere, which is
enough to transfer all remaining outgoing primitive equations.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- Transfer the outgoing mass, incoming-expansion, and incoming-density
equations along one source segment with the canonical representative. -/
theorem outgoing_mass_nu_beta_of_source_agreement
    {U : Set (ℝ × ℝ)} {S G : Fields}
    (h : IsBVSolution U S) {u a b : ℝ} (hab : a ≤ b)
    (hseg : outSeg u a b ⊆ U)
    (hfields : ∀ t ∈ Icc a b,
      G.r u t = S.r u t ∧ G.phi u t = S.phi u t ∧
      G.m u t = S.m u t ∧ G.nu u t = S.nu u t ∧
      G.beta u t = S.beta u t)
    (hdens : ∀ᵐ t ∂volume, t ∈ Ioc a b →
      G.lam u t = S.lam u t ∧ G.alpha u t = S.alpha u t) :
    IntervalPrimitive (G.m u)
      (fun t => (1 - 2 * G.m u t / G.r u t) * (G.theta u t) ^ 2 /
        (2 * G.lam u t)) a b ∧
    IntervalPrimitive (G.nu u)
      (fun t => IsBVSolution.radiusCoeff G u t) a b ∧
    IntervalPrimitive (G.beta u)
      (fun t => IsBVSolution.radiusCoeff G u t * G.phi u t) a b := by
  have hEqMass : EqOn (S.m u) (G.m u) (Icc a b) :=
    fun t ht => (hfields t ht).2.2.1.symm
  have hEqNu : EqOn (S.nu u) (G.nu u) (Icc a b) :=
    fun t ht => (hfields t ht).2.2.2.1.symm
  have hEqBeta : EqOn (S.beta u) (G.beta u) (Icc a b) :=
    fun t ht => (hfields t ht).2.2.2.2.symm
  have hCoeffAE : ∀ᵐ t ∂volume, t ∈ Ioc a b →
      IsBVSolution.radiusCoeff S u t =
        IsBVSolution.radiusCoeff G u t := by
    filter_upwards [hdens] with t ht htab
    obtain ⟨hr, _, hm, hnu, _⟩ := hfields t ⟨htab.1.le, htab.2⟩
    obtain ⟨hlam, _⟩ := ht htab
    simp only [IsBVSolution.radiusCoeff, ← hr, ← hm, ← hnu, ← hlam]
  have hCoeffPhiAE : ∀ᵐ t ∂volume, t ∈ Ioc a b →
      IsBVSolution.radiusCoeff S u t * S.phi u t =
        IsBVSolution.radiusCoeff G u t * G.phi u t := by
    filter_upwards [hCoeffAE] with t ht htab
    rw [ht htab, (hfields t ⟨htab.1.le, htab.2⟩).2.1.symm]
  have hMassAE : ∀ᵐ t ∂volume, t ∈ Ioc a b →
      (1 - 2 * S.m u t / S.r u t) * (S.theta u t) ^ 2 /
        (2 * S.lam u t) =
      (1 - 2 * G.m u t / G.r u t) * (G.theta u t) ^ 2 /
        (2 * G.lam u t) := by
    filter_upwards [hdens] with t ht htab
    obtain ⟨hr, hphi, hm, _, _⟩ := hfields t ⟨htab.1.le, htab.2⟩
    obtain ⟨hlam, halpha⟩ := ht htab
    simp only [Fields.theta, ← hr, ← hphi, ← hm, ← hlam, ← halpha]
  have hMass := h.solution.mass_out u a b hab hseg
  have hNu : IntervalPrimitive (S.nu u)
      (fun t => IsBVSolution.radiusCoeff S u t) a b :=
    h.solution.nu_out u a b hab hseg
  have hBeta : IntervalPrimitive (S.beta u)
      (fun t => IsBVSolution.radiusCoeff S u t * S.phi u t) a b :=
    h.solution.beta_out u a b hab hseg
  exact ⟨IntervalPrimitive.congr_on_segment hab hMass hEqMass hMassAE,
    IntervalPrimitive.congr_on_segment hab hNu hEqNu hCoeffAE,
    IntervalPrimitive.congr_on_segment hab hBeta hEqBeta hCoeffPhiAE⟩

/-- The three remaining outgoing primitive equations hold on every closed
outgoing segment contained in the union. -/
theorem gluedFields_mass_nu_beta_out
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {u a b : ℝ} (hab : a ≤ b)
    (hseg : outSeg u a b ⊆ U₁ ∪ U₂) :
    IntervalPrimitive ((gluedFields U₁ S₁ S₂).m u)
      (fun t => (1 - 2 * (gluedFields U₁ S₁ S₂).m u t /
        (gluedFields U₁ S₁ S₂).r u t) *
        ((gluedFields U₁ S₁ S₂).theta u t) ^ 2 /
        (2 * (gluedFields U₁ S₁ S₂).lam u t)) a b ∧
    IntervalPrimitive ((gluedFields U₁ S₁ S₂).nu u)
      (fun t => IsBVSolution.radiusCoeff (gluedFields U₁ S₁ S₂) u t) a b ∧
    IntervalPrimitive ((gluedFields U₁ S₁ S₂).beta u)
      (fun t => IsBVSolution.radiusCoeff (gluedFields U₁ S₁ S₂) u t *
        (gluedFields U₁ S₁ S₂).phi u t) a b := by
  let G := gluedFields U₁ S₁ S₂
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
    have hfields (t : ℝ) (ht : t ∈ Icc a b) :=
      gluedFields_eq_first (S₁ := S₁) (S₂ := S₂) (hseg₁ (by
        change u ∈ ({u} : Set ℝ) ∧ t ∈ Icc a b
        exact ⟨rfl, ht⟩))
    have hae := gluedFields_lam_alpha_ae_first (S₂ := S₂) h₁ hb₁
    have hae' : ∀ᵐ t ∂volume, t ∈ Ioc a b →
        G.lam u t = S₁.lam u t ∧ G.alpha u t = S₁.alpha u t := by
      filter_upwards [hae] with t ht htab
      exact ht ⟨hua.trans htab.1, htab.2⟩
    exact outgoing_mass_nu_beta_of_source_agreement h₁ hab hseg₁ hfields hae'
  · have hseg₂ := h₂.solution.development.out_seg_subset hb₂ hua hab le_rfl
    have hfields (t : ℝ) (ht : t ∈ Icc a b) :=
      gluedFields_eq_second h₁ h₂ hdata (hseg₂ (by
        change u ∈ ({u} : Set ℝ) ∧ t ∈ Icc a b
        exact ⟨rfl, ht⟩))
    have hae := gluedFields_lam_alpha_ae_second h₁ h₂ hdata hb₂
    have hae' : ∀ᵐ t ∂volume, t ∈ Ioc a b →
        G.lam u t = S₂.lam u t ∧ G.alpha u t = S₂.alpha u t := by
      filter_upwards [hae] with t ht htab
      exact ht ⟨hua.trans htab.1, htab.2⟩
    exact outgoing_mass_nu_beta_of_source_agreement h₂ hab hseg₂ hfields hae'

end ChristodoulouBV.Uniqueness

end
