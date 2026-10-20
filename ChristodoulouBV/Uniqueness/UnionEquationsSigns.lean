module

public import ChristodoulouBV.Uniqueness.UnionEquationsIncomingMassUnion

/-!
# Signs and conformal factor on the union

The left-trace outgoing expansion inherits the source's strict global lower
bound. The remaining pointwise signs supply a positive conformal factor.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- A positive lower bound for an outgoing source expansion also bounds its
left trace at every point of the source. -/
theorem source_lam_leftLim_ge_lower
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {c u v : ℝ}
    (hlow : ∀ p ∈ U, c ≤ S.lam p.1 p.2)
    (hp : (u, v) ∈ U) :
    c ≤ (S.lam u).leftLim v := by
  have huv := (h.solution.development.wedge hp).2
  have hslice : Ioc u v ⊆ {t | (u, t) ∈ U} := by
    intro t ht
    exact h.solution.development.outgoing_mem hp ht.1 ht.2
  have hBV : BoundedVariationOn (S.lam u) (Ioc u v) := by
    have hBV' : BoundedVariationOn (S.lam u) {t | (u, t) ∈ U} :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item1.choose_spec.1 u)
    exact hBV'.mono hslice
  have hlim := leftLim_tendsto_of_bv_Ioc huv hBV
  have hbound : ∀ᶠ t in 𝓝[<] v, c ≤ S.lam u t := by
    filter_upwards [Ioo_mem_nhdsLT huv] with t ht
    exact hlow (u, t) (h.solution.development.outgoing_mem hp ht.1 ht.2.le)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hbound

/-- The selected outgoing expansion is strictly positive on the union. -/
theorem gluedFields_lam_pos
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {u v : ℝ} (hp : (u, v) ∈ U₁ ∪ U₂) :
    0 < (gluedFields U₁ S₁ S₂).lam u v := by
  rcases hp with hp₁ | hp₂
  · obtain ⟨c, hc, hlow⟩ := h₁.lam_bounded_below
    rw [(gluedFields_lam_alpha_eq_first (S₂ := S₂) hp₁).1]
    exact hc.trans_le (source_lam_leftLim_ge_lower h₁ hlow hp₁)
  · obtain ⟨c, hc, hlow⟩ := h₂.lam_bounded_below
    rw [(gluedFields_lam_alpha_eq_second h₁ h₂ hdata hp₂).1]
    exact hc.trans_le (source_lam_leftLim_ge_lower h₂ hlow hp₂)

/-- The selected fields admit a positive conformal factor at every point of
the union. -/
theorem gluedFields_conformal
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {u v : ℝ} (hp : (u, v) ∈ U₁ ∪ U₂) :
    ∃ Ω : ℝ, 0 < Ω ∧
      (1 - 2 * (gluedFields U₁ S₁ S₂).m u v /
        (gluedFields U₁ S₁ S₂).r u v) * Ω ^ 2 =
        -(4 * (gluedFields U₁ S₁ S₂).lam u v *
          (gluedFields U₁ S₁ S₂).nu u v) := by
  let G := gluedFields U₁ S₁ S₂
  have hgap := (gluedFields_radius_pos_mass_gap_pos h₁ h₂ hdata hp).2
  have hlam := gluedFields_lam_pos h₁ h₂ hdata hp
  have hnu := gluedFields_nu_neg h₁ h₂ hdata hp
  let q := -(4 * G.lam u v * G.nu u v) / (1 - 2 * G.m u v / G.r u v)
  have hq : 0 < q := by
    dsimp [q]
    apply div_pos _ hgap
    have hneg : 0 < -G.nu u v := neg_pos.mpr hnu
    have : 0 < 4 * G.lam u v * (-G.nu u v) := by positivity
    nlinarith
  refine ⟨Real.sqrt q, Real.sqrt_pos.2 hq, ?_⟩
  rw [Real.sq_sqrt hq.le]
  dsimp [q]
  exact mul_div_cancel₀ _ (ne_of_gt hgap)

end ChristodoulouBV.Uniqueness

end
