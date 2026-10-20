module

public import ChristodoulouBV.Uniqueness.UnionEquationsIncomingMassBound

/-!
# Incoming mass equation at mixed terminal levels

The source mass equation passes to a mixed top segment by dominated
convergence. The denominator stays nonzero because the incoming expansion is
strictly negative at every union point.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The selected incoming expansion is strictly negative at every point of
the union. -/
theorem gluedFields_nu_neg
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {u v : ℝ} (hp : (u, v) ∈ U₁ ∪ U₂) :
    (gluedFields U₁ S₁ S₂).nu u v < 0 := by
  rcases hp with hp₁ | hp₂
  · rw [(gluedFields_eq_first (S₂ := S₂) hp₁).2.2.2.1]
    obtain ⟨c, hc, hlow⟩ := h₁.lam_bounded_below
    have hn := h₁.nu_le_neg_lower hc hlow hp₁
    linarith
  · rw [(gluedFields_eq_second h₁ h₂ hdata hp₂).2.2.2.1]
    obtain ⟨c, hc, hlow⟩ := h₂.lam_bounded_below
    have hn := h₂.nu_le_neg_lower hc hlow hp₂
    linarith

/-- The first source's incoming mass density converges pointwise to the
selected mass density at every point of a mixed terminal segment. -/
theorem first_source_mass_in_density_tendsto_mixed_top
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b s : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) (hb : (b, v) ∈ U₁)
    (hs : s ∈ Icc a b) :
    Tendsto
      (fun t => (1 - 2 * S₁.m s t / S₁.r s t) * (S₁.zeta s t) ^ 2 /
        (2 * S₁.nu s t))
      (𝓝[<] v)
      (𝓝 ((1 - 2 * (gluedFields U₁ S₁ S₂).m s v /
        (gluedFields U₁ S₁ S₂).r s v) *
        ((gluedFields U₁ S₁ S₂).zeta s v) ^ 2 /
        (2 * (gluedFields U₁ S₁ S₂).nu s v))) := by
  let G := gluedFields U₁ S₁ S₂
  obtain ⟨hr, hphi, hm, hnu, hbeta⟩ :=
    first_source_fields_tendsto_mixed_top h₁ h₂ hdata hab hseg hb hs
  have htop : (s, v) ∈ U₁ ∪ U₂ := hseg (by
    change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨hs, rfl⟩)
  have hr0 : G.r s v ≠ 0 :=
    ne_of_gt (gluedFields_radius_pos_mass_gap_pos h₁ h₂ hdata htop).1
  have hnu0 : 2 * G.nu s v ≠ 0 := by
    have hn := gluedFields_nu_neg h₁ h₂ hdata htop
    exact mul_ne_zero (by norm_num) (ne_of_lt hn)
  have hzeta : Tendsto (fun t => S₁.zeta s t) (𝓝[<] v)
      (𝓝 (G.zeta s v)) := by
    simpa only [Fields.zeta] using hbeta.sub (hnu.mul hphi)
  have hratio : Tendsto (fun t => 2 * S₁.m s t / S₁.r s t)
      (𝓝[<] v) (𝓝 (2 * G.m s v / G.r s v)) :=
    (tendsto_const_nhds.mul hm).div hr hr0
  have htopdens : Tendsto
      (fun t => (1 - 2 * S₁.m s t / S₁.r s t) * (S₁.zeta s t) ^ 2 /
        (2 * S₁.nu s t)) (𝓝[<] v)
      (𝓝 ((1 - 2 * G.m s v / G.r s v) * (G.zeta s v) ^ 2 /
        (2 * G.nu s v))) :=
    ((tendsto_const_nhds.sub hratio).mul (hzeta.pow 2)).div
      (tendsto_const_nhds.mul hnu) hnu0
  exact htopdens

/-- The incoming mass primitive holds across a mixed terminal segment whose
upper endpoint belongs to the first source. -/
theorem first_source_mass_in_mixed_top
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) (hb : (b, v) ∈ U₁) :
    IntervalPrimitive (fun s => (gluedFields U₁ S₁ S₂).m s v)
      (fun s => (1 - 2 * (gluedFields U₁ S₁ S₂).m s v /
        (gluedFields U₁ S₁ S₂).r s v) *
        ((gluedFields U₁ S₁ S₂).zeta s v) ^ 2 /
        (2 * (gluedFields U₁ S₁ S₂).nu s v)) a b := by
  let G := gluedFields U₁ S₁ S₂
  have ha : (a, v) ∈ U₁ ∪ U₂ := hseg (by
    change a ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨⟨le_rfl, hab⟩, rfl⟩)
  have ha0 : 0 ≤ a := by
    rcases ha with ha₁ | ha₂
    · exact (h₁.solution.development.wedge ha₁).1
    · exact (h₂.solution.development.wedge ha₂).1
  have hbv : b < v := (h₁.solution.development.wedge hb).2
  have hstrip : ∀ᶠ t in 𝓝[<] v, inSeg t a b ⊆ U₁ := by
    filter_upwards [Ioo_mem_nhdsLT hbv] with t ht
    exact h₁.solution.development.in_seg_subset hb ha0 hab le_rfl ht.1 ht.2
  have hsource : ∀ᶠ t in 𝓝[<] v,
      IntervalPrimitive (fun s => S₁.m s t)
        (fun s => (1 - 2 * S₁.m s t / S₁.r s t) *
          (S₁.zeta s t) ^ 2 / (2 * S₁.nu s t)) a b :=
    hstrip.mono (fun t ht => h₁.solution.mass_in t a b hab ht)
  obtain ⟨C, hC, hbound⟩ :=
    first_source_mass_in_density_uniform_below_top h₁ h₂ hdata hab hseg hb
  obtain ⟨hTargetInt, hIntegralLimit⟩ :=
    intervalIntegrable_and_tendsto_integral_of_eventually_bounded
      hab (hsource.mono (fun _ ht => ht.1)) ⟨C, hC, hbound⟩
      (fun s hs => first_source_mass_in_density_tendsto_mixed_top
        h₁ h₂ hdata hab hseg hb hs)
  have hA := (first_source_fields_tendsto_mixed_top h₁ h₂ hdata
    hab hseg hb ⟨le_rfl, hab⟩).2.2.1
  have hB := (first_source_fields_tendsto_mixed_top h₁ h₂ hdata
    hab hseg hb ⟨hab, le_rfl⟩).2.2.1
  have hEqEv : ∀ᶠ t in 𝓝[<] v,
      S₁.m b t - S₁.m a t =
        ∫ s in a..b, (1 - 2 * S₁.m s t / S₁.r s t) *
          (S₁.zeta s t) ^ 2 / (2 * S₁.nu s t) :=
    hsource.mono (fun _ ht => ht.2)
  have hEq : G.m b v - G.m a v =
      ∫ s in a..b, (1 - 2 * G.m s v / G.r s v) *
        (G.zeta s v) ^ 2 / (2 * G.nu s v) := by
    have hleft := hB.sub hA
    have hright := hIntegralLimit.congr' (hEqEv.mono fun _ ht => ht.symm)
    exact tendsto_nhds_unique hleft hright
  exact ⟨hTargetInt, hEq⟩

end ChristodoulouBV.Uniqueness

end
