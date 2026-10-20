module

public import ChristodoulouBV.Uniqueness.UnionRepresentativesCoefficient

/-!
# Incoming coefficient limits at mixed terminal segments

The source coefficient converges pointwise to the coefficient of the chosen
union fields. The strip bound in the preceding module then permits dominated
convergence in the incoming primitive equations.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The chosen primary fields have positive radius and mass gap at every
point of the union. -/
theorem gluedFields_radius_pos_mass_gap_pos
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {u v : ℝ} (hp : (u, v) ∈ U₁ ∪ U₂) :
    0 < (gluedFields U₁ S₁ S₂).r u v ∧
      0 < 1 - 2 * (gluedFields U₁ S₁ S₂).m u v /
        (gluedFields U₁ S₁ S₂).r u v := by
  rcases hp with hp₁ | hp₂
  · obtain ⟨hr, _, hm, _, _⟩ := gluedFields_eq_first hp₁
    rw [hr, hm]
    have hgap := (h₁.mass_ratio_bounds hp₁).2
    exact ⟨h₁.solution.radius_pos (u, v) hp₁, by linarith⟩
  · obtain ⟨hr, _, hm, _, _⟩ := gluedFields_eq_second h₁ h₂ hdata hp₂
    rw [hr, hm]
    have hgap := (h₂.mass_ratio_bounds hp₂).2
    exact ⟨h₂.solution.radius_pos (u, v) hp₂, by linarith⟩

/-- The mixed coefficient of the source containing the upper incoming
endpoint converges to the coefficient of the selected union fields. -/
theorem first_source_radiusCoeff_tendsto_mixed_top
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b s : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) (hb : (b, v) ∈ U₁)
    (hs : s ∈ Icc a b) :
    Tendsto (fun t => IsBVSolution.radiusCoeff S₁ s t) (𝓝[<] v)
      (𝓝 (IsBVSolution.radiusCoeff (gluedFields U₁ S₁ S₂) s v)) ∧
    Tendsto (fun t => IsBVSolution.radiusCoeff S₁ s t * S₁.phi s t)
      (𝓝[<] v)
      (𝓝 (IsBVSolution.radiusCoeff (gluedFields U₁ S₁ S₂) s v *
        (gluedFields U₁ S₁ S₂).phi s v)) := by
  let G := gluedFields U₁ S₁ S₂
  have hp : (s, v) ∈ U₁ ∪ U₂ := hseg (by
    change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨hs, rfl⟩)
  have ⟨hrpos, hgappos⟩ :=
    gluedFields_radius_pos_mass_gap_pos h₁ h₂ hdata hp
  obtain ⟨hr, hphi, hm, hnu, _⟩ :=
    first_source_fields_tendsto_mixed_top h₁ h₂ hdata hab hseg hb hs
  obtain ⟨hlam, _⟩ :=
    first_source_lam_alpha_tendsto_mixed_top h₁ h₂ hdata hab hseg hb hs
  have hratio : Tendsto (fun t => 2 * S₁.m s t / S₁.r s t)
      (𝓝[<] v) (𝓝 (2 * G.m s v / G.r s v)) :=
    (tendsto_const_nhds.mul hm).div hr (ne_of_gt hrpos)
  have hgap : Tendsto (fun t => 1 - 2 * S₁.m s t / S₁.r s t)
      (𝓝[<] v) (𝓝 (1 - 2 * G.m s v / G.r s v)) :=
    tendsto_const_nhds.sub hratio
  have hden : Tendsto
      (fun t => (1 - 2 * S₁.m s t / S₁.r s t) * S₁.r s t)
      (𝓝[<] v) (𝓝 ((1 - 2 * G.m s v / G.r s v) * G.r s v)) :=
    hgap.mul hr
  have hnum : Tendsto
      (fun t => (2 * S₁.m s t / S₁.r s t) * S₁.lam s t * S₁.nu s t)
      (𝓝[<] v) (𝓝 ((2 * G.m s v / G.r s v) * G.lam s v * G.nu s v)) :=
    (hratio.mul hlam).mul hnu
  have hcoeff := hnum.div hden (ne_of_gt (mul_pos hgappos hrpos))
  have hfun (f g : ℝ → ℝ) : f / g = fun t => f t / g t := by
    funext t
    exact Pi.div_apply f g t
  rw [hfun] at hcoeff
  have hcoeff' : Tendsto (fun t => IsBVSolution.radiusCoeff S₁ s t)
      (𝓝[<] v) (𝓝 (IsBVSolution.radiusCoeff G s v)) := by
    simpa only [IsBVSolution.radiusCoeff] using hcoeff
  exact ⟨hcoeff', hcoeff'.mul hphi⟩

end ChristodoulouBV.Uniqueness

end
