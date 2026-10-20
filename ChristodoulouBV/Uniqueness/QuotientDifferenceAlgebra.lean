module

public import ChristodoulouBV.Uniqueness.QuotientEquations

/-!
# Algebra of the scalar quotient difference equations

These identities expand the compact a.e. quotient equations into the terms
printed before (3.20) and (3.21), including the weighted mass-ratio term.
-/

@[expose] public section

namespace ChristodoulouBV.Uniqueness

private theorem alpha_alg
    {m1 m2 r1 r2 l1 l2 n1 n2 t1 t2 : ℝ}
    (hr1 : r1 ≠ 0) (hr2 : r2 ≠ 0)
    (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0)
    (hg1 : 1 - m1 ≠ 0) (hg2 : 1 - m2 ≠ 0) :
    -(m1 * l1 * n1 / ((1 - m1) * r1)) * t1 / l1 ^ 2 +
      (m2 * l2 * n2 / ((1 - m2) * r2)) * t2 / l2 ^ 2 =
      -m1 / (1 - m1) * (n1 / l1) * ((t1 - t2) / r1) -
      m1 / (1 - m1) * (t2 / r2) * (1 / l1) *
        ((n1 - n2) - (n2 / l2) * (l1 - l2)) +
      m1 / (1 - m1) * (t2 * n1 / (r2 * l1)) * ((r1 - r2) / r1) -
      (n2 / l2) * (t2 / r2) * ((m1 - m2) / ((1 - m1) * (1 - m2))) := by
  field_simp [hr1, hr2, hl1, hl2, hg1, hg2]
  ring

private theorem beta_alg
    {m1 m2 r1 r2 l1 l2 n1 n2 z1 z2 : ℝ}
    (hr1 : r1 ≠ 0) (hr2 : r2 ≠ 0)
    (hn1 : n1 ≠ 0) (hn2 : n2 ≠ 0)
    (hg1 : 1 - m1 ≠ 0) (hg2 : 1 - m2 ≠ 0) :
    -(m1 * l1 * n1 / ((1 - m1) * r1)) * z1 / n1 ^ 2 +
      (m2 * l2 * n2 / ((1 - m2) * r2)) * z2 / n2 ^ 2 =
      -m1 / (1 - m1) * (l1 / n1) * ((z1 - z2) / r1) -
      m1 / (1 - m1) * (z2 / r2) * (1 / n1) *
        ((l1 - l2) - (l2 / n2) * (n1 - n2)) +
      m1 / (1 - m1) * (z2 * l1 / (r2 * n1)) * ((r1 - r2) / r1) -
      (l2 / n2) * (z2 / r2) * ((m1 - m2) / ((1 - m1) * (1 - m2))) := by
  field_simp [hr1, hr2, hn1, hn2, hg1, hg2]
  ring

/-- The four forcing terms in the incoming `α/λ` difference equation on
pp. 1154–1155, with the corrected mass ratio identity (3.9). -/
noncomputable def alphaRatioForcing (D : ComparisonData) (u v : ℝ) : ℝ :=
  let μ₁ := IsBVSolution.mu D.S₁ u v;
  let μ₂ := IsBVSolution.mu D.S₂ u v;
  -μ₁ / (1 - μ₁) * (D.S₁.nu u v / D.S₁.lam u v) *
      ((D.S₁.theta u v - D.S₂.theta u v) / D.S₁.r u v) -
    μ₁ / (1 - μ₁) * (D.S₂.theta u v / D.S₂.r u v) *
      (1 / D.S₁.lam u v) *
      ((D.S₁.nu u v - D.S₂.nu u v) -
        (D.S₂.nu u v / D.S₂.lam u v) *
          (D.S₁.lam u v - D.S₂.lam u v)) +
    μ₁ / (1 - μ₁) *
      (D.S₂.theta u v * D.S₁.nu u v /
        (D.S₂.r u v * D.S₁.lam u v)) *
      ((D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v) -
    (D.S₂.nu u v / D.S₂.lam u v) *
      (D.S₂.theta u v / D.S₂.r u v) *
      ((μ₁ - μ₂) / ((1 - μ₁) * (1 - μ₂)))

/-- The four forcing terms in the outgoing `β/ν` difference equation on
pp. 1154–1155. -/
noncomputable def betaRatioForcing (D : ComparisonData) (u v : ℝ) : ℝ :=
  let μ₁ := IsBVSolution.mu D.S₁ u v;
  let μ₂ := IsBVSolution.mu D.S₂ u v;
  -μ₁ / (1 - μ₁) * (D.S₁.lam u v / D.S₁.nu u v) *
      ((D.S₁.zeta u v - D.S₂.zeta u v) / D.S₁.r u v) -
    μ₁ / (1 - μ₁) * (D.S₂.zeta u v / D.S₂.r u v) *
      (1 / D.S₁.nu u v) *
      ((D.S₁.lam u v - D.S₂.lam u v) -
        (D.S₂.lam u v / D.S₂.nu u v) *
          (D.S₁.nu u v - D.S₂.nu u v)) +
    μ₁ / (1 - μ₁) *
      (D.S₂.zeta u v * D.S₁.lam u v /
        (D.S₂.r u v * D.S₁.nu u v)) *
      ((D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v) -
    (D.S₂.lam u v / D.S₂.nu u v) *
      (D.S₂.zeta u v / D.S₂.r u v) *
      ((μ₁ - μ₂) / ((1 - μ₁) * (1 - μ₂)))

/-- Pointwise algebra converting the compact incoming quotient derivative
to the printed four-term difference equation. -/
theorem ComparisonData.alpha_ratio_forcing_algebra (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    -IsBVSolution.radiusCoeff D.S₁ u v * D.S₁.theta u v /
        D.S₁.lam u v ^ 2 +
      IsBVSolution.radiusCoeff D.S₂ u v * D.S₂.theta u v /
        D.S₂.lam u v ^ 2 = alphaRatioForcing D u v := by
  have hp := D.hT huv
  have hr₁ := (D.h₁.solution.radius_pos (u, v) hp.1).ne'
  have hr₂ := (D.h₂.solution.radius_pos (u, v) hp.2).ne'
  have hl₁ := (D.h₁.solution.lam_pos (u, v) hp.1).ne'
  have hl₂ := (D.h₂.solution.lam_pos (u, v) hp.2).ne'
  have hg₁ : 1 - IsBVSolution.mu D.S₁ u v ≠ 0 := by
    have hmu := (D.h₁.mass_ratio_bounds hp.1).2
    change IsBVSolution.mu D.S₁ u v < 1 at hmu
    linarith
  have hg₂ : 1 - IsBVSolution.mu D.S₂ u v ≠ 0 := by
    have hmu := (D.h₂.mass_ratio_bounds hp.2).2
    change IsBVSolution.mu D.S₂ u v < 1 at hmu
    linarith
  unfold alphaRatioForcing IsBVSolution.radiusCoeff
  change _ = _
  exact alpha_alg hr₁ hr₂ hl₁ hl₂ hg₁ hg₂

/-- Pointwise algebra converting the compact outgoing quotient derivative
to the printed four-term difference equation. -/
theorem ComparisonData.beta_ratio_forcing_algebra (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    -IsBVSolution.radiusCoeff D.S₁ u v * D.S₁.zeta u v /
        D.S₁.nu u v ^ 2 +
      IsBVSolution.radiusCoeff D.S₂ u v * D.S₂.zeta u v /
        D.S₂.nu u v ^ 2 = betaRatioForcing D u v := by
  have hp := D.hT huv
  have hr₁ := (D.h₁.solution.radius_pos (u, v) hp.1).ne'
  have hr₂ := (D.h₂.solution.radius_pos (u, v) hp.2).ne'
  obtain ⟨c₁, hc₁, hlam₁⟩ := D.h₁.lam_bounded_below
  obtain ⟨c₂, hc₂, hlam₂⟩ := D.h₂.lam_bounded_below
  have hn₁ : D.S₁.nu u v ≠ 0 :=
    ne_of_lt ((D.h₁.nu_le_neg_lower hc₁ hlam₁ hp.1).trans_lt
      (neg_lt_zero.mpr hc₁))
  have hn₂ : D.S₂.nu u v ≠ 0 :=
    ne_of_lt ((D.h₂.nu_le_neg_lower hc₂ hlam₂ hp.2).trans_lt
      (neg_lt_zero.mpr hc₂))
  have hg₁ : 1 - IsBVSolution.mu D.S₁ u v ≠ 0 := by
    have hmu := (D.h₁.mass_ratio_bounds hp.1).2
    change IsBVSolution.mu D.S₁ u v < 1 at hmu
    linarith
  have hg₂ : 1 - IsBVSolution.mu D.S₂ u v ≠ 0 := by
    have hmu := (D.h₂.mass_ratio_bounds hp.2).2
    change IsBVSolution.mu D.S₂ u v < 1 at hmu
    linarith
  unfold betaRatioForcing IsBVSolution.radiusCoeff
  change _ = _
  exact beta_alg hr₁ hr₂ hn₁ hn₂ hg₁ hg₂

/-- The a.e. incoming difference equation in its four-term source form.
The quotient difference has an absolutely continuous representative on every
compact incoming subsegment of the comparison triangle. -/
theorem ComparisonData.alpha_ratio_source_ae (D : ComparisonData)
    {v a b : ℝ} (hav : D.a ≤ a) (hab : a ≤ b)
    (hbv : b < v) (hvb : v < D.b) :
    AbsolutelyContinuousOnInterval
      (fun s => D.S₁.alpha s v / D.S₁.lam s v -
        D.S₂.alpha s v / D.S₂.lam s v) a b ∧
      ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.Icc a b →
        deriv (fun t => D.S₁.alpha t v / D.S₁.lam t v -
          D.S₂.alpha t v / D.S₂.lam t v) s =
          alphaRatioForcing D s v := by
  obtain ⟨hAC, hder⟩ := D.alpha_ratio_difference_ae hav hab hbv hvb
  refine ⟨hAC, ?_⟩
  filter_upwards [hder] with s hsder hs
  have hsT : (s, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨hav.trans hs.1, hs.2.trans_lt hbv, hvb⟩
  rw [hsder hs, D.alpha_ratio_forcing_algebra hsT]

/-- The a.e. outgoing difference equation in its four-term source form.
The quotient difference has an absolutely continuous representative on every
compact outgoing subsegment of the comparison triangle. -/
theorem ComparisonData.beta_ratio_source_ae (D : ComparisonData)
    {u a b : ℝ} (hau : D.a ≤ u) (hua : u < a)
    (hab : a ≤ b) (hbb : b < D.b) :
    AbsolutelyContinuousOnInterval
      (fun t => D.S₁.beta u t / D.S₁.nu u t -
        D.S₂.beta u t / D.S₂.nu u t) a b ∧
      ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Icc a b →
        deriv (fun s => D.S₁.beta u s / D.S₁.nu u s -
          D.S₂.beta u s / D.S₂.nu u s) t =
          betaRatioForcing D u t := by
  obtain ⟨hAC, hder⟩ := D.beta_ratio_difference_ae hau hua hab hbb
  refine ⟨hAC, ?_⟩
  filter_upwards [hder] with t htder ht
  have htT : (u, t) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨hau, hua.trans_le ht.1, ht.2.trans_lt hbb⟩
  rw [htder ht, D.beta_ratio_forcing_algebra htT]

end ChristodoulouBV.Uniqueness

end
