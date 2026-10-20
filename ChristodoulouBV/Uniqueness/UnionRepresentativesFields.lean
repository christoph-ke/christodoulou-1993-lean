module

public import ChristodoulouBV.Uniqueness.UnionRepresentativesIncoming

/-!
# The seven common field representatives

The three primary fields are fixed pointwise by uniqueness. The outgoing
densities use left traces, while the incoming densities agree pointwise on
source overlaps.
-/

@[expose] public section

namespace ChristodoulouBV.Uniqueness

/-- The candidate field tuple on the union. The solution and BV equations
are verified separately. -/
noncomputable def gluedFields (U₁ : Set (ℝ × ℝ)) (S₁ S₂ : Fields) : Fields :=
  { r := (commonPrimary U₁ S₁ S₂).r
    phi := (commonPrimary U₁ S₁ S₂).phi
    m := (commonPrimary U₁ S₁ S₂).m
    lam := commonLam U₁ S₁ S₂
    nu := commonNu U₁ S₁ S₂
    alpha := commonAlpha U₁ S₁ S₂
    beta := commonBeta U₁ S₁ S₂ }

/-- The candidate restricts to the first source in its three primary and
two incoming fields. -/
theorem gluedFields_eq_first
    {U₁ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    {u v : ℝ} (hp : (u, v) ∈ U₁) :
    (gluedFields U₁ S₁ S₂).r u v = S₁.r u v ∧
      (gluedFields U₁ S₁ S₂).phi u v = S₁.phi u v ∧
      (gluedFields U₁ S₁ S₂).m u v = S₁.m u v ∧
      (gluedFields U₁ S₁ S₂).nu u v = S₁.nu u v ∧
      (gluedFields U₁ S₁ S₂).beta u v = S₁.beta u v := by
  obtain ⟨hr, hphi, hm⟩ := commonPrimary_eq_first hp
  obtain ⟨hnu, hbeta⟩ := common_nu_beta_eq_first hp
  exact ⟨hr, hphi, hm, hnu, hbeta⟩

/-- The same five fields restrict pointwise to the second source. -/
theorem gluedFields_eq_second
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {u v : ℝ} (hp : (u, v) ∈ U₂) :
    (gluedFields U₁ S₁ S₂).r u v = S₂.r u v ∧
      (gluedFields U₁ S₁ S₂).phi u v = S₂.phi u v ∧
      (gluedFields U₁ S₁ S₂).m u v = S₂.m u v ∧
      (gluedFields U₁ S₁ S₂).nu u v = S₂.nu u v ∧
      (gluedFields U₁ S₁ S₂).beta u v = S₂.beta u v := by
  obtain ⟨hr, hphi, hm⟩ := commonPrimary_eq_second h₁ h₂ hdata hp
  obtain ⟨hnu, hbeta⟩ := common_nu_beta_eq_second h₁ h₂ hdata hp
  exact ⟨hr, hphi, hm, hnu, hbeta⟩

/-- The outgoing fields restrict to the first source's left traces. -/
theorem gluedFields_lam_alpha_eq_first
    {U₁ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    {u v : ℝ} (hp : (u, v) ∈ U₁) :
    (gluedFields U₁ S₁ S₂).lam u v = (S₁.lam u).leftLim v ∧
      (gluedFields U₁ S₁ S₂).alpha u v = (S₁.alpha u).leftLim v :=
  common_lam_alpha_eq_first hp

/-- The outgoing fields restrict to the second source's left traces. -/
theorem gluedFields_lam_alpha_eq_second
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {u v : ℝ} (hp : (u, v) ∈ U₂) :
    (gluedFields U₁ S₁ S₂).lam u v = (S₂.lam u).leftLim v ∧
      (gluedFields U₁ S₁ S₂).alpha u v = (S₂.alpha u).leftLim v :=
  common_lam_alpha_eq_second h₁ h₂ hdata hp

end ChristodoulouBV.Uniqueness

end
