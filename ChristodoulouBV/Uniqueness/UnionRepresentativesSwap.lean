module

public import ChristodoulouBV.Uniqueness.UnionRepresentativesTransport

/-!
# Symmetry of the selected union representatives

Swapping the two source labels gives the same seven values at every union
point. This transfers the mixed incoming transport argument to a segment
whose upper endpoint belongs to the second source.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- Initial agreement is symmetric in the two sources. -/
theorem swapped_initial_agreement
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w) :
    ∀ w, (0, w) ∈ U₂ ∩ U₁ →
      S₂.r 0 w = S₁.r 0 w ∧ S₂.phi 0 w = S₁.phi 0 w := by
  intro w hw
  obtain ⟨hr, hphi⟩ := hdata w ⟨hw.2, hw.1⟩
  exact ⟨hr.symm, hphi.symm⟩

/-- Every selected field value is independent of which source is named
first, at all points of the union. -/
theorem gluedFields_swap_eq_on_union
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {u v : ℝ} (hp : (u, v) ∈ U₁ ∪ U₂) :
    (gluedFields U₂ S₂ S₁).r u v = (gluedFields U₁ S₁ S₂).r u v ∧
    (gluedFields U₂ S₂ S₁).phi u v = (gluedFields U₁ S₁ S₂).phi u v ∧
    (gluedFields U₂ S₂ S₁).m u v = (gluedFields U₁ S₁ S₂).m u v ∧
    (gluedFields U₂ S₂ S₁).lam u v = (gluedFields U₁ S₁ S₂).lam u v ∧
    (gluedFields U₂ S₂ S₁).nu u v = (gluedFields U₁ S₁ S₂).nu u v ∧
    (gluedFields U₂ S₂ S₁).alpha u v =
      (gluedFields U₁ S₁ S₂).alpha u v ∧
    (gluedFields U₂ S₂ S₁).beta u v = (gluedFields U₁ S₁ S₂).beta u v := by
  have hdata' := swapped_initial_agreement hdata
  rcases hp with hp₁ | hp₂
  · obtain ⟨hr₁, hphi₁, hm₁, hnu₁, hbeta₁⟩ :=
      gluedFields_eq_first (S₂ := S₂) hp₁
    obtain ⟨hr₂, hphi₂, hm₂, hnu₂, hbeta₂⟩ :=
      gluedFields_eq_second h₂ h₁ hdata' hp₁
    obtain ⟨hlam₁, halpha₁⟩ :=
      gluedFields_lam_alpha_eq_first (S₂ := S₂) hp₁
    obtain ⟨hlam₂, halpha₂⟩ :=
      gluedFields_lam_alpha_eq_second h₂ h₁ hdata' hp₁
    exact ⟨hr₂.trans hr₁.symm, hphi₂.trans hphi₁.symm,
      hm₂.trans hm₁.symm, hlam₂.trans hlam₁.symm,
      hnu₂.trans hnu₁.symm, halpha₂.trans halpha₁.symm,
      hbeta₂.trans hbeta₁.symm⟩
  · obtain ⟨hr₁, hphi₁, hm₁, hnu₁, hbeta₁⟩ :=
      gluedFields_eq_second h₁ h₂ hdata hp₂
    obtain ⟨hr₂, hphi₂, hm₂, hnu₂, hbeta₂⟩ :=
      gluedFields_eq_first (S₂ := S₁) hp₂
    obtain ⟨hlam₁, halpha₁⟩ :=
      gluedFields_lam_alpha_eq_second h₁ h₂ hdata hp₂
    obtain ⟨hlam₂, halpha₂⟩ :=
      gluedFields_lam_alpha_eq_first (S₂ := S₁) hp₂
    exact ⟨hr₂.trans hr₁.symm, hphi₂.trans hphi₁.symm,
      hm₂.trans hm₁.symm, hlam₂.trans hlam₁.symm,
      hnu₂.trans hnu₁.symm, halpha₂.trans halpha₁.symm,
      hbeta₂.trans hbeta₁.symm⟩

/-- The incoming transport primitives on a mixed terminal segment also hold
when its upper endpoint belongs to the second source. -/
theorem second_source_lam_alpha_in_mixed_top
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) (hb : (b, v) ∈ U₂) :
    IntervalPrimitive
      (fun s => (gluedFields U₁ S₁ S₂).lam s v)
      (fun s => IsBVSolution.radiusCoeff (gluedFields U₁ S₁ S₂) s v) a b ∧
    IntervalPrimitive
      (fun s => (gluedFields U₁ S₁ S₂).alpha s v)
      (fun s => IsBVSolution.radiusCoeff (gluedFields U₁ S₁ S₂) s v *
        (gluedFields U₁ S₁ S₂).phi s v) a b := by
  let G₁ := gluedFields U₁ S₁ S₂
  let G₂ := gluedFields U₂ S₂ S₁
  have hseg' : inSeg v a b ⊆ U₂ ∪ U₁ := by
    intro p hp
    exact (hseg hp).symm
  have hprime := first_source_lam_alpha_in_mixed_top h₂ h₁
    (swapped_initial_agreement hdata) hab hseg' hb
  have heq (s : ℝ) (hs : s ∈ Icc a b) :=
    gluedFields_swap_eq_on_union h₁ h₂ hdata
      (hseg (by
        change s ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
        exact ⟨hs, rfl⟩))
  have hcoeffEq (s : ℝ) (hs : s ∈ Icc a b) :
      IsBVSolution.radiusCoeff G₂ s v =
        IsBVSolution.radiusCoeff G₁ s v := by
    obtain ⟨hr, _, hm, hlam, hnu, _, _⟩ := heq s hs
    dsimp only [G₁, G₂]
    simp only [IsBVSolution.radiusCoeff, hr, hm, hlam, hnu]
  have hcoeffPhiEq (s : ℝ) (hs : s ∈ Icc a b) :
      IsBVSolution.radiusCoeff G₂ s v * G₂.phi s v =
        IsBVSolution.radiusCoeff G₁ s v * G₁.phi s v := by
    rw [hcoeffEq s hs, (heq s hs).2.1]
  have hcoeffEqI : EqOn
      (fun s => IsBVSolution.radiusCoeff G₂ s v)
      (fun s => IsBVSolution.radiusCoeff G₁ s v) (Ι a b) := by
    intro s hs
    rw [uIoc_of_le hab] at hs
    exact hcoeffEq s ⟨hs.1.le, hs.2⟩
  have hcoeffPhiEqI : EqOn
      (fun s => IsBVSolution.radiusCoeff G₂ s v * G₂.phi s v)
      (fun s => IsBVSolution.radiusCoeff G₁ s v * G₁.phi s v) (Ι a b) := by
    intro s hs
    rw [uIoc_of_le hab] at hs
    exact hcoeffPhiEq s ⟨hs.1.le, hs.2⟩
  have hLamInt : IntervalIntegrable
      (fun s => IsBVSolution.radiusCoeff G₁ s v) volume a b :=
    hprime.1.1.congr hcoeffEqI
  have hAlphaInt : IntervalIntegrable
      (fun s => IsBVSolution.radiusCoeff G₁ s v * G₁.phi s v)
      volume a b := hprime.2.1.congr hcoeffPhiEqI
  have hLamIntegralEq :
      (∫ s in a..b, IsBVSolution.radiusCoeff G₂ s v) =
        ∫ s in a..b, IsBVSolution.radiusCoeff G₁ s v := by
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall fun s hs => hcoeffEqI hs
  have hAlphaIntegralEq :
      (∫ s in a..b, IsBVSolution.radiusCoeff G₂ s v * G₂.phi s v) =
        ∫ s in a..b, IsBVSolution.radiusCoeff G₁ s v * G₁.phi s v := by
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall fun s hs => hcoeffPhiEqI hs
  have hLamEq : G₁.lam b v - G₁.lam a v =
      ∫ s in a..b, IsBVSolution.radiusCoeff G₁ s v := by
    have heqa := (heq a ⟨le_rfl, hab⟩).2.2.2.1
    have heqb := (heq b ⟨hab, le_rfl⟩).2.2.2.1
    have hprimEq := hprime.1.2
    change G₂.lam b v - G₂.lam a v =
      ∫ s in a..b, IsBVSolution.radiusCoeff G₂ s v at hprimEq
    rw [heqa, heqb, hLamIntegralEq] at hprimEq
    exact hprimEq
  have hAlphaEq : G₁.alpha b v - G₁.alpha a v =
      ∫ s in a..b, IsBVSolution.radiusCoeff G₁ s v * G₁.phi s v := by
    have heqa := (heq a ⟨le_rfl, hab⟩).2.2.2.2.2.1
    have heqb := (heq b ⟨hab, le_rfl⟩).2.2.2.2.2.1
    have hprimEq := hprime.2.2
    change G₂.alpha b v - G₂.alpha a v =
      ∫ s in a..b, IsBVSolution.radiusCoeff G₂ s v * G₂.phi s v at hprimEq
    rw [heqa, heqb, hAlphaIntegralEq] at hprimEq
    exact hprimEq
  exact ⟨⟨hLamInt, hLamEq⟩, ⟨hAlphaInt, hAlphaEq⟩⟩

/-- The chosen fields satisfy both incoming transport primitives on every
closed incoming segment contained in the union, including mixed terminal
segments. -/
theorem gluedFields_lam_alpha_in
    {U₁ U₂ : Set (ℝ × ℝ)} {S₁ S₂ : Fields}
    (h₁ : IsBVSolution U₁ S₁) (h₂ : IsBVSolution U₂ S₂)
    (hdata : ∀ w, (0, w) ∈ U₁ ∩ U₂ →
      S₁.r 0 w = S₂.r 0 w ∧ S₁.phi 0 w = S₂.phi 0 w)
    {v a b : ℝ} (hab : a ≤ b)
    (hseg : inSeg v a b ⊆ U₁ ∪ U₂) :
    IntervalPrimitive
      (fun s => (gluedFields U₁ S₁ S₂).lam s v)
      (fun s => IsBVSolution.radiusCoeff (gluedFields U₁ S₁ S₂) s v) a b ∧
    IntervalPrimitive
      (fun s => (gluedFields U₁ S₁ S₂).alpha s v)
      (fun s => IsBVSolution.radiusCoeff (gluedFields U₁ S₁ S₂) s v *
        (gluedFields U₁ S₁ S₂).phi s v) a b := by
  have hb : (b, v) ∈ U₁ ∪ U₂ := hseg (by
    change b ∈ Icc a b ∧ v ∈ ({v} : Set ℝ)
    exact ⟨⟨hab, le_rfl⟩, rfl⟩)
  rcases hb with hb₁ | hb₂
  · exact first_source_lam_alpha_in_mixed_top h₁ h₂ hdata hab hseg hb₁
  · exact second_source_lam_alpha_in_mixed_top h₁ h₂ hdata hab hseg hb₂

end ChristodoulouBV.Uniqueness

end
