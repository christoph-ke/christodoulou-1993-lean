module

public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamCoefficient
import Mathlib.Tactic

/-!
# Congruence of the gravitational coefficient jet

The coefficient `A = 2mλ/(r(r-2m))` depends only on three primary fields.
Matching values and full relative jets of those fields therefore match the
coefficient jet, without any input about the transverse `ν` or `β` jets.
-/

public section

namespace ChristodoulouBV.Uniqueness

/-- Matching radius, mass and expansion values and full relative first jets
give the same gravitational coefficient jet on two closed regions. -/
theorem routeB_gravCoefficient_jet_eq_of_primary_jets
    {K₁ K₂ : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hU₁ : UniqueDiffWithinAt ℝ K₁ p)
    (hU₂ : UniqueDiffWithinAt ℝ K₂ p)
    {S₁ S₂ : Fields}
    (hC₁ : RouteBFieldsC1On S₁ K₁)
    (hC₂ : RouteBFieldsC1On S₂ K₂)
    (hp₁ : p ∈ K₁) (hp₂ : p ∈ K₂)
    (hr : S₁.r p.1 p.2 = S₂.r p.1 p.2)
    (hm : S₁.m p.1 p.2 = S₂.m p.1 p.2)
    (hl : S₁.lam p.1 p.2 = S₂.lam p.1 p.2)
    (hR : fderivWithin ℝ (routeBField S₁ .radius) K₁ p =
      fderivWithin ℝ (routeBField S₂ .radius) K₂ p)
    (hM : fderivWithin ℝ (routeBField S₁ .mass) K₁ p =
      fderivWithin ℝ (routeBField S₂ .mass) K₂ p)
    (hL : fderivWithin ℝ (routeBField S₁ .expansion) K₁ p =
      fderivWithin ℝ (routeBField S₂ .expansion) K₂ p)
    (hrne : S₁.r p.1 p.2 ≠ 0)
    (hgap : S₁.r p.1 p.2 - 2 * S₁.m p.1 p.2 ≠ 0) :
    fderivWithin ℝ (routeBGravCoefficient S₁) K₁ p =
      fderivWithin ℝ (routeBGravCoefficient S₂) K₂ p := by
  let X (S : Fields) : ℝ × ℝ → ℝ × (ℝ × ℝ) :=
    fun q => (S.r q.1 q.2, (S.m q.1 q.2, S.lam q.1 q.2))
  let g : ℝ × (ℝ × ℝ) → ℝ := fun z =>
    2 * z.2.1 * z.2.2 / (z.1 * (z.1 - 2 * z.2.1))
  have hXval : X S₁ p = X S₂ p := by
    simp only [X, Prod.mk.injEq]
    exact ⟨hr, hm, hl⟩
  have hRdiff₁ := (hC₁ .radius).differentiableOn (by norm_num) p hp₁
  have hMdiff₁ := (hC₁ .mass).differentiableOn (by norm_num) p hp₁
  have hLdiff₁ := (hC₁ .expansion).differentiableOn (by norm_num) p hp₁
  have hRdiff₂ := (hC₂ .radius).differentiableOn (by norm_num) p hp₂
  have hMdiff₂ := (hC₂ .mass).differentiableOn (by norm_num) p hp₂
  have hLdiff₂ := (hC₂ .expansion).differentiableOn (by norm_num) p hp₂
  have hXdiff₁ : DifferentiableWithinAt ℝ (X S₁) K₁ p :=
    hRdiff₁.prodMk (hMdiff₁.prodMk hLdiff₁)
  have hXdiff₂ : DifferentiableWithinAt ℝ (X S₂) K₂ p :=
    hRdiff₂.prodMk (hMdiff₂.prodMk hLdiff₂)
  have hXjet : fderivWithin ℝ (X S₁) K₁ p =
      fderivWithin ℝ (X S₂) K₂ p := by
    have h₁ := hRdiff₁.fderivWithin_prodMk
      (hMdiff₁.prodMk hLdiff₁) hU₁
    have h₂ := hMdiff₁.fderivWithin_prodMk hLdiff₁ hU₁
    have h₃ := hRdiff₂.fderivWithin_prodMk
      (hMdiff₂.prodMk hLdiff₂) hU₂
    have h₄ := hMdiff₂.fderivWithin_prodMk hLdiff₂ hU₂
    change fderivWithin ℝ (X S₁) K₁ p = _ at h₁
    change fderivWithin ℝ (X S₂) K₂ p = _ at h₃
    rw [h₁, h₃, h₂, h₄]
    exact congrArg₂ ContinuousLinearMap.prod hR
      (congrArg₂ ContinuousLinearMap.prod hM hL)
  have hden : (X S₁ p).1 * ((X S₁ p).1 - 2 * (X S₁ p).2.1) ≠ 0 :=
    mul_ne_zero hrne hgap
  have hGdiff : DifferentiableAt ℝ g (X S₁ p) := by
    dsimp [g]
    fun_prop
  have hComp₁ := fderivWithin_comp p (s := K₁) (t := Set.univ)
    hGdiff.differentiableWithinAt hXdiff₁ (by intro q hq; trivial) hU₁
  have hComp₂ := fderivWithin_comp p (s := K₂) (t := Set.univ)
    (hXval ▸ hGdiff.differentiableWithinAt)
    hXdiff₂ (by intro q hq; trivial) hU₂
  have hA₁ : routeBGravCoefficient S₁ = g ∘ X S₁ := by
    funext q
    rfl
  have hA₂ : routeBGravCoefficient S₂ = g ∘ X S₂ := by
    funext q
    rfl
  rw [hA₁, hA₂, hComp₁, hComp₂, hXval, hXjet]

end ChristodoulouBV.Uniqueness

end
