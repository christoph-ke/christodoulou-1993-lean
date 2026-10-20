module

public import ChristodoulouBV.Uniqueness.GammaFinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Corrected incoming mass difference equation

The first denominator in the displayed incoming difference equation on p. 1154
is `ν₂`. The equation below records the pointwise algebra of the two incoming
mass densities before it is integrated on a complete incoming characteristic.
-/

@[expose] public section

namespace ChristodoulouBV.Uniqueness

/-- The homogeneous coefficient of the corrected incoming mass equation. -/
noncomputable def incomingMassCoefficient (D : ComparisonData) (u v : ℝ) : ℝ :=
  -(D.S₂.zeta u v ^ 2 / (D.S₂.nu u v * D.S₁.r u v))

/-- Twice the forcing in the corrected incoming mass difference equation. -/
noncomputable def incomingMassForcing (D : ComparisonData) (u v : ℝ) : ℝ :=
  (D.S₂.zeta u v ^ 2 / D.S₂.nu u v) *
    (IsBVSolution.mu D.S₂ u v *
        ((D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v) -
      ((1 - IsBVSolution.mu D.S₁ u v) / D.S₁.nu u v) *
        (D.S₁.nu u v - D.S₂.nu u v)) +
    ((1 - IsBVSolution.mu D.S₁ u v) / D.S₁.nu u v) *
      (D.S₁.zeta u v + D.S₂.zeta u v) *
        (D.S₁.zeta u v - D.S₂.zeta u v)

/-- Subtraction of the two incoming mass densities, with the corrected `ν₂`
denominator. This is the pointwise identity behind the a.e. equation for
`∂ᵤ Δm`. -/
theorem ComparisonData.mass_in_difference_linear (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    IsBVSolution.massInDensity D.S₁ u v -
        IsBVSolution.massInDensity D.S₂ u v =
      incomingMassCoefficient D u v *
          (D.S₁.m u v - D.S₂.m u v) +
        incomingMassForcing D u v / 2 := by
  have hp := D.hT huv
  have hr₁ : D.S₁.r u v ≠ 0 :=
    (D.h₁.solution.radius_pos (u, v) hp.1).ne'
  have hr₂ : D.S₂.r u v ≠ 0 :=
    (D.h₂.solution.radius_pos (u, v) hp.2).ne'
  have hn₁ : D.S₁.nu u v ≠ 0 := by
    obtain ⟨c, hc, hlam⟩ := D.h₁.lam_bounded_below
    exact (lt_of_le_of_lt (D.h₁.nu_le_neg_lower hc hlam hp.1)
      (neg_lt_zero.mpr hc)).ne
  have hn₂ : D.S₂.nu u v ≠ 0 := by
    obtain ⟨c, hc, hlam⟩ := D.h₂.lam_bounded_below
    exact (lt_of_le_of_lt (D.h₂.nu_le_neg_lower hc hlam hp.2)
      (neg_lt_zero.mpr hc)).ne
  unfold IsBVSolution.massInDensity incomingMassCoefficient
    incomingMassForcing IsBVSolution.mu
  field_simp
  ring

/-- On every compact part of a complete incoming ray, the derivative of the
mass difference has the corrected linear coefficient and forcing. The endpoint
`v` remains excluded from the solution domain. -/
theorem ComparisonData.mass_in_difference_ae (D : ComparisonData)
    {u w v : ℝ} (huv : (u, v) ∈ triangle D.a D.b)
    (huw : u ≤ w) (hwv : w < v) :
    ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.Icc u w →
      deriv (fun t => D.S₁.m t v - D.S₂.m t v) s =
        incomingMassCoefficient D s v *
          (D.S₁.m s v - D.S₂.m s v) +
        incomingMassForcing D s v / 2 := by
  have haccess₁ := IsBVSolution.incoming_axis_access_of_triangle
    (fun p hp => (D.hT hp).1) huv
  have haccess₂ := IsBVSolution.incoming_axis_access_of_triangle
    (fun p hp => (D.hT hp).2) huv
  have hseg₁ := IsBVSolution.incoming_seg_subset_of_half_open_access
    hwv haccess₁
  have hseg₂ := IsBVSolution.incoming_seg_subset_of_half_open_access
    hwv haccess₂
  have h₁ := D.h₁.solution.mass_in_ac_ae huw hseg₁
  have h₂ := D.h₂.solution.mass_in_ac_ae huw hseg₂
  filter_upwards [h₁.1.ae_differentiableAt, h₂.1.ae_differentiableAt,
    h₁.2, h₂.2] with s hd₁ hd₂ hm₁ hm₂ hs
  have hsT : (s, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨huv.1.trans hs.1, hs.2.trans_lt hwv, huv.2.2⟩
  have hsU : s ∈ Set.uIcc u w := by
    simpa only [Set.uIcc_of_le huw] using hs
  change deriv ((fun t => D.S₁.m t v) - (fun t => D.S₂.m t v)) s = _
  rw [deriv_sub (hd₁ hsU) (hd₂ hsU), hm₁ hs, hm₂ hs]
  exact D.mass_in_difference_linear hsT

end ChristodoulouBV.Uniqueness

end
