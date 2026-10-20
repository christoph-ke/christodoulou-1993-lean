module

public import ChristodoulouBV.Uniqueness.ExtensionStripDomain
public import ChristodoulouBV.Uniqueness.ExtensionLocalSigns

/-!
# Signed integrals on the enlarged working domain

These are the three integrals following equation (5.2), with a segment in
the actual enlarged domain. They have no old-domain cutoff parameter.
-/

@[expose] public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- The signed `I₁` integral on an incoming segment of the enlarged domain. -/
noncomputable def stripIntegralI₁ (u₁ top : ℝ) (S : Fields) (u₀ u v : ℝ)
    (_hseg : ∀ s ∈ Icc u₀ u, (s, v) ∈ extensionWorkingDomain u₁ top) : ℝ :=
  -∫ s in u₀..u, (S.nu s v / S.r s v) *
    ((2 * S.m s v / S.r s v) / (1 - 2 * S.m s v / S.r s v)) *
    (deriv (fun t => S.alpha s t / S.lam s t) v / S.lam s v)

/-- The signed `I₂` integral on an incoming segment of the enlarged domain. -/
noncomputable def stripIntegralI₂ (u₁ top : ℝ) (S : Fields) (u₀ u v : ℝ)
    (_hseg : ∀ s ∈ Icc u₀ u, (s, v) ∈ extensionWorkingDomain u₁ top) : ℝ :=
  -∫ s in u₀..u, (S.nu s v / (S.r s v)^2) *
    ((2 * S.m s v / S.r s v) / (1 - 2 * S.m s v / S.r s v)) *
    (S.theta s v / S.lam s v)

/-- The signed `I₃` integral on an incoming segment of the enlarged domain. -/
noncomputable def stripIntegralI₃ (u₁ top : ℝ) (S : Fields) (u₀ u v : ℝ)
    (_hseg : ∀ s ∈ Icc u₀ u, (s, v) ∈ extensionWorkingDomain u₁ top) : ℝ :=
  -∫ s in u₀..u, (S.nu s v / (S.r s v)^2) *
    (1 / (1 - 2 * S.m s v / S.r s v)) *
    (S.theta s v / S.lam s v)^3

end ChristodoulouBV.Uniqueness

end
