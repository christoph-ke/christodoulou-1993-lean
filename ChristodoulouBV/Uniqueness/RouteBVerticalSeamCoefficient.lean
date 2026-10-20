module

public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamMixed
public import ChristodoulouBV.Uniqueness.RouteBVerticalSeamPartial
import Mathlib.Tactic

/-!
# The off-axis gravitational coefficient

The mixed gravitational source is linear in the contraction `ν`.  Its
coefficient is C¹ on every safe off-axis subregion, even though the axis
triangle itself contains points where the quotient is singular.
-/

@[expose] public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The coefficient in `ν_v = A ν`, written with the mass gap as denominator. -/
noncomputable def routeBGravCoefficient (S : Fields) (p : ℝ × ℝ) : ℝ :=
  2 * S.m p.1 p.2 * S.lam p.1 p.2 /
    (S.r p.1 p.2 * (S.r p.1 p.2 - 2 * S.m p.1 p.2))

/-- The usual positive mass ratio gap gives the positive undivided mass gap
where the radius is positive. -/
theorem routeB_mass_gap_pos_of_radius_and_ratio
    {r m : ℝ} (hr : 0 < r) (hgap : 0 < 1 - 2 * m / r) :
    0 < r - 2 * m := by
  have hproduct := mul_pos hgap hr
  have heq : (1 - 2 * m / r) * r = r - 2 * m := by
    field_simp [ne_of_gt hr]
  exact heq ▸ hproduct

/-- The classical mixed source factors as the gravitational coefficient times
the contraction wherever the radius and mass gap are nonzero. -/
theorem routeB_mixedExpr_eq_gravCoefficient_mul_nu
    (S : Fields) (p : ℝ × ℝ)
    (hr : S.r p.1 p.2 ≠ 0)
    (hgap : S.r p.1 p.2 - 2 * S.m p.1 p.2 ≠ 0) :
    routeBMixedExpr (fun c => routeBField S c p) =
      routeBGravCoefficient S p * S.nu p.1 p.2 := by
  change ((2 * S.m p.1 p.2 / S.r p.1 p.2) *
      S.lam p.1 p.2 * S.nu p.1 p.2) /
      ((1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) * S.r p.1 p.2) =
    (2 * S.m p.1 p.2 * S.lam p.1 p.2 /
      (S.r p.1 p.2 * (S.r p.1 p.2 - 2 * S.m p.1 p.2))) *
        S.nu p.1 p.2
  field_simp [hr, hgap]

/-- Relative C¹ regularity of the fields gives relative C¹ regularity of
the gravitational coefficient on an off-axis region. -/
theorem routeB_gravCoefficient_contDiffOn
    {K : Set (ℝ × ℝ)} {S : Fields}
    (hC1 : RouteBFieldsC1On S K)
    (hr : ∀ p ∈ K, S.r p.1 p.2 ≠ 0)
    (hgap : ∀ p ∈ K, S.r p.1 p.2 - 2 * S.m p.1 p.2 ≠ 0) :
    ContDiffOn ℝ 1 (routeBGravCoefficient S) K := by
  have hm := hC1 .mass
  have hl := hC1 .expansion
  have hrC1 := hC1 .radius
  change ContDiffOn ℝ 1
    (fun p : ℝ × ℝ => 2 * S.m p.1 p.2 * S.lam p.1 p.2 /
      (S.r p.1 p.2 * (S.r p.1 p.2 - 2 * S.m p.1 p.2))) K
  apply ((contDiffOn_const.mul hm).mul hl).div
    (hrC1.mul (hrC1.sub (contDiffOn_const.mul hm)))
  intro p hp
  exact mul_ne_zero (hr p hp) (hgap p hp)

end ChristodoulouBV.Uniqueness

end
