module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBox
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Uniform two-input bounds for removable quotients

The fields of a common box are the cubic value and quadratic first-jet bounds
that arise from a Volterra estimate, together with radius bounds. The
conclusions here are bounds for the removable cubic-over-linear and
cubic-over-square quotients throughout the closed coordinate triangle.
-/

public section

open Set

namespace intervalIntegral

/-- A continuous inequality verified on the interior of a nondegenerate
closed coordinate triangle holds on its whole closure. -/
theorem le_on_closedCoordTriangle_of_interior
    {a b : ℝ} (hab : a < b) {f g : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hg : ContinuousOn g (closedCoordTriangle a b))
    (h : ∀ p ∈ interior (closedCoordTriangle a b), f p ≤ g p) :
    ∀ p ∈ closedCoordTriangle a b, f p ≤ g p := by
  have hclosure : closure (interior (closedCoordTriangle a b)) =
      closedCoordTriangle a b := by
    rw [(convex_closedCoordTriangle a b).closure_interior_eq_closure_of_nonempty_interior
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab),
      (isClosed_closedCoordTriangle a b).closure_eq]
  intro p hp
  have hf' : ContinuousOn f (closure (interior (closedCoordTriangle a b))) := by
    simpa only [hclosure] using hf
  have hg' : ContinuousOn g (closure (interior (closedCoordTriangle a b))) := by
    simpa only [hclosure] using hg
  have hp' : p ∈ closure (interior (closedCoordTriangle a b)) := by
    simpa only [hclosure] using hp
  exact le_on_closure h hf' hg' hp'

/-- Two instances of cubic axis data with common value, first-jet, radius,
and difference bounds. These are input estimates, independent of how the
two cubic numerators were produced. -/
structure CubicRationalPairBox (a b c : ℝ) where
  /-- First cubic input. -/
  first : CubicRationalTriangleBox a b c
  /-- Second cubic input. -/
  second : CubicRationalTriangleBox a b c
  /-- Common cubic value coefficient. -/
  J₀ : ℝ
  /-- Common quadratic jet coefficient. -/
  J₁ : ℝ
  /-- Cubic value-difference coefficient. -/
  JΔ₀ : ℝ
  /-- Quadratic jet-difference coefficient. -/
  JΔ₁ : ℝ
  /-- Common radius-jet coefficient. -/
  R₁ : ℝ
  /-- Radius-jet difference coefficient. -/
  RΔ : ℝ
  /-- Common size of the input difference. -/
  D : ℝ
  /-- The coordinate gap is at most one. -/
  width_le_one : b - a ≤ 1
  /-- The common bound coefficients are nonnegative. -/
  J₀_nonneg : 0 ≤ J₀
  /-- The common jet bound is nonnegative. -/
  J₁_nonneg : 0 ≤ J₁
  /-- The numerator value-difference coefficient is nonnegative. -/
  JΔ₀_nonneg : 0 ≤ JΔ₀
  /-- The numerator jet-difference coefficient is nonnegative. -/
  JΔ₁_nonneg : 0 ≤ JΔ₁
  /-- The radius jet bound is nonnegative. -/
  R₁_nonneg : 0 ≤ R₁
  /-- The radius jet-difference coefficient is nonnegative. -/
  RΔ_nonneg : 0 ≤ RΔ
  /-- The input distance is nonnegative. -/
  D_nonneg : 0 ≤ D
  /-- Both numerators are nonnegative and have a common cubic bound. -/
  J_bound : ∀ p ∈ closedCoordTriangle a b,
    (0 ≤ first.J p ∧ first.J p ≤ J₀ * (p.2 - p.1) ^ 3) ∧
    (0 ≤ second.J p ∧ second.J p ≤ J₀ * (p.2 - p.1) ^ 3)
  /-- Both coordinate numerator jets have a common quadratic bound. -/
  J_jet_bound : ∀ p ∈ closedCoordTriangle a b, ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
    |(fderivWithin ℝ first.J (closedCoordTriangle a b) p) e| ≤
      J₁ * (p.2 - p.1) ^ 2 ∧
    |(fderivWithin ℝ second.J (closedCoordTriangle a b) p) e| ≤
      J₁ * (p.2 - p.1) ^ 2
  /-- Cubic two-input numerator difference. -/
  J_sub_bound : ∀ p ∈ closedCoordTriangle a b,
    |first.J p - second.J p| ≤ JΔ₀ * (p.2 - p.1) ^ 3 * D
  /-- Quadratic two-input numerator-jet difference. -/
  J_jet_sub_bound : ∀ p ∈ closedCoordTriangle a b,
    ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
      |(fderivWithin ℝ first.J (closedCoordTriangle a b) p) e -
        (fderivWithin ℝ second.J (closedCoordTriangle a b) p) e| ≤
          JΔ₁ * (p.2 - p.1) ^ 2 * D
  /-- Both radii have uniformly bounded coordinate jets. -/
  r_jet_bound : ∀ p ∈ closedCoordTriangle a b,
    ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
      |(fderivWithin ℝ first.r (closedCoordTriangle a b) p) e| ≤ R₁ ∧
      |(fderivWithin ℝ second.r (closedCoordTriangle a b) p) e| ≤ R₁
  /-- The radius difference vanishes linearly. -/
  r_sub_bound : ∀ p ∈ closedCoordTriangle a b,
    |first.r p - second.r p| ≤ (p.2 - p.1) * D
  /-- The radius-jet difference has a common bound. -/
  r_jet_sub_bound : ∀ p ∈ closedCoordTriangle a b,
    ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
      |(fderivWithin ℝ first.r (closedCoordTriangle a b) p) e -
        (fderivWithin ℝ second.r (closedCoordTriangle a b) p) e| ≤ RΔ * D

/-- The common box gives a positive gap away from the diagonal and a
unit upper bound for the coordinate gap. -/
theorem CubicRationalPairBox.gap_bounds
    {a b c : ℝ} (B : CubicRationalPairBox a b c)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hstrict : p.1 < p.2) :
    0 < p.2 - p.1 ∧ p.2 - p.1 ≤ 1 ∧
      c * (p.2 - p.1) ≤ B.first.r p ∧
      c * (p.2 - p.1) ≤ B.second.r p := by
  have hd : 0 < p.2 - p.1 := sub_pos.mpr hstrict
  have hdle : p.2 - p.1 ≤ 1 := by
    have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
    linarith [B.width_le_one]
  have hr₁ : c * (p.2 - p.1) ≤ B.first.r p := by
    rw [B.first.r_factor p hp]
    nlinarith only [B.first.ρ_lower p hp, hd.le]
  have hr₂ : c * (p.2 - p.1) ≤ B.second.r p := by
    rw [B.second.r_factor p hp]
    nlinarith only [B.second.ρ_lower p hp, hd.le]
  exact ⟨hd, hdle, hr₁, hr₂⟩

/-- The two removable cubic-over-linear quotients satisfy the expected
quadratic value bounds, including at the diagonal. -/
theorem CubicRationalPairBox.linearQuotient_value_bounds
    {a b c : ℝ} (B : CubicRationalPairBox a b c) (hc : 0 < c) :
    ∀ p ∈ closedCoordTriangle a b,
      0 ≤ cubicLinearQuotient B.first.J B.first.r p ∧
      cubicLinearQuotient B.first.J B.first.r p ≤
        (B.J₀ / c) * (p.2 - p.1) ^ 2 ∧
      0 ≤ cubicLinearQuotient B.second.J B.second.r p ∧
      cubicLinearQuotient B.second.J B.second.r p ≤
        (B.J₀ / c) * (p.2 - p.1) ^ 2 := by
  intro p hp
  by_cases hstrict : p.1 < p.2
  · obtain ⟨hd, _, hr₁, hr₂⟩ := B.gap_bounds hp hstrict
    have hj := B.J_bound p hp
    have hr₁pos : 0 < B.first.r p := (mul_pos hc hd).trans_le hr₁
    have hr₂pos : 0 < B.second.r p := (mul_pos hc hd).trans_le hr₂
    have h₁ := abs_div_le_of_cubic_gap_bound hc hd hr₁
      (by rw [abs_of_nonneg hj.1.1]; exact hj.1.2)
    have h₂ := abs_div_le_of_cubic_gap_bound hc hd hr₂
      (by rw [abs_of_nonneg hj.2.1]; exact hj.2.2)
    simpa [cubicLinearQuotient, hstrict, abs_of_nonneg
      (div_nonneg hj.1.1 hr₁pos.le), abs_of_nonneg
      (div_nonneg hj.2.1 hr₂pos.le)] using
        And.intro (div_nonneg hj.1.1 hr₁pos.le)
          (And.intro h₁ (And.intro (div_nonneg hj.2.1 hr₂pos.le) h₂))
  · have hd : 0 ≤ p.2 - p.1 := sub_nonneg.mpr hp.2.1
    simp only [cubicLinearQuotient, hstrict, ↓reduceIte]
    have hnonneg := mul_nonneg (div_nonneg B.J₀_nonneg hc.le) (sq_nonneg (p.2 - p.1))
    exact ⟨le_refl _, hnonneg, le_refl _, hnonneg⟩

/-- A common off-diagonal complementary gap extends to the diagonal for
both nonnegative cubic-over-linear quotients. The nondegenerate triangle
forces the proposed gap constant to be at most one. -/
theorem CubicRationalPairBox.offDiagonal_gap_closed
    {a b c ε : ℝ} (B : CubicRationalPairBox a b c)
    (hab : a < b) (hc : 0 < c)
    (hfirst : ∀ p ∈ closedCoordTriangle a b, p.1 < p.2 →
      cubicLinearQuotient B.first.J B.first.r p ≤ 1 - ε)
    (hsecond : ∀ p ∈ closedCoordTriangle a b, p.1 < p.2 →
      cubicLinearQuotient B.second.J B.second.r p ≤ 1 - ε) :
    (∀ p ∈ closedCoordTriangle a b,
      ε ≤ 1 - cubicLinearQuotient B.first.J B.first.r p) ∧
    (∀ p ∈ closedCoordTriangle a b,
      ε ≤ 1 - cubicLinearQuotient B.second.J B.second.r p) := by
  have habmem : (a, b) ∈ closedCoordTriangle a b :=
    ⟨le_rfl, hab.le, le_rfl⟩
  have hnonneg := (B.linearQuotient_value_bounds hc (a, b) habmem).1
  have hεone : ε ≤ 1 := by
    have h := hfirst (a, b) habmem hab
    linarith
  constructor
  · intro p hp
    by_cases hstrict : p.1 < p.2
    · linarith [hfirst p hp hstrict]
    · simp only [cubicLinearQuotient, hstrict, ↓reduceIte]
      linarith
  · intro p hp
    by_cases hstrict : p.1 < p.2
    · linarith [hsecond p hp hstrict]
    · simp only [cubicLinearQuotient, hstrict, ↓reduceIte]
      linarith

/-- The two-input value difference for the cubic-over-linear quotient has
the coefficient from the ordinary quotient subtraction ledger. -/
theorem CubicRationalPairBox.linearQuotient_sub_bound
    {a b c : ℝ} (B : CubicRationalPairBox a b c) (hc : 0 < c) :
    ∀ p ∈ closedCoordTriangle a b,
      |cubicLinearQuotient B.first.J B.first.r p -
        cubicLinearQuotient B.second.J B.second.r p| ≤
          (B.JΔ₀ / c + B.J₀ / c ^ 2) * (p.2 - p.1) ^ 2 * B.D := by
  intro p hp
  by_cases hstrict : p.1 < p.2
  · obtain ⟨hd, _, hr₁, hr₂⟩ := B.gap_bounds hp hstrict
    have hJ₂ := (B.J_bound p hp).2
    have h := abs_div_sub_div_le_of_cubic_gap_bounds hc hd hr₁ hr₂
      (B.r_sub_bound p hp)
      (by rw [abs_of_nonneg hJ₂.1]; exact hJ₂.2)
      (B.J_sub_bound p hp)
    simpa [cubicLinearQuotient, hstrict] using h
  · have hd : 0 ≤ p.2 - p.1 := sub_nonneg.mpr hp.2.1
    simp only [cubicLinearQuotient, hstrict, ↓reduceIte, sub_self, abs_zero]
    have hcoef : 0 ≤ B.JΔ₀ / c + B.J₀ / c ^ 2 :=
      add_nonneg (div_nonneg B.JΔ₀_nonneg hc.le)
        (div_nonneg B.J₀_nonneg (sq_nonneg c))
    exact mul_nonneg (mul_nonneg hcoef (sq_nonneg _)) B.D_nonneg

/-- The squared quotient has a linear value bound and a linear two-input
difference on the closed triangle. -/
theorem CubicRationalPairBox.squaredQuotient_value_bounds
    {a b c : ℝ} (B : CubicRationalPairBox a b c) (hc : 0 < c) :
    ∀ p ∈ closedCoordTriangle a b,
      |cubicSquaredQuotient B.first.J B.first.r p| ≤
        (B.J₀ / c ^ 2) * (p.2 - p.1) ∧
      |cubicSquaredQuotient B.second.J B.second.r p| ≤
        (B.J₀ / c ^ 2) * (p.2 - p.1) ∧
      |cubicSquaredQuotient B.first.J B.first.r p -
        cubicSquaredQuotient B.second.J B.second.r p| ≤
          (B.JΔ₀ / c ^ 2 + 2 * B.J₀ / c ^ 3) *
            (p.2 - p.1) * B.D := by
  intro p hp
  by_cases hstrict : p.1 < p.2
  · obtain ⟨hd, _, hr₁, hr₂⟩ := B.gap_bounds hp hstrict
    have hJ := B.J_bound p hp
    have h₁ := abs_div_sq_le_of_cubic_gap_bound hc hd hr₁
      (by rw [abs_of_nonneg hJ.1.1]; exact hJ.1.2)
    have h₂ := abs_div_sq_le_of_cubic_gap_bound hc hd hr₂
      (by rw [abs_of_nonneg hJ.2.1]; exact hJ.2.2)
    have hΔ := abs_div_sq_sub_div_sq_le_of_cubic_gap_bounds hc hd
      B.J₀_nonneg B.JΔ₀_nonneg B.D_nonneg hr₁ hr₂ (B.r_sub_bound p hp)
      (by rw [abs_of_nonneg hJ.2.1]; exact hJ.2.2)
      (B.J_sub_bound p hp)
    simpa [cubicSquaredQuotient, hstrict] using And.intro h₁ (And.intro h₂ hΔ)
  · have hd : 0 ≤ p.2 - p.1 := sub_nonneg.mpr hp.2.1
    simp only [cubicSquaredQuotient, hstrict, ↓reduceIte, abs_zero, sub_self]
    have hA : 0 ≤ B.J₀ / c ^ 2 * (p.2 - p.1) :=
      mul_nonneg (div_nonneg B.J₀_nonneg (sq_nonneg c)) hd
    have hΔcoef : 0 ≤ B.JΔ₀ / c ^ 2 + 2 * B.J₀ / c ^ 3 := by
      apply add_nonneg
      · exact div_nonneg B.JΔ₀_nonneg (pow_nonneg hc.le 2)
      · exact div_nonneg (mul_nonneg (by norm_num) B.J₀_nonneg)
          (pow_nonneg hc.le 3)
    exact ⟨hA, hA, mul_nonneg (mul_nonneg hΔcoef hd) B.D_nonneg⟩

end intervalIntegral

end
