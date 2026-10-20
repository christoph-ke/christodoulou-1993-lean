module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Algebra for the unweighted terminal transport bootstrap

The first mass improvement makes the mass ratio linear in radius. These
pointwise inequalities show that all three terms in (5.2) have the same
integrable square-root radius singularity.
-/

public section

namespace ChristodoulouBV.Uniqueness

/-- The unsigned three-term coefficient in (5.2), expressed in the coordinate
`x = √r`, has at most a `1/x` singularity. -/
theorem transport_coefficient_le_sqrt_radius
    {x μ p f A M : ℝ}
    (hx : 0 < x) (hM : 0 ≤ M)
    (hμ : μ ≤ M * x ^ 2)
    (hp : x * |p| ≤ A)
    (hf : |f| ≤ (2 * A / 3) * x) :
    2 * μ * |p| / x ^ 2 +
      3 * μ * |f| / x ^ 4 + |f| ^ 3 / x ^ 4 ≤
        (4 * M * A + 8 * A ^ 3 / 27) / x := by
  have hx2 : 0 < x ^ 2 := pow_pos hx _
  have hx4 : 0 < x ^ 4 := pow_pos hx _
  have h1 : μ * |p| ≤ M * A * x := by
    calc
      μ * |p| ≤ (M * x ^ 2) * |p| :=
        mul_le_mul_of_nonneg_right hμ (abs_nonneg _)
      _ = (M * x) * (x * |p|) := by ring
      _ ≤ (M * x) * A :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg hM hx.le)
      _ = M * A * x := by ring
  have h2 : μ * |f| ≤ (2 * M * A / 3) * x ^ 3 := by
    calc
      μ * |f| ≤ (M * x ^ 2) * |f| :=
        mul_le_mul_of_nonneg_right hμ (abs_nonneg _)
      _ ≤ (M * x ^ 2) * ((2 * A / 3) * x) :=
        mul_le_mul_of_nonneg_left hf
          (mul_nonneg hM (sq_nonneg _))
      _ = (2 * M * A / 3) * x ^ 3 := by ring
  have h3 : |f| ^ 3 ≤ (8 * A ^ 3 / 27) * x ^ 3 := by
    calc
      |f| ^ 3 ≤ ((2 * A / 3) * x) ^ 3 := by gcongr
      _ = (8 * A ^ 3 / 27) * x ^ 3 := by ring
  have hterm1 : 2 * μ * |p| / x ^ 2 ≤ 2 * M * A / x := by
    apply (div_le_div_iff₀ hx2 hx).2
    have h := mul_le_mul_of_nonneg_right h1 hx.le
    nlinarith only [h]
  have hterm2 : 3 * μ * |f| / x ^ 4 ≤ 2 * M * A / x := by
    apply (div_le_div_iff₀ hx4 hx).2
    have h := mul_le_mul_of_nonneg_right h2 hx.le
    nlinarith only [h]
  have hterm3 : |f| ^ 3 / x ^ 4 ≤ (8 * A ^ 3 / 27) / x := by
    apply (div_le_div_iff₀ hx4 hx).2
    have h := mul_le_mul_of_nonneg_right h3 hx.le
    nlinarith only [h]
  calc
    2 * μ * |p| / x ^ 2 +
        3 * μ * |f| / x ^ 4 + |f| ^ 3 / x ^ 4 ≤
          2 * M * A / x + 2 * M * A / x +
            (8 * A ^ 3 / 27) / x := by
      exact add_le_add (add_le_add hterm1 hterm2) hterm3
    _ = (4 * M * A + 8 * A ^ 3 / 27) / x := by ring

/-- The full signed right-hand side of (5.2) is controlled by the incoming
square-root radius primitive when the mass gap is at least `q₀`. -/
theorem abs_transport_rhs_le_sqrt_radius
    {x ν μ q q₀ p f A M : ℝ}
    (hx : 0 < x) (hν : ν ≤ 0) (hμ0 : 0 ≤ μ)
    (hq₀ : 0 < q₀) (hq : q₀ ≤ q)
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hμ : μ ≤ M * x ^ 2)
    (hp : x * |p| ≤ A)
    (hf : |f| ≤ (2 * A / 3) * x) :
    |-2 * (ν / x ^ 2) * (μ / q) * p +
        3 * (ν / x ^ 4) * (μ / q) * f -
        (ν / x ^ 4) * (1 / q) * f ^ 3| ≤
      ((4 * M * A + 8 * A ^ 3 / 27) / q₀) * ((-ν) / x) := by
  let C : ℝ := 4 * M * A + 8 * A ^ 3 / 27
  let T : ℝ := -2 * μ * p / x ^ 2 + 3 * μ * f / x ^ 4 - f ^ 3 / x ^ 4
  have hqpos : 0 < q := hq₀.trans_le hq
  have hx2 : 0 < x ^ 2 := pow_pos hx _
  have hx4 : 0 < x ^ 4 := pow_pos hx _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcoef : 2 * μ * |p| / x ^ 2 +
      3 * μ * |f| / x ^ 4 + |f| ^ 3 / x ^ 4 ≤ C / x := by
    dsimp [C]
    exact transport_coefficient_le_sqrt_radius hx hM hμ hp hf
  have hterm1 : |-2 * μ * p / x ^ 2| = 2 * μ * |p| / x ^ 2 := by
    rw [abs_div, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg hμ0, abs_of_pos hx2]
  have hterm2 : |3 * μ * f / x ^ 4| = 3 * μ * |f| / x ^ 4 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
      abs_of_nonneg hμ0, abs_of_pos hx4]
  have hterm3 : |-f ^ 3 / x ^ 4| = |f| ^ 3 / x ^ 4 := by
    rw [abs_div, abs_neg, abs_pow, abs_of_pos hx4]
  have hTtri : |T| ≤ 2 * μ * |p| / x ^ 2 +
      3 * μ * |f| / x ^ 4 + |f| ^ 3 / x ^ 4 := by
    have h1 := abs_add_le (-2 * μ * p / x ^ 2 + 3 * μ * f / x ^ 4)
      (-f ^ 3 / x ^ 4)
    have h2 := abs_add_le (-2 * μ * p / x ^ 2) (3 * μ * f / x ^ 4)
    rw [hterm1, hterm2] at h2
    rw [hterm3] at h1
    calc
      |T| = |-2 * μ * p / x ^ 2 + 3 * μ * f / x ^ 4 +
          -f ^ 3 / x ^ 4| := by congr 1; dsimp [T]; ring
      _ ≤ |-2 * μ * p / x ^ 2 + 3 * μ * f / x ^ 4| +
          |f| ^ 3 / x ^ 4 := h1
      _ ≤ 2 * μ * |p| / x ^ 2 +
          3 * μ * |f| / x ^ 4 + |f| ^ 3 / x ^ 4 := by
            linarith only [h2]
  have hrepr : -2 * (ν / x ^ 2) * (μ / q) * p +
        3 * (ν / x ^ 4) * (μ / q) * f -
        (ν / x ^ 4) * (1 / q) * f ^ 3 = (ν / q) * T := by
    dsimp [T]
    ring
  rw [hrepr, abs_mul, abs_div, abs_of_nonpos hν, abs_of_pos hqpos]
  have hqmon : (-ν) / q ≤ (-ν) / q₀ :=
    div_le_div_of_nonneg_left (neg_nonneg.mpr hν) hq₀ hq
  calc
    (-ν) / q * |T| ≤ (-ν) / q * (C / x) :=
      mul_le_mul_of_nonneg_left (hTtri.trans hcoef)
        (div_nonneg (neg_nonneg.mpr hν) hqpos.le)
    _ ≤ (-ν) / q₀ * (C / x) :=
      mul_le_mul_of_nonneg_right hqmon (div_nonneg hC hx.le)
    _ = (C / q₀) * ((-ν) / x) := by ring

end ChristodoulouBV.Uniqueness

end
