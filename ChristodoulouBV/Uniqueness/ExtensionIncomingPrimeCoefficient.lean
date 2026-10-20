module

public import ChristodoulouBV.Uniqueness.ExtensionIncomingPrimeGronwall
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

/-!
# A bounded coefficient form of equation (5.2)

On an off-axis strip, the established uniform field and gap bounds give a
constant coefficient differential inequality for the outgoing derivative.
-/

public section

namespace ChristodoulouBV.Uniqueness

/-- Elementary coefficient estimate for the right side of equation (5.2).
The constants depend only on the uniform strip bounds. -/
theorem alphaPrime_rhs_abs_le
    {nu r mu q lam theta P ρ N q₀ l M : ℝ}
    (hρ : 0 < ρ) (hr : ρ ≤ r) (hN : 0 ≤ N) (hnu : |nu| ≤ N)
    (hmu : 0 ≤ mu ∧ mu ≤ 1) (hq₀ : 0 < q₀) (hq : q₀ ≤ q)
    (hl : 0 < l) (hlam : l ≤ lam) (hM : 0 ≤ M) (htheta : |theta| ≤ M) :
    |(-2 * (nu / r) * (mu / q) * P +
      3 * (nu / r ^ 2) * (mu / q) * (theta / lam) -
      (nu / r ^ 2) * (1 / q) * (theta / lam) ^ 3)| ≤
      (2 * (N / ρ) * (1 / q₀)) * |P| +
        (3 * (N / ρ ^ 2) * (1 / q₀) * (M / l) +
          (N / ρ ^ 2) * (1 / q₀) * (M / l) ^ 3) := by
  have hrpos : 0 < r := hρ.trans_le hr
  have hqpos : 0 < q := hq₀.trans_le hq
  have hlampos : 0 < lam := hl.trans_le hlam
  have hr2 : ρ ^ 2 ≤ r ^ 2 := by nlinarith only [hρ, hr]
  have hA : |nu / r| ≤ N / ρ := by
    rw [abs_div, abs_of_pos hrpos]
    apply (div_le_div_iff₀ hrpos hρ).2
    calc
      |nu| * ρ ≤ N * ρ := mul_le_mul_of_nonneg_right hnu hρ.le
      _ ≤ N * r := mul_le_mul_of_nonneg_left hr hN
  have hB : |nu / r ^ 2| ≤ N / ρ ^ 2 := by
    rw [abs_div, abs_of_pos (sq_pos_of_pos hrpos)]
    apply (div_le_div_iff₀ (sq_pos_of_pos hrpos) (sq_pos_of_pos hρ)).2
    calc
      |nu| * ρ ^ 2 ≤ N * ρ ^ 2 :=
        mul_le_mul_of_nonneg_right hnu (sq_nonneg ρ)
      _ ≤ N * r ^ 2 := mul_le_mul_of_nonneg_left hr2 hN
  have hQ : |mu / q| ≤ 1 / q₀ := by
    rw [abs_div, abs_of_nonneg hmu.1, abs_of_pos hqpos]
    apply (div_le_div_iff₀ hqpos hq₀).2
    calc
      mu * q₀ ≤ 1 * q₀ := mul_le_mul_of_nonneg_right hmu.2 hq₀.le
      _ ≤ 1 * q := by simpa only [one_mul] using hq
  have hInv : |(1 : ℝ) / q| ≤ 1 / q₀ := by
    rw [abs_div, abs_one, abs_of_pos hqpos]
    exact one_div_le_one_div_of_le hq₀ hq
  have hT : |theta / lam| ≤ M / l := by
    rw [abs_div, abs_of_pos hlampos]
    apply (div_le_div_iff₀ hlampos hl).2
    calc
      |theta| * l ≤ M * l := mul_le_mul_of_nonneg_right htheta hl.le
      _ ≤ M * lam := mul_le_mul_of_nonneg_left hlam hM
  have hA0 : 0 ≤ N / ρ := div_nonneg hN hρ.le
  have hB0 : 0 ≤ N / ρ ^ 2 := div_nonneg hN (sq_nonneg ρ)
  have hQ0 : 0 ≤ 1 / q₀ := by positivity
  have hT0 : 0 ≤ M / l := div_nonneg hM hl.le
  have hterm1 : |(-2 * (nu / r) * (mu / q) * P)| ≤
      (2 * (N / ρ) * (1 / q₀)) * |P| := by
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    gcongr
  have hterm2 : |3 * (nu / r ^ 2) * (mu / q) * (theta / lam)| ≤
      3 * (N / ρ ^ 2) * (1 / q₀) * (M / l) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    gcongr
  have hterm3 : |(nu / r ^ 2) * (1 / q) * (theta / lam) ^ 3| ≤
      (N / ρ ^ 2) * (1 / q₀) * (M / l) ^ 3 := by
    rw [abs_mul, abs_mul, abs_pow]
    gcongr
  have htri : |(-2 * (nu / r) * (mu / q) * P +
      3 * (nu / r ^ 2) * (mu / q) * (theta / lam)) -
      ((nu / r ^ 2) * (1 / q) * (theta / lam) ^ 3)| ≤
      |(-2 * (nu / r) * (mu / q) * P +
        3 * (nu / r ^ 2) * (mu / q) * (theta / lam))| +
      |(nu / r ^ 2) * (1 / q) * (theta / lam) ^ 3| := by
    let A := -2 * (nu / r) * (mu / q) * P +
      3 * (nu / r ^ 2) * (mu / q) * (theta / lam)
    let B := (nu / r ^ 2) * (1 / q) * (theta / lam) ^ 3
    change |A - B| ≤ |A| + |B|
    calc
      |A - B| ≤ |A| + |-B| := by
        simpa only [sub_eq_add_neg] using abs_add_le A (-B)
      _ = |A| + |B| := by rw [abs_neg]
  have htri2 := abs_add_le
    (-2 * (nu / r) * (mu / q) * P)
    (3 * (nu / r ^ 2) * (mu / q) * (theta / lam))
  linarith only [hterm1, hterm2, hterm3, htri, htri2]

end ChristodoulouBV.Uniqueness

end
