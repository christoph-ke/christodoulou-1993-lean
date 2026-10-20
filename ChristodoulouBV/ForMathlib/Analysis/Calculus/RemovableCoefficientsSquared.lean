module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficients
import Mathlib.Tactic

/-!
# Squared-denominator quotient estimates

These are scalar estimates for the value and first jet of a quotient with a
squared denominator. In particular, the derivative estimate keeps the factor
two from differentiating the square.
-/

public section

namespace intervalIntegral

/-- The Fréchet derivative of a quotient with a squared scalar denominator. -/
theorem fderiv_div_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hgne : g x ≠ 0) :
    fderiv ℝ (fun y => f y / g y ^ 2) x =
      (1 / g x ^ 2) • fderiv ℝ f x -
        (2 * f x / g x ^ 3) • fderiv ℝ g x := by
  have hgp := hg.hasFDerivAt.pow 2
  have hginv := (hasFDerivAt_inv (pow_ne_zero 2 hgne)).comp x hgp
  have hmul := hf.hasFDerivAt.mul hginv
  change fderiv ℝ (f * ((fun y : ℝ => y⁻¹) ∘ fun y => g y ^ 2)) x = _
  rw [hmul.fderiv]
  ext e
  simp only [add_apply, sub_apply, smul_apply, Function.comp_apply,
    ContinuousLinearMap.coe_comp, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]
  field_simp [hgne]
  ring

/-- Reciprocal cubes are Lipschitz on a positive half-line, with the bound
obtained by factoring a difference of cubes of reciprocals. -/
theorem abs_inv_cube_sub_inv_cube_le {c x y D : ℝ}
    (hc : 0 < c) (hx : c ≤ x) (hy : c ≤ y)
    (hxy : |x - y| ≤ D) :
    |(x ^ 3)⁻¹ - (y ^ 3)⁻¹| ≤ 3 * D / c ^ 4 := by
  have hxpos : 0 < x := hc.trans_le hx
  have hypos : 0 < y := hc.trans_le hy
  have hD : 0 ≤ D := (abs_nonneg _).trans hxy
  have hinv : |x⁻¹ - y⁻¹| ≤ D / c ^ 2 := by
    have h := abs_div_sub_div_le hc hx hy (x₁ := (1 : ℝ)) (x₂ := 1)
      (X := 0) (Y := D) (Z := 1) (by simp) hxy (by simp)
    simpa using h
  have hsq := abs_inv_sq_sub_inv_sq_le hc hx hy hxy
  have hxi : |x⁻¹| ≤ c⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr hxpos)]
    exact (inv_le_inv₀ hxpos hc).2 hx
  have hyi : |(y ^ 2)⁻¹| ≤ (c ^ 2)⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr (pow_pos hypos 2))]
    exact (inv_le_inv₀ (pow_pos hypos 2) (pow_pos hc 2)).2 (by gcongr)
  have hfirst : |((x ^ 2)⁻¹ - (y ^ 2)⁻¹) * x⁻¹| ≤
      (2 * D / c ^ 3) * c⁻¹ := by
    rw [abs_mul]
    exact mul_le_mul hsq hxi (abs_nonneg _) (div_nonneg (by positivity) (pow_nonneg hc.le 3))
  have hsecond : |(y ^ 2)⁻¹ * (x⁻¹ - y⁻¹)| ≤
      (c ^ 2)⁻¹ * (D / c ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul hyi hinv (abs_nonneg _) (inv_nonneg.mpr (pow_nonneg hc.le 2))
  have hid : (x ^ 3)⁻¹ - (y ^ 3)⁻¹ =
      ((x ^ 2)⁻¹ - (y ^ 2)⁻¹) * x⁻¹ +
        (y ^ 2)⁻¹ * (x⁻¹ - y⁻¹) := by ring
  rw [hid]
  calc
    _ ≤ |((x ^ 2)⁻¹ - (y ^ 2)⁻¹) * x⁻¹| +
        |(y ^ 2)⁻¹ * (x⁻¹ - y⁻¹)| := abs_add_le _ _
    _ ≤ (2 * D / c ^ 3) * c⁻¹ + (c ^ 2)⁻¹ * (D / c ^ 2) :=
      add_le_add hfirst hsecond
    _ = 3 * D / c ^ 4 := by field_simp [hc.ne']; ring

/-- The first jet of a quotient by a squared positive denominator has the
two-term bound from the quotient rule. -/
theorem abs_squaredQuotientJet_le
    {c j₀ p₀ R ρ J P S : ℝ}
    (hc : 0 < c) (hj₀ : 0 ≤ j₀) (hp₀ : 0 ≤ p₀) (hR : 0 ≤ R)
    (hρ : c ≤ ρ) (hJ : |J| ≤ j₀) (hP : |P| ≤ p₀)
    (hS : |S| ≤ R) :
    |P / ρ ^ 2 - 2 * J * S / ρ ^ 3| ≤
      p₀ / c ^ 2 + 2 * j₀ * R / c ^ 3 := by
  have hρpos : 0 < ρ := hc.trans_le hρ
  have hfirst : |P / ρ ^ 2| ≤ p₀ / c ^ 2 := by
    rw [abs_div, abs_of_pos (pow_pos hρpos 2)]
    gcongr
  have hsecond : |2 * J * S / ρ ^ 3| ≤ 2 * j₀ * R / c ^ 3 := by
    rw [abs_div, abs_of_pos (pow_pos hρpos 3), abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    gcongr
  calc
    _ ≤ |P / ρ ^ 2| + |2 * J * S / ρ ^ 3| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (P / ρ ^ 2) (-(2 * J * S / ρ ^ 3))
    _ ≤ p₀ / c ^ 2 + 2 * j₀ * R / c ^ 3 := add_le_add hfirst hsecond

/-- The five sources of variation in the jet of a squared-denominator
quotient give the derivative ledger with coefficients `2` and `6`. -/
theorem abs_squaredQuotientJet_sub_le
    {c j₀ p₀ jΔ₀ pΔ₀ R RΔ D : ℝ}
    {ρ₁ ρ₂ J₁ J₂ P₁ P₂ S₁ S₂ : ℝ}
    (hc : 0 < c) (hj₀ : 0 ≤ j₀) (hp₀ : 0 ≤ p₀)
    (hjΔ₀ : 0 ≤ jΔ₀) (hpΔ₀ : 0 ≤ pΔ₀)
    (hR : 0 ≤ R) (hRΔ : 0 ≤ RΔ) (hD : 0 ≤ D)
    (hρ₁ : c ≤ ρ₁) (hρ₂ : c ≤ ρ₂)
    (hρdiff : |ρ₁ - ρ₂| ≤ D)
    (hJ₂ : |J₂| ≤ j₀) (hJdiff : |J₁ - J₂| ≤ jΔ₀ * D)
    (hP₂ : |P₂| ≤ p₀) (hPdiff : |P₁ - P₂| ≤ pΔ₀ * D)
    (hS₁ : |S₁| ≤ R) (hS₂ : |S₂| ≤ R)
    (hSdiff : |S₁ - S₂| ≤ RΔ * D) :
    |(P₁ / ρ₁ ^ 2 - 2 * J₁ * S₁ / ρ₁ ^ 3) -
      (P₂ / ρ₂ ^ 2 - 2 * J₂ * S₂ / ρ₂ ^ 3)| ≤
      (pΔ₀ / c ^ 2 + 2 * p₀ / c ^ 3 +
        2 * jΔ₀ * R / c ^ 3 + 2 * j₀ * RΔ / c ^ 3 +
        6 * j₀ * R / c ^ 4) * D := by
  have hρ₁pos : 0 < ρ₁ := hc.trans_le hρ₁
  have hρ₂pos : 0 < ρ₂ := hc.trans_le hρ₂
  have hsq := abs_inv_sq_sub_inv_sq_le hc hρ₁ hρ₂ hρdiff
  have hcube := abs_inv_cube_sub_inv_cube_le hc hρ₁ hρ₂ hρdiff
  have hsq₁ : |(ρ₁ ^ 2)⁻¹| ≤ (c ^ 2)⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr (pow_pos hρ₁pos 2))]
    exact (inv_le_inv₀ (pow_pos hρ₁pos 2) (pow_pos hc 2)).2 (by gcongr)
  have hcube₁ : |(ρ₁ ^ 3)⁻¹| ≤ (c ^ 3)⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr (pow_pos hρ₁pos 3))]
    exact (inv_le_inv₀ (pow_pos hρ₁pos 3) (pow_pos hc 3)).2 (by gcongr)
  have hprod : |J₁ * S₁ - J₂ * S₂| ≤
      (jΔ₀ * R + j₀ * RΔ) * D := by
    have hid : J₁ * S₁ - J₂ * S₂ =
        (J₁ - J₂) * S₁ + J₂ * (S₁ - S₂) := by ring
    rw [hid]
    have ha : |(J₁ - J₂) * S₁| ≤ jΔ₀ * D * R := by
      rw [abs_mul]
      exact mul_le_mul hJdiff hS₁ (abs_nonneg _) (mul_nonneg hjΔ₀ hD)
    have hb : |J₂ * (S₁ - S₂)| ≤ j₀ * (RΔ * D) := by
      rw [abs_mul]
      exact mul_le_mul hJ₂ hSdiff (abs_nonneg _) hj₀
    nlinarith only [(abs_add_le _ _).trans (add_le_add ha hb)]
  have hprod₂ : |J₂ * S₂| ≤ j₀ * R := by
    rw [abs_mul]
    exact mul_le_mul hJ₂ hS₂ (abs_nonneg _) hj₀
  have hfirst : |P₁ / ρ₁ ^ 2 - P₂ / ρ₂ ^ 2| ≤
      (pΔ₀ / c ^ 2 + 2 * p₀ / c ^ 3) * D := by
    have hid : P₁ / ρ₁ ^ 2 - P₂ / ρ₂ ^ 2 =
        (P₁ - P₂) * (ρ₁ ^ 2)⁻¹ +
          P₂ * ((ρ₁ ^ 2)⁻¹ - (ρ₂ ^ 2)⁻¹) := by
      simp only [div_eq_mul_inv]; ring
    rw [hid]
    have ha : |(P₁ - P₂) * (ρ₁ ^ 2)⁻¹| ≤
        (pΔ₀ * D) * (c ^ 2)⁻¹ := by
      rw [abs_mul]
      exact mul_le_mul hPdiff hsq₁ (abs_nonneg _) (mul_nonneg hpΔ₀ hD)
    have hb : |P₂ * ((ρ₁ ^ 2)⁻¹ - (ρ₂ ^ 2)⁻¹)| ≤
        p₀ * (2 * D / c ^ 3) := by
      rw [abs_mul]
      exact mul_le_mul hP₂ hsq (abs_nonneg _) hp₀
    have h := (abs_add_le _ _).trans (add_le_add ha hb)
    calc
      _ ≤ pΔ₀ * D * (c ^ 2)⁻¹ + p₀ * (2 * D / c ^ 3) := h
      _ = (pΔ₀ / c ^ 2 + 2 * p₀ / c ^ 3) * D := by field_simp [hc.ne']
  have hsecond : |J₁ * S₁ / ρ₁ ^ 3 - J₂ * S₂ / ρ₂ ^ 3| ≤
      (jΔ₀ * R / c ^ 3 + j₀ * RΔ / c ^ 3 +
        3 * j₀ * R / c ^ 4) * D := by
    have hid : J₁ * S₁ / ρ₁ ^ 3 - J₂ * S₂ / ρ₂ ^ 3 =
        (J₁ * S₁ - J₂ * S₂) * (ρ₁ ^ 3)⁻¹ +
          J₂ * S₂ * ((ρ₁ ^ 3)⁻¹ - (ρ₂ ^ 3)⁻¹) := by
      simp only [div_eq_mul_inv]; ring
    rw [hid]
    have ha : |(J₁ * S₁ - J₂ * S₂) * (ρ₁ ^ 3)⁻¹| ≤
        ((jΔ₀ * R + j₀ * RΔ) * D) * (c ^ 3)⁻¹ := by
      rw [abs_mul]
      exact mul_le_mul hprod hcube₁ (abs_nonneg _) (by positivity)
    have hb : |J₂ * S₂ * ((ρ₁ ^ 3)⁻¹ - (ρ₂ ^ 3)⁻¹)| ≤
        (j₀ * R) * (3 * D / c ^ 4) := by
      rw [abs_mul]
      exact mul_le_mul hprod₂ hcube (abs_nonneg _) (mul_nonneg hj₀ hR)
    have h := (abs_add_le _ _).trans (add_le_add ha hb)
    calc
      _ ≤ ((jΔ₀ * R + j₀ * RΔ) * D) * (c ^ 3)⁻¹ +
          (j₀ * R) * (3 * D / c ^ 4) := h
      _ = (jΔ₀ * R / c ^ 3 + j₀ * RΔ / c ^ 3 +
          3 * j₀ * R / c ^ 4) * D := by field_simp [hc.ne']
  have hid : (P₁ / ρ₁ ^ 2 - 2 * J₁ * S₁ / ρ₁ ^ 3) -
      (P₂ / ρ₂ ^ 2 - 2 * J₂ * S₂ / ρ₂ ^ 3) =
      (P₁ / ρ₁ ^ 2 - P₂ / ρ₂ ^ 2) -
        2 * (J₁ * S₁ / ρ₁ ^ 3 - J₂ * S₂ / ρ₂ ^ 3) := by ring
  rw [hid]
  have htri : |(P₁ / ρ₁ ^ 2 - P₂ / ρ₂ ^ 2) -
      2 * (J₁ * S₁ / ρ₁ ^ 3 - J₂ * S₂ / ρ₂ ^ 3)| ≤
      |P₁ / ρ₁ ^ 2 - P₂ / ρ₂ ^ 2| +
        2 * |J₁ * S₁ / ρ₁ ^ 3 - J₂ * S₂ / ρ₂ ^ 3| := by
    calc
      _ ≤ |P₁ / ρ₁ ^ 2 - P₂ / ρ₂ ^ 2| +
          |2 * (J₁ * S₁ / ρ₁ ^ 3 - J₂ * S₂ / ρ₂ ^ 3)| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              (abs_sub_le (P₁ / ρ₁ ^ 2 - P₂ / ρ₂ ^ 2) 0
                (2 * (J₁ * S₁ / ρ₁ ^ 3 - J₂ * S₂ / ρ₂ ^ 3)))
      _ = _ := by rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h := htri.trans (add_le_add hfirst
    (mul_le_mul_of_nonneg_left hsecond (by norm_num)))
  calc
    _ ≤ (pΔ₀ / c ^ 2 + 2 * p₀ / c ^ 3) * D +
        2 * ((jΔ₀ * R / c ^ 3 + j₀ * RΔ / c ^ 3 +
          3 * j₀ * R / c ^ 4) * D) := h
    _ = _ := by ring

/-- A two-input value bound for a quotient with a squared positive denominator. -/
theorem abs_div_sq_sub_div_sq_le
    {c j₀ jΔ₀ D ρ₁ ρ₂ J₁ J₂ : ℝ}
    (hc : 0 < c) (hj₀ : 0 ≤ j₀) (hjΔ₀ : 0 ≤ jΔ₀) (hD : 0 ≤ D)
    (hρ₁ : c ≤ ρ₁) (hρ₂ : c ≤ ρ₂)
    (hρdiff : |ρ₁ - ρ₂| ≤ D)
    (hJ₂ : |J₂| ≤ j₀) (hJdiff : |J₁ - J₂| ≤ jΔ₀ * D) :
    |J₁ / ρ₁ ^ 2 - J₂ / ρ₂ ^ 2| ≤
      (jΔ₀ / c ^ 2 + 2 * j₀ / c ^ 3) * D := by
  have hρ₁pos : 0 < ρ₁ := hc.trans_le hρ₁
  have hsq := abs_inv_sq_sub_inv_sq_le hc hρ₁ hρ₂ hρdiff
  have hsq₁ : |(ρ₁ ^ 2)⁻¹| ≤ (c ^ 2)⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr (pow_pos hρ₁pos 2))]
    exact (inv_le_inv₀ (pow_pos hρ₁pos 2) (pow_pos hc 2)).2 (by gcongr)
  have hid : J₁ / ρ₁ ^ 2 - J₂ / ρ₂ ^ 2 =
      (J₁ - J₂) * (ρ₁ ^ 2)⁻¹ +
        J₂ * ((ρ₁ ^ 2)⁻¹ - (ρ₂ ^ 2)⁻¹) := by
    simp only [div_eq_mul_inv]; ring
  rw [hid]
  have ha : |(J₁ - J₂) * (ρ₁ ^ 2)⁻¹| ≤
      (jΔ₀ * D) * (c ^ 2)⁻¹ := by
    rw [abs_mul]
    exact mul_le_mul hJdiff hsq₁ (abs_nonneg _) (mul_nonneg hjΔ₀ hD)
  have hb : |J₂ * ((ρ₁ ^ 2)⁻¹ - (ρ₂ ^ 2)⁻¹)| ≤
      j₀ * (2 * D / c ^ 3) := by
    rw [abs_mul]
    exact mul_le_mul hJ₂ hsq (abs_nonneg _) hj₀
  calc
    _ ≤ |(J₁ - J₂) * (ρ₁ ^ 2)⁻¹| +
        |J₂ * ((ρ₁ ^ 2)⁻¹ - (ρ₂ ^ 2)⁻¹)| := abs_add_le _ _
    _ ≤ (jΔ₀ * D) * (c ^ 2)⁻¹ + j₀ * (2 * D / c ^ 3) :=
      add_le_add ha hb
    _ = (jΔ₀ / c ^ 2 + 2 * j₀ / c ^ 3) * D := by field_simp [hc.ne']

/-- A cubic numerator over a squared linear denominator vanishes linearly. -/
theorem abs_div_sq_le_of_cubic_gap_bound
    {c d j₀ r j : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hr : c * d ≤ r) (hj : |j| ≤ j₀ * d ^ 3) :
    |j / r ^ 2| ≤ (j₀ / c ^ 2) * d := by
  have hrpos : 0 < r := (mul_pos hc hd).trans_le hr
  have hjs : 0 ≤ j₀ * d ^ 3 := (abs_nonneg _).trans hj
  rw [abs_div, abs_of_pos (pow_pos hrpos 2)]
  calc
    _ ≤ (j₀ * d ^ 3) / (c * d) ^ 2 := by gcongr
    _ = (j₀ / c ^ 2) * d := by field_simp [hc.ne', hd.ne']

/-- The two-input value estimate for cubically vanishing numerators over
squared linear denominators. -/
theorem abs_div_sq_sub_div_sq_le_of_cubic_gap_bounds
    {c d j₀ jΔ₀ D r₁ r₂ J₁ J₂ : ℝ}
    (hc : 0 < c) (hd : 0 < d)
    (hj₀ : 0 ≤ j₀) (hjΔ₀ : 0 ≤ jΔ₀) (hD : 0 ≤ D)
    (hr₁ : c * d ≤ r₁) (hr₂ : c * d ≤ r₂)
    (hrdiff : |r₁ - r₂| ≤ d * D)
    (hJ₂ : |J₂| ≤ j₀ * d ^ 3)
    (hJdiff : |J₁ - J₂| ≤ jΔ₀ * d ^ 3 * D) :
    |J₁ / r₁ ^ 2 - J₂ / r₂ ^ 2| ≤
      (jΔ₀ / c ^ 2 + 2 * j₀ / c ^ 3) * d * D := by
  have hρ₁ : c ≤ r₁ / d := (le_div_iff₀ hd).2 (by nlinarith only [hr₁])
  have hρ₂ : c ≤ r₂ / d := (le_div_iff₀ hd).2 (by nlinarith only [hr₂])
  have hρdiff : |r₁ / d - r₂ / d| ≤ D := by
    rw [← sub_div, abs_div, abs_of_pos hd]
    exact (div_le_iff₀ hd).2 (by simpa only [mul_comm] using hrdiff)
  have hJ₂' : |J₂ / d ^ 3| ≤ j₀ := by
    rw [abs_div, abs_of_pos (pow_pos hd 3)]
    exact (div_le_iff₀ (pow_pos hd 3)).2 (by nlinarith only [hJ₂])
  have hJdiff' : |J₁ / d ^ 3 - J₂ / d ^ 3| ≤ jΔ₀ * D := by
    rw [← sub_div, abs_div, abs_of_pos (pow_pos hd 3)]
    exact (div_le_iff₀ (pow_pos hd 3)).2 (by nlinarith only [hJdiff])
  have h := abs_div_sq_sub_div_sq_le hc hj₀ hjΔ₀ hD
    hρ₁ hρ₂ hρdiff hJ₂' hJdiff'
  have hnorm : ∀ r J : ℝ, r ≠ 0 →
      (J / d ^ 3) / (r / d) ^ 2 = (J / r ^ 2) / d := by
    intro r J hr
    field_simp [hd.ne', hr]
  rw [hnorm r₁ J₁ (ne_of_gt ((mul_pos hc hd).trans_le hr₁)),
    hnorm r₂ J₂ (ne_of_gt ((mul_pos hc hd).trans_le hr₂)),
    ← sub_div, abs_div, abs_of_pos hd] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using (div_le_iff₀ hd).1 h

/-- The first jet of a cubically vanishing numerator over a squared linear
denominator is bounded uniformly down to the diagonal. -/
theorem abs_squaredQuotientJet_le_of_cubic_gap_bounds
    {c d j₀ p₀ R r j ji ri : ℝ}
    (hc : 0 < c) (hd : 0 < d)
    (hj₀ : 0 ≤ j₀) (hp₀ : 0 ≤ p₀) (hR : 0 ≤ R)
    (hr : c * d ≤ r)
    (hj : |j| ≤ j₀ * d ^ 3)
    (hji : |ji| ≤ p₀ * d ^ 2)
    (hri : |ri| ≤ R) :
    |ji / r ^ 2 - 2 * j * ri / r ^ 3| ≤
      p₀ / c ^ 2 + 2 * j₀ * R / c ^ 3 := by
  have hρ : c ≤ r / d := (le_div_iff₀ hd).2 (by nlinarith only [hr])
  have hJ : |j / d ^ 3| ≤ j₀ := by
    rw [abs_div, abs_of_pos (pow_pos hd 3)]
    exact (div_le_iff₀ (pow_pos hd 3)).2 (by nlinarith only [hj])
  have hP : |ji / d ^ 2| ≤ p₀ := by
    rw [abs_div, abs_of_pos (pow_pos hd 2)]
    exact (div_le_iff₀ (pow_pos hd 2)).2 (by nlinarith only [hji])
  have h := abs_squaredQuotientJet_le hc hj₀ hp₀ hR hρ hJ hP hri
  have hrne : r ≠ 0 := ne_of_gt ((mul_pos hc hd).trans_le hr)
  have hid : (ji / d ^ 2) / (r / d) ^ 2 -
      2 * (j / d ^ 3) * ri / (r / d) ^ 3 =
      ji / r ^ 2 - 2 * j * ri / r ^ 3 := by
    field_simp [hd.ne', hrne]
  rwa [hid] at h

/-- The two-input first-jet estimate for cubically vanishing numerators over
squared linear denominators has the five quotient-rule terms. -/
theorem abs_squaredQuotientJet_sub_le_of_cubic_gap_bounds
    {c d j₀ p₀ jΔ₀ pΔ₀ R RΔ D : ℝ}
    {r₁ r₂ J₁ J₂ P₁ P₂ S₁ S₂ : ℝ}
    (hc : 0 < c) (hd : 0 < d)
    (hj₀ : 0 ≤ j₀) (hp₀ : 0 ≤ p₀)
    (hjΔ₀ : 0 ≤ jΔ₀) (hpΔ₀ : 0 ≤ pΔ₀)
    (hR : 0 ≤ R) (hRΔ : 0 ≤ RΔ) (hD : 0 ≤ D)
    (hr₁ : c * d ≤ r₁) (hr₂ : c * d ≤ r₂)
    (hrdiff : |r₁ - r₂| ≤ d * D)
    (hJ₂ : |J₂| ≤ j₀ * d ^ 3)
    (hJdiff : |J₁ - J₂| ≤ jΔ₀ * d ^ 3 * D)
    (hP₂ : |P₂| ≤ p₀ * d ^ 2)
    (hPdiff : |P₁ - P₂| ≤ pΔ₀ * d ^ 2 * D)
    (hS₁ : |S₁| ≤ R) (hS₂ : |S₂| ≤ R)
    (hSdiff : |S₁ - S₂| ≤ RΔ * D) :
    |(P₁ / r₁ ^ 2 - 2 * J₁ * S₁ / r₁ ^ 3) -
      (P₂ / r₂ ^ 2 - 2 * J₂ * S₂ / r₂ ^ 3)| ≤
      (pΔ₀ / c ^ 2 + 2 * p₀ / c ^ 3 +
        2 * jΔ₀ * R / c ^ 3 + 2 * j₀ * RΔ / c ^ 3 +
        6 * j₀ * R / c ^ 4) * D := by
  have hρ₁ : c ≤ r₁ / d := (le_div_iff₀ hd).2 (by nlinarith only [hr₁])
  have hρ₂ : c ≤ r₂ / d := (le_div_iff₀ hd).2 (by nlinarith only [hr₂])
  have hρdiff : |r₁ / d - r₂ / d| ≤ D := by
    rw [← sub_div, abs_div, abs_of_pos hd]
    exact (div_le_iff₀ hd).2 (by simpa only [mul_comm] using hrdiff)
  have hJ₂' : |J₂ / d ^ 3| ≤ j₀ := by
    rw [abs_div, abs_of_pos (pow_pos hd 3)]
    exact (div_le_iff₀ (pow_pos hd 3)).2 (by nlinarith only [hJ₂])
  have hJdiff' : |J₁ / d ^ 3 - J₂ / d ^ 3| ≤ jΔ₀ * D := by
    rw [← sub_div, abs_div, abs_of_pos (pow_pos hd 3)]
    exact (div_le_iff₀ (pow_pos hd 3)).2 (by nlinarith only [hJdiff])
  have hP₂' : |P₂ / d ^ 2| ≤ p₀ := by
    rw [abs_div, abs_of_pos (pow_pos hd 2)]
    exact (div_le_iff₀ (pow_pos hd 2)).2 (by nlinarith only [hP₂])
  have hPdiff' : |P₁ / d ^ 2 - P₂ / d ^ 2| ≤ pΔ₀ * D := by
    rw [← sub_div, abs_div, abs_of_pos (pow_pos hd 2)]
    exact (div_le_iff₀ (pow_pos hd 2)).2 (by nlinarith only [hPdiff])
  have h := abs_squaredQuotientJet_sub_le hc hj₀ hp₀ hjΔ₀ hpΔ₀ hR hRΔ hD
    hρ₁ hρ₂ hρdiff hJ₂' hJdiff' hP₂' hPdiff' hS₁ hS₂ hSdiff
  have hnorm : ∀ r J P S : ℝ, r ≠ 0 →
      (P / d ^ 2) / (r / d) ^ 2 -
        2 * (J / d ^ 3) * S / (r / d) ^ 3 =
        P / r ^ 2 - 2 * J * S / r ^ 3 := by
    intro r J P S hr
    field_simp [hd.ne', hr]
  rwa [hnorm r₁ J₁ P₁ S₁ (ne_of_gt ((mul_pos hc hd).trans_le hr₁)),
    hnorm r₂ J₂ P₂ S₂ (ne_of_gt ((mul_pos hc hd).trans_le hr₂))] at h

end intervalIntegral

end
