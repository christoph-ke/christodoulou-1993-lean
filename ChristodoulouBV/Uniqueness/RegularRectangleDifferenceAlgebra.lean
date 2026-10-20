module

public import ChristodoulouBV.Uniqueness.RegularRectangleComparison
public import ChristodoulouBV.Uniqueness.RegularRectangleCoefficients

/-!
# Algebraic difference bounds for regular coefficients

These estimates use positive lower denominators supplied by the compact
rectangle, and require no representative continuity.
-/

public section

open Set MeasureTheory

namespace ChristodoulouBV.Uniqueness

/-- Difference of quotients with positive denominators and a bounded second
numerator. -/
theorem regular_quotient_difference_le
    {a₁ a₂ b₁ b₂ d A : ℝ}
    (hd : 0 < d) (hb₁ : d ≤ b₁) (hb₂ : d ≤ b₂)
    (hA : 0 ≤ A) (ha₂ : |a₂| ≤ A) :
    |a₁ / b₁ - a₂ / b₂| ≤
      |a₁ - a₂| / d + A * |b₁ - b₂| / d ^ 2 := by
  have hb₁pos : 0 < b₁ := hd.trans_le hb₁
  have hb₂pos : 0 < b₂ := hd.trans_le hb₂
  have hden : 0 < b₁ * b₂ := mul_pos hb₁pos hb₂pos
  have hdd : 0 < d ^ 2 := sq_pos_of_pos hd
  have hdenLow : d ^ 2 ≤ b₁ * b₂ := by
    rw [pow_two]
    exact mul_le_mul hb₁ hb₂ hd.le hb₁pos.le
  have heq : a₁ / b₁ - a₂ / b₂ =
      (a₁ - a₂) / b₁ + a₂ * (b₂ - b₁) / (b₁ * b₂) := by
    field_simp [ne_of_gt hb₁pos, ne_of_gt hb₂pos]
    ring
  rw [heq]
  have htri := abs_add_le ((a₁ - a₂) / b₁)
    (a₂ * (b₂ - b₁) / (b₁ * b₂))
  have hfirst : |(a₁ - a₂) / b₁| ≤ |a₁ - a₂| / d := by
    rw [abs_div, abs_of_pos hb₁pos]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hd hb₁
  have hsecond : |a₂ * (b₂ - b₁) / (b₁ * b₂)| ≤
      A * |b₁ - b₂| / d ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos hden, abs_sub_comm]
    apply (div_le_div_iff₀ hden hdd).2
    have hnum : |a₂| * |b₁ - b₂| ≤ A * |b₁ - b₂| :=
      mul_le_mul_of_nonneg_right ha₂ (abs_nonneg _)
    calc
      (|a₂| * |b₁ - b₂|) * d ^ 2 ≤
          (A * |b₁ - b₂|) * d ^ 2 :=
        mul_le_mul_of_nonneg_right hnum hdd.le
      _ ≤ (A * |b₁ - b₂|) * (b₁ * b₂) :=
        mul_le_mul_of_nonneg_left hdenLow
          (mul_nonneg hA (abs_nonneg _))
  exact htri.trans (add_le_add hfirst hsecond)

/-- The mass ratio is Lipschitz in mass and radius on a positive-radius
rectangle; the second ratio is at most one. -/
theorem regular_mass_ratio_difference_le
    {m₁ m₂ r₁ r₂ ρ : ℝ}
    (hρ : 0 < ρ) (hr₁ : ρ ≤ r₁) (hr₂ : ρ ≤ r₂)
    (hμ₂0 : 0 ≤ 2 * m₂ / r₂) (hμ₂1 : 2 * m₂ / r₂ ≤ 1) :
    |2 * m₁ / r₁ - 2 * m₂ / r₂| ≤
      (2 * |m₁ - m₂| + |r₁ - r₂|) / ρ := by
  have hr₁pos : 0 < r₁ := hρ.trans_le hr₁
  have hr₂pos : 0 < r₂ := hρ.trans_le hr₂
  have heq : 2 * m₁ / r₁ - 2 * m₂ / r₂ =
      (2 * (m₁ - m₂) +
        (2 * m₂ / r₂) * (r₂ - r₁)) / r₁ := by
    field_simp [ne_of_gt hr₁pos, ne_of_gt hr₂pos]
    ring
  rw [heq, abs_div, abs_of_pos hr₁pos]
  have hratio : |2 * m₂ / r₂| ≤ 1 := by
    rwa [abs_of_nonneg hμ₂0]
  have hmul : |(2 * m₂ / r₂) * (r₂ - r₁)| ≤ |r₁ - r₂| := by
    rw [abs_mul]
    calc
      |2 * m₂ / r₂| * |r₂ - r₁| ≤ 1 * |r₂ - r₁| :=
        mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
      _ = |r₁ - r₂| := by rw [one_mul, abs_sub_comm]
  have hfirst : |2 * (m₁ - m₂)| = 2 * |m₁ - m₂| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hnum : |2 * (m₁ - m₂) +
      (2 * m₂ / r₂) * (r₂ - r₁)| ≤
      2 * |m₁ - m₂| + |r₁ - r₂| := by
    calc
      |2 * (m₁ - m₂) + (2 * m₂ / r₂) * (r₂ - r₁)| ≤
          |2 * (m₁ - m₂)| +
            |(2 * m₂ / r₂) * (r₂ - r₁)| := abs_add_le _ _
      _ ≤ 2 * |m₁ - m₂| + |r₁ - r₂| := by
          rw [hfirst]
          linarith
  have hnum0 : 0 ≤ 2 * |m₁ - m₂| + |r₁ - r₂| := by positivity
  calc
    |2 * (m₁ - m₂) + (2 * m₂ / r₂) * (r₂ - r₁)| / r₁ ≤
        (2 * |m₁ - m₂| + |r₁ - r₂|) / r₁ :=
      div_le_div_of_nonneg_right hnum hr₁pos.le
    _ ≤ (2 * |m₁ - m₂| + |r₁ - r₂|) / ρ :=
      div_le_div_of_nonneg_left hnum0 hρ hr₁

/-- A product inherits a difference bound from bounded factors and their
individual difference bounds. -/
theorem regular_product_lipschitz
    {a₁ a₂ b₁ b₂ A B K L F : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hK : 0 ≤ K) (_hL : 0 ≤ L)
    (_hF : 0 ≤ F) (ha : |a₁| ≤ A) (hb : |b₂| ≤ B)
    (hda : |a₁ - a₂| ≤ K * F)
    (hdb : |b₁ - b₂| ≤ L * F) :
    |a₁ * b₁ - a₂ * b₂| ≤ (A * L + B * K) * F := by
  have h := regular_product_difference_le a₁ a₂ b₁ b₂
  have hleft : |a₁| * |b₁ - b₂| ≤ A * (L * F) := by
    exact (mul_le_mul_of_nonneg_right ha (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hdb hA)
  have hright : |b₂| * |a₁ - a₂| ≤ B * (K * F) := by
    exact (mul_le_mul_of_nonneg_right hb (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hda hB)
  calc
    |a₁ * b₁ - a₂ * b₂| ≤
        |a₁| * |b₁ - b₂| + |b₂| * |a₁ - a₂| := h
    _ ≤ A * (L * F) + B * (K * F) := add_le_add hleft hright
    _ = (A * L + B * K) * F := by ring

/-- A quotient with denominators bounded below inherits a difference
bound from numerator and denominator differences. -/
theorem regular_quotient_lipschitz
    {a₁ a₂ b₁ b₂ d A K L F : ℝ}
    (hd : 0 < d) (hb₁ : d ≤ b₁) (hb₂ : d ≤ b₂)
    (hA : 0 ≤ A) (_hK : 0 ≤ K) (_hL : 0 ≤ L)
    (_hF : 0 ≤ F) (ha₂ : |a₂| ≤ A)
    (hda : |a₁ - a₂| ≤ K * F)
    (hdb : |b₁ - b₂| ≤ L * F) :
    |a₁ / b₁ - a₂ / b₂| ≤ (K / d + A * L / d ^ 2) * F := by
  have h := regular_quotient_difference_le (a₁ := a₁) hd hb₁ hb₂ hA ha₂
  have hfirst : |a₁ - a₂| / d ≤ (K * F) / d :=
    div_le_div_of_nonneg_right hda hd.le
  have hsecond : A * |b₁ - b₂| / d ^ 2 ≤
      A * (L * F) / d ^ 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdb hA)
      (sq_nonneg d)
  calc
    |a₁ / b₁ - a₂ / b₂| ≤
        |a₁ - a₂| / d + A * |b₁ - b₂| / d ^ 2 := h
    _ ≤ (K * F) / d + A * (L * F) / d ^ 2 :=
      add_le_add hfirst hsecond
    _ = (K / d + A * L / d ^ 2) * F := by ring

/-- Squaring preserves a difference estimate on a bounded interval. -/
theorem regular_square_lipschitz
    {x₁ x₂ T K F : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hF : 0 ≤ F)
    (hx₁ : |x₁| ≤ T) (hx₂ : |x₂| ≤ T)
    (hdx : |x₁ - x₂| ≤ K * F) :
    |x₁ ^ 2 - x₂ ^ 2| ≤ 2 * T * K * F := by
  have h := regular_product_lipschitz hT hT hK hK hF hx₁ hx₂ hdx hdx
  convert h using 1 <;> ring_nf

/-- A positive-denominator quotient has the expected uniform absolute
bound. -/
theorem regular_quotient_abs_le
    {a b d A : ℝ} (hd : 0 < d) (hb : d ≤ b)
    (hA : 0 ≤ A) (ha : |a| ≤ A) :
    |a / b| ≤ A / d := by
  have hbpos := hd.trans_le hb
  rw [abs_div, abs_of_pos hbpos]
  calc
    |a| / b ≤ A / b := div_le_div_of_nonneg_right ha hbpos.le
    _ ≤ A / d := div_le_div_of_nonneg_left hA hd hb

/-- The scalar transport amplitude `a - b c` is bounded when each
primitive field is bounded. -/
theorem regular_amplitude_abs_le
    {a b c C : ℝ} (hC : 0 ≤ C)
    (ha : |a| ≤ C) (hb : |b| ≤ C) (hc : |c| ≤ C) :
    |a - b * c| ≤ C + C ^ 2 := by
  have hbc : |b * c| ≤ C ^ 2 := by
    rw [abs_mul, pow_two]
    exact (mul_le_mul_of_nonneg_right hb (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hc hC)
  calc
    |a - b * c| ≤ |a| + |b * c| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-(b * c))
    _ ≤ C + C ^ 2 := add_le_add ha hbc

/-- Differences of scalar transport amplitudes are linear in differences
of their three primitive fields. -/
theorem regular_amplitude_lipschitz
    {a₁ a₂ b₁ b₂ c₁ c₂ C F : ℝ}
    (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hb₁ : |b₁| ≤ C) (hc₂ : |c₂| ≤ C)
    (hda : |a₁ - a₂| ≤ F)
    (hdb : |b₁ - b₂| ≤ F)
    (hdc : |c₁ - c₂| ≤ F) :
    |(a₁ - b₁ * c₁) - (a₂ - b₂ * c₂)| ≤ (1 + 2 * C) * F := by
  have hprod : |b₁ * c₁ - b₂ * c₂| ≤ (C + C) * F := by
    simpa only [mul_one] using
      regular_product_lipschitz hC hC (by norm_num : (0 : ℝ) ≤ 1)
        (by norm_num : (0 : ℝ) ≤ 1) hF hb₁ hc₂
        (by simpa only [one_mul] using hdb)
        (by simpa only [one_mul] using hdc)
  calc
    |(a₁ - b₁ * c₁) - (a₂ - b₂ * c₂)| =
        |(a₁ - a₂) - (b₁ * c₁ - b₂ * c₂)| := by congr 1; ring
    _ ≤ |a₁ - a₂| + |b₁ * c₁ - b₂ * c₂| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (a₁ - a₂) (-(b₁ * c₁ - b₂ * c₂))
    _ ≤ F + (C + C) * F := add_le_add hda hprod
    _ = (1 + 2 * C) * F := by ring

/-- The nonlinear mass density is locally Lipschitz on a region with a
positive expansion and bounded scalar amplitude. -/
theorem regular_mass_density_lipschitz
    {g₁ g₂ x₁ x₂ q₁ q₂ c T Kg Kx Kq F : ℝ}
    (hc : 0 < c) (hT : 0 ≤ T) (hKg : 0 ≤ Kg)
    (hKx : 0 ≤ Kx) (hKq : 0 ≤ Kq) (hF : 0 ≤ F)
    (hg₁ : 0 ≤ g₁) (hg₁' : g₁ ≤ 1)
    (hg₂ : 0 ≤ g₂) (hg₂' : g₂ ≤ 1)
    (hq₁ : c ≤ q₁) (hq₂ : c ≤ q₂)
    (hx₁ : |x₁| ≤ T) (hx₂ : |x₂| ≤ T)
    (hdg : |g₁ - g₂| ≤ Kg * F)
    (hdx : |x₁ - x₂| ≤ Kx * F)
    (hdq : |q₁ - q₂| ≤ Kq * F) :
    |g₁ * x₁ ^ 2 / (2 * q₁) - g₂ * x₂ ^ 2 / (2 * q₂)| ≤
      (((2 * T * Kx + T ^ 2 * Kg) / (2 * c)) +
        T ^ 2 * (2 * Kq) / (2 * c) ^ 2) * F := by
  have hTsq : 0 ≤ T ^ 2 := sq_nonneg T
  have hx1sq : |x₁ ^ 2| ≤ T ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hx₁ _
  have hx2sq : |x₂ ^ 2| ≤ T ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hx₂ _
  have hsquare : |x₁ ^ 2 - x₂ ^ 2| ≤ (2 * T * Kx) * F := by
    simpa only [mul_assoc] using
      regular_square_lipschitz hT hKx hF hx₁ hx₂ hdx
  have hnum : |g₁ * x₁ ^ 2 - g₂ * x₂ ^ 2| ≤
      (2 * T * Kx + T ^ 2 * Kg) * F := by
    have h := regular_product_lipschitz
      (show 0 ≤ (1 : ℝ) by norm_num) hTsq hKg
      (by positivity : 0 ≤ 2 * T * Kx) hF
      (by rwa [abs_of_nonneg hg₁] : |g₁| ≤ 1)
      hx2sq hdg hsquare
    convert h using 1
    ring
  have hnum₂ : |g₂ * x₂ ^ 2| ≤ T ^ 2 := by
    rw [abs_mul, abs_of_nonneg hg₂]
    calc
      g₂ * |x₂ ^ 2| ≤ 1 * |x₂ ^ 2| :=
        mul_le_mul_of_nonneg_right hg₂' (abs_nonneg _)
      _ = |x₂ ^ 2| := by ring
      _ ≤ T ^ 2 := hx2sq
  have hqdiff : |2 * q₁ - 2 * q₂| ≤ (2 * Kq) * F := by
    have heq : 2 * q₁ - 2 * q₂ = 2 * (q₁ - q₂) := by ring
    rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hdq]
  have hden₁ : 2 * c ≤ 2 * q₁ := by linarith
  have hden₂ : 2 * c ≤ 2 * q₂ := by linarith
  have hbound := regular_quotient_lipschitz
    (show 0 < 2 * c by positivity) hden₁ hden₂ hTsq
    (by positivity : 0 ≤ 2 * T * Kx + T ^ 2 * Kg)
    (by positivity : 0 ≤ 2 * Kq) hF hnum₂ hnum hqdiff
  exact hbound

/-- The mixed radius coefficient is locally Lipschitz on a positive-radius,
positive-gap rectangle. -/
theorem regular_radius_coefficient_lipschitz
    {μ₁ μ₂ g₁ g₂ r₁ r₂ lam₁ lam₂ nu₁ nu₂ ρ δ C Kμ F : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hKμ : 0 ≤ Kμ) (hF : 0 ≤ F)
    (hμ₁ : 0 ≤ μ₁) (hμ₁' : μ₁ ≤ 1)
    (hμ₂ : 0 ≤ μ₂) (hμ₂' : μ₂ ≤ 1)
    (hg₁ : δ ≤ g₁) (hg₂ : δ ≤ g₂)
    (hr₁ : ρ ≤ r₁) (hr₂ : ρ ≤ r₂)
    (_hlam₁ : |lam₁| ≤ C) (hlam₂ : |lam₂| ≤ C)
    (hnu₁ : |nu₁| ≤ C) (_hnu₂ : |nu₂| ≤ C)
    (hdμ : |μ₁ - μ₂| ≤ Kμ * F)
    (hdg : |g₁ - g₂| ≤ Kμ * F)
    (hdr : |r₁ - r₂| ≤ F)
    (hdlam : |lam₁ - lam₂| ≤ F)
    (hdnu : |nu₁ - nu₂| ≤ F) :
    |μ₁ * lam₁ * nu₁ / (g₁ * r₁) -
      μ₂ * lam₂ * nu₂ / (g₂ * r₂)| ≤
      (C * ((1 / δ) * (1 / ρ + C / ρ ^ 2) +
        (C / ρ) * (Kμ / δ + Kμ / δ ^ 2)) +
        (1 / δ) * (C / ρ)) * F := by
  let K₁ := Kμ / δ + Kμ / δ ^ 2
  let K₂ := 1 / ρ + C / ρ ^ 2
  let K₃ := (1 / δ) * K₂ + (C / ρ) * K₁
  let A := (1 / δ) * (C / ρ)
  have hK₁ : 0 ≤ K₁ := by dsimp [K₁]; positivity
  have hK₂ : 0 ≤ K₂ := by dsimp [K₂]; positivity
  have hK₃ : 0 ≤ K₃ := by dsimp [K₃]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hμ₁abs : |μ₁| ≤ 1 := by rwa [abs_of_nonneg hμ₁]
  have hμ₂abs : |μ₂| ≤ 1 := by rwa [abs_of_nonneg hμ₂]
  have hratioμ₁ : |μ₁ / g₁| ≤ 1 / δ :=
    regular_quotient_abs_le hδ hg₁ (by norm_num) hμ₁abs
  have hratioμ₂ : |μ₂ / g₂| ≤ 1 / δ :=
    regular_quotient_abs_le hδ hg₂ (by norm_num) hμ₂abs
  have hratiolam₂ : |lam₂ / r₂| ≤ C / ρ :=
    regular_quotient_abs_le hρ hr₂ hC hlam₂
  have hdμratio : |μ₁ / g₁ - μ₂ / g₂| ≤ K₁ * F := by
    simpa only [K₁, one_mul] using regular_quotient_lipschitz hδ hg₁ hg₂
      (by norm_num : (0 : ℝ) ≤ 1) hKμ hKμ hF hμ₂abs hdμ hdg
  have hdlamratio : |lam₁ / r₁ - lam₂ / r₂| ≤ K₂ * F := by
    simpa only [K₂, one_mul, mul_one] using regular_quotient_lipschitz
      hρ hr₁ hr₂ hC (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) ≤ 1) hF hlam₂
      (by simpa only [one_mul] using hdlam)
      (by simpa only [one_mul] using hdr)
  have hratioProd₂ : |(μ₂ / g₂) * (lam₂ / r₂)| ≤ A := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hratioμ₂ (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hratiolam₂ (by positivity))
  have hdprod : |(μ₁ / g₁) * (lam₁ / r₁) -
      (μ₂ / g₂) * (lam₂ / r₂)| ≤ K₃ * F := by
    simpa only [K₃] using regular_product_lipschitz
      (by positivity : 0 ≤ 1 / δ) (by positivity : 0 ≤ C / ρ)
      hK₁ hK₂ hF hratioμ₁ hratiolam₂ hdμratio hdlamratio
  have hfinal : |nu₁ * ((μ₁ / g₁) * (lam₁ / r₁)) -
      nu₂ * ((μ₂ / g₂) * (lam₂ / r₂))| ≤
      (C * K₃ + A) * F := by
    simpa only [one_mul, mul_one] using regular_product_lipschitz
      hC hA (by norm_num : (0 : ℝ) ≤ 1) hK₃ hF
      hnu₁ hratioProd₂ (by simpa only [one_mul] using hdnu) hdprod
  have hform₁ : μ₁ * lam₁ * nu₁ / (g₁ * r₁) =
      nu₁ * ((μ₁ / g₁) * (lam₁ / r₁)) := by
    have hg : g₁ ≠ 0 := (hδ.trans_le hg₁).ne'
    have hr : r₁ ≠ 0 := (hρ.trans_le hr₁).ne'
    field_simp
  have hform₂ : μ₂ * lam₂ * nu₂ / (g₂ * r₂) =
      nu₂ * ((μ₂ / g₂) * (lam₂ / r₂)) := by
    have hg : g₂ ≠ 0 := (hδ.trans_le hg₂).ne'
    have hr : r₂ ≠ 0 := (hρ.trans_le hr₂).ne'
    field_simp
  rw [hform₁, hform₂]
  exact hfinal

/-- Recovering the scalar from its radius multiple is Lipschitz when the
radius is bounded below. -/
theorem regular_scalar_of_radius_scalar_difference_le
    {r₁ r₂ φ₁ φ₂ ρ C : ℝ}
    (hρ : 0 < ρ) (hr₁ : ρ ≤ r₁)
    (hC : 0 ≤ C) (hφ₂ : |φ₂| ≤ C) :
    |φ₁ - φ₂| ≤
      (|r₁ * φ₁ - r₂ * φ₂| + C * |r₁ - r₂|) / ρ := by
  have hr₁pos : 0 < r₁ := hρ.trans_le hr₁
  have heq : r₁ * (φ₁ - φ₂) =
      (r₁ * φ₁ - r₂ * φ₂) - (r₁ - r₂) * φ₂ := by ring
  have hnum : |r₁ * (φ₁ - φ₂)| ≤
      |r₁ * φ₁ - r₂ * φ₂| + C * |r₁ - r₂| := by
    rw [heq]
    have htri : |(r₁ * φ₁ - r₂ * φ₂) - (r₁ - r₂) * φ₂| ≤
        |r₁ * φ₁ - r₂ * φ₂| + |(r₁ - r₂) * φ₂| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (r₁ * φ₁ - r₂ * φ₂) (-((r₁ - r₂) * φ₂))
    have hprod : |(r₁ - r₂) * φ₂| ≤ C * |r₁ - r₂| := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right hφ₂ (abs_nonneg _)
    linarith
  have hdiv : |φ₁ - φ₂| = |r₁ * (φ₁ - φ₂)| / r₁ := by
    rw [abs_mul, abs_of_pos hr₁pos]
    field_simp
  rw [hdiv]
  calc
    |r₁ * (φ₁ - φ₂)| / r₁ ≤
        (|r₁ * φ₁ - r₂ * φ₂| + C * |r₁ - r₂|) / r₁ :=
      div_le_div_of_nonneg_right hnum hr₁pos.le
    _ ≤ (|r₁ * φ₁ - r₂ * φ₂| + C * |r₁ - r₂|) / ρ :=
      div_le_div_of_nonneg_left (by positivity) hρ hr₁

end ChristodoulouBV.Uniqueness

end
