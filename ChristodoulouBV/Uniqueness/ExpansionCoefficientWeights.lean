module

public import ChristodoulouBV.Uniqueness.ExpansionCoefficientPointwise

/-!
# Weighted terms in expansion coefficient differences

These real-variable inequalities isolate the axis-distance weight carried by
the mass forcing in both characteristic directions.
-/

public section

namespace ChristodoulouBV.Uniqueness

/-- A fixed coefficient bound converts the mass contribution in the
coefficient difference into the squared axis-distance weight. -/
theorem mass_coefficient_term_le_weighted
    {dm d r g₁ g₂ x C : ℝ}
    (hd : 0 < d) (hr : 0 < r) (hg₁ : 0 < g₁) (hg₂ : 0 < g₂)
    (hC : 0 ≤ C) (hdr : d / r ≤ C) (hx : |x| ≤ C)
    (hg₁inv : 1 / g₁ ≤ C) (hg₂inv : 1 / g₂ ≤ C) :
    (2 * |dm| / r) / (g₁ * g₂) * |x / r| ≤
      2 * C ^ 5 * (|dm| / d ^ 2) := by
  have hnonneg : 0 ≤ |dm| / d ^ 2 :=
    div_nonneg (abs_nonneg _) (sq_nonneg _)
  have hratio : 0 ≤ d / r := div_nonneg hd.le hr.le
  have h₁ : 0 ≤ 1 / g₁ := by positivity
  have h₂ : 0 ≤ 1 / g₂ := by positivity
  have heq : (2 * |dm| / r) / (g₁ * g₂) * |x / r| =
      2 * (|dm| / d ^ 2) * (d / r) * (d / r) *
        |x| * (1 / g₁) * (1 / g₂) := by
    rw [abs_div, abs_of_pos hr]
    field_simp [hd.ne', hr.ne', hg₁.ne', hg₂.ne']
  rw [heq]
  calc
    2 * (|dm| / d ^ 2) * (d / r) * (d / r) *
        |x| * (1 / g₁) * (1 / g₂) ≤
      2 * (|dm| / d ^ 2) * C * C * C * C * C := by
        gcongr
    _ = 2 * C ^ 5 * (|dm| / d ^ 2) := by ring

/-- The radius part of the mass-ratio difference is a fixed multiple of the
second coefficient, once the two radii and expansions are comparable. -/
theorem radius_coefficient_term_le_weighted
    {μ dr r₁ r₂ g₁ g₂ x₁ x₂ C E : ℝ}
    (hμ : 0 ≤ μ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hg₁ : 0 < g₁) (hg₂ : 0 < g₂) (hx₂ : x₂ ≠ 0)
    (hC : 0 ≤ C)
    (hxratio : |x₁ / x₂| ≤ C) (hrratio : r₂ / r₁ ≤ C)
    (hginv : 1 / g₁ ≤ C) (hdrratio : |dr| / r₁ ≤ C * E) :
    (μ * |dr| / r₁) / (g₁ * g₂) * |x₁ / r₁| ≤
      C ^ 4 * E * (μ * |x₂| / (g₂ * r₂)) := by
  have hq : 0 ≤ μ * |x₂| / (g₂ * r₂) :=
    div_nonneg (mul_nonneg hμ (abs_nonneg _)) (mul_pos hg₂ hr₂).le
  have hratio : 0 ≤ r₂ / r₁ := div_nonneg hr₂.le hr₁.le
  have hginvnonneg : 0 ≤ 1 / g₁ := by positivity
  have hdrnonneg : 0 ≤ |dr| / r₁ := div_nonneg (abs_nonneg _) hr₁.le
  have heq : (μ * |dr| / r₁) / (g₁ * g₂) * |x₁ / r₁| =
      (μ * |x₂| / (g₂ * r₂)) * |x₁ / x₂| *
        (r₂ / r₁) * (1 / g₁) * (|dr| / r₁) := by
    rw [abs_div, abs_div, abs_of_pos hr₁]
    field_simp [hr₁.ne', hr₂.ne', hg₁.ne', hg₂.ne', hx₂]
  rw [heq]
  calc
    (μ * |x₂| / (g₂ * r₂)) * |x₁ / x₂| *
        (r₂ / r₁) * (1 / g₁) * (|dr| / r₁) ≤
      (μ * |x₂| / (g₂ * r₂)) * C * C * C * (C * E) := by
        gcongr
    _ = C ^ 4 * E * (μ * |x₂| / (g₂ * r₂)) := by ring

/-- The expansion and direct radius terms are controlled by the second
coefficient times the comparison expansion norm. -/
theorem expansion_coefficient_terms_le_weighted
    {μ dx dr r₁ r₂ g₂ x₁ x₂ C E : ℝ}
    (hμ : 0 ≤ μ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hg₂ : 0 < g₂) (hx₂ : x₂ ≠ 0)
    (hC : 0 ≤ C) (hdx : |dx| ≤ E)
    (hxinv : 1 / |x₂| ≤ C) (hxratio : |x₁ / x₂| ≤ C)
    (hdrratio : |dr| / r₁ ≤ C * E) :
    (μ / (g₂ * r₂)) * (|dx| + |x₁ * dr / r₁|) ≤
      (C + C ^ 2) * E * (μ * |x₂| / (g₂ * r₂)) := by
  have hx₂abs : 0 < |x₂| := abs_pos.mpr hx₂
  have hq : 0 ≤ μ * |x₂| / (g₂ * r₂) :=
    div_nonneg (mul_nonneg hμ (abs_nonneg _)) (mul_pos hg₂ hr₂).le
  have hxinvnonneg : 0 ≤ 1 / |x₂| := by positivity
  have hratio : 0 ≤ |x₁ / x₂| := abs_nonneg _
  have hdrnonneg : 0 ≤ |dr| / r₁ := div_nonneg (abs_nonneg _) hr₁.le
  have hE : 0 ≤ E := (abs_nonneg _).trans hdx
  have heq : (μ / (g₂ * r₂)) * (|dx| + |x₁ * dr / r₁|) =
      (μ * |x₂| / (g₂ * r₂)) *
        (|dx| * (1 / |x₂|) + |x₁ / x₂| * (|dr| / r₁)) := by
    rw [abs_div, abs_mul, abs_div, abs_of_pos hr₁]
    field_simp [hr₁.ne', hr₂.ne', hg₂.ne', hx₂abs.ne', hx₂]
  rw [heq]
  calc
    (μ * |x₂| / (g₂ * r₂)) *
        (|dx| * (1 / |x₂|) + |x₁ / x₂| * (|dr| / r₁)) ≤
      (μ * |x₂| / (g₂ * r₂)) * (E * C + C * (C * E)) := by
        gcongr
    _ = (C + C ^ 2) * E * (μ * |x₂| / (g₂ * r₂)) := by ring

private theorem coefficient_difference_weighted
    {K μ dx dr dm d r₁ r₂ g₁ g₂ x₁ x₂ C E : ℝ}
    (hd : 0 < d) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hg₁ : 0 < g₁) (hg₂ : 0 < g₂) (hμ : 0 ≤ μ)
    (hx₂ : x₂ ≠ 0) (hC : 0 ≤ C)
    (hdx : |dx| ≤ E) (hdrratio : |dr| / r₁ ≤ C * E)
    (hxinv : 1 / |x₂| ≤ C) (hxratio : |x₁ / x₂| ≤ C)
    (hrratio : r₂ / r₁ ≤ C) (hdratio : d / r₁ ≤ C)
    (hx₁ : |x₁| ≤ C) (hg₁inv : 1 / g₁ ≤ C)
    (hg₂inv : 1 / g₂ ≤ C)
    (hK : |K| ≤
      (μ / (g₂ * r₂)) * (|dx| + |x₁ * dr / r₁|) +
      (2 * |dm| / r₁ + μ * |dr| / r₁) /
        (g₁ * g₂) * |x₁ / r₁|) :
    |K| ≤ (C + C ^ 2 + C ^ 4) * E *
        (μ * |x₂| / (g₂ * r₂)) +
      2 * C ^ 5 * (|dm| / d ^ 2) := by
  have hA := expansion_coefficient_terms_le_weighted hμ hr₁ hr₂
    hg₂ hx₂ hC hdx hxinv hxratio hdrratio
  have hM := mass_coefficient_term_le_weighted (dm := dm) hd hr₁ hg₁ hg₂ hC
    hdratio hx₁ hg₁inv hg₂inv
  have hR := radius_coefficient_term_le_weighted hμ hr₁ hr₂
    hg₁ hg₂ hx₂ hC hxratio hrratio hg₁inv hdrratio
  have hsplit :
      (2 * |dm| / r₁ + μ * |dr| / r₁) /
          (g₁ * g₂) * |x₁ / r₁| =
      (2 * |dm| / r₁) / (g₁ * g₂) * |x₁ / r₁| +
        (μ * |dr| / r₁) / (g₁ * g₂) * |x₁ / r₁| := by ring
  calc
    |K| ≤ (μ / (g₂ * r₂)) * (|dx| + |x₁ * dr / r₁|) +
        (2 * |dm| / r₁ + μ * |dr| / r₁) /
          (g₁ * g₂) * |x₁ / r₁| := hK
    _ = (μ / (g₂ * r₂)) * (|dx| + |x₁ * dr / r₁|) +
        (2 * |dm| / r₁) / (g₁ * g₂) * |x₁ / r₁| +
        (μ * |dr| / r₁) / (g₁ * g₂) * |x₁ / r₁| := by rw [hsplit]; ring
    _ ≤ (C + C ^ 2) * E * (μ * |x₂| / (g₂ * r₂)) +
        2 * C ^ 5 * (|dm| / d ^ 2) +
        C ^ 4 * E * (μ * |x₂| / (g₂ * r₂)) := by
      exact add_le_add (add_le_add hA hM) hR
    _ = (C + C ^ 2 + C ^ 4) * E *
        (μ * |x₂| / (g₂ * r₂)) +
      2 * C ^ 5 * (|dm| / d ^ 2) := by ring

/-- At a good outgoing point, fixed coefficient bounds reduce the outgoing
coefficient difference to `L` times the second positive coefficient and the
weighted mass difference. -/
theorem ComparisonData.nuCoeff_difference_weighted (D : ComparisonData)
    {V u v C : ℝ} (hV : V ≤ D.b)
    (huv : (u, v) ∈ triangle D.a V) (hvG : v ∈ D.goodV)
    (hC : 0 ≤ C)
    (hbounds :
      1 / |D.S₂.lam u v| ≤ C ∧
      |D.S₁.lam u v / D.S₂.lam u v| ≤ C ∧
      D.S₂.r u v / D.S₁.r u v ≤ C ∧
      (v - u) / D.S₁.r u v ≤ C ∧
      |D.S₁.lam u v| ≤ C ∧
      1 / (1 - IsBVSolution.mu D.S₁ u v) ≤ C ∧
      1 / (1 - IsBVSolution.mu D.S₂ u v) ≤ C) :
    |IsBVSolution.nuCoeff D.S₁ u v -
      IsBVSolution.nuCoeff D.S₂ u v| ≤
      (C + C ^ 2 + C ^ 4) * D.L V *
        IsBVSolution.nuCoeff D.S₂ u v +
      2 * C ^ 5 *
        (|D.S₁.m u v - D.S₂.m u v| / (v - u) ^ 2) := by
  have hfull : (u, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨huv.1, huv.2.1, huv.2.2.trans_le hV⟩
  have hp := D.hT hfull
  have hd : 0 < v - u := sub_pos.mpr huv.2.1
  have hr₁ := D.h₁.solution.radius_pos (u, v) hp.1
  have hr₂ := D.h₂.solution.radius_pos (u, v) hp.2
  have hlam₂ := D.h₂.solution.lam_pos (u, v) hp.2
  have hμ := (D.h₂.mass_ratio_bounds hp.2).1
  change 0 ≤ IsBVSolution.mu D.S₂ u v at hμ
  have hg₁ : 0 < 1 - IsBVSolution.mu D.S₁ u v := by
    have hh := (D.h₁.mass_ratio_bounds hp.1).2
    change IsBVSolution.mu D.S₁ u v < 1 at hh
    linarith
  have hg₂ : 0 < 1 - IsBVSolution.mu D.S₂ u v := by
    have hh := (D.h₂.mass_ratio_bounds hp.2).2
    change IsBVSolution.mu D.S₂ u v < 1 at hh
    linarith
  have hdx := D.lam_diff_le_L_good hV huv hvG
  have hL : 0 ≤ D.L V := (abs_nonneg _).trans hdx
  have hrad := D.radius_diff_le_L hV huv
  have hdratio :
      |D.S₁.r u v - D.S₂.r u v| / D.S₁.r u v ≤ C * D.L V := by
    calc
      _ ≤ ((v - u) * D.L V) / D.S₁.r u v :=
        div_le_div_of_nonneg_right hrad hr₁.le
      _ = ((v - u) / D.S₁.r u v) * D.L V := by ring
      _ ≤ C * D.L V := mul_le_mul_of_nonneg_right hbounds.2.2.2.1 hL
  have hx₂ : D.S₂.lam u v ≠ 0 := ne_of_gt hlam₂
  have hraw := D.nuCoeff_difference_abs_le hfull
  have hweighted := coefficient_difference_weighted hd hr₁ hr₂ hg₁ hg₂
    hμ hx₂ hC hdx hdratio hbounds.1 hbounds.2.1
    hbounds.2.2.1 hbounds.2.2.2.1 hbounds.2.2.2.2.1
    hbounds.2.2.2.2.2.1 hbounds.2.2.2.2.2.2 hraw
  have hcoeff := D.h₂.nuCoeff_eq_mass_ratio_coefficient_out hp.2
  change IsBVSolution.nuCoeff D.S₂ u v =
    IsBVSolution.mu D.S₂ u v * D.S₂.lam u v /
      ((1 - IsBVSolution.mu D.S₂ u v) * D.S₂.r u v) at hcoeff
  rw [abs_of_pos hlam₂, ← hcoeff] at hweighted
  exact hweighted

/-- At a good incoming point, the second coefficient is nonpositive, so its
negative is the weight controlled by the unsigned incoming (3.12) bound. -/
theorem ComparisonData.incomingCoeff_difference_weighted (D : ComparisonData)
    {V u v C : ℝ} (hV : V < D.b)
    (huv : (u, v) ∈ triangle D.a V) (hvG : v ∈ D.goodV)
    (hC : 0 ≤ C)
    (hbounds :
      1 / |D.S₂.nu u v| ≤ C ∧
      |D.S₁.nu u v / D.S₂.nu u v| ≤ C ∧
      D.S₂.r u v / D.S₁.r u v ≤ C ∧
      (v - u) / D.S₁.r u v ≤ C ∧
      |D.S₁.nu u v| ≤ C ∧
      1 / (1 - IsBVSolution.mu D.S₁ u v) ≤ C ∧
      1 / (1 - IsBVSolution.mu D.S₂ u v) ≤ C) :
    |IsBVSolution.incomingCoeff D.S₁ u v -
      IsBVSolution.incomingCoeff D.S₂ u v| ≤
      (C + C ^ 2 + C ^ 4) * D.N V *
        (-IsBVSolution.incomingCoeff D.S₂ u v) +
      2 * C ^ 5 *
        (|D.S₁.m u v - D.S₂.m u v| / (v - u) ^ 2) := by
  have hfull : (u, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨huv.1, huv.2.1, huv.2.2.trans hV⟩
  have hp := D.hT hfull
  have hd : 0 < v - u := sub_pos.mpr huv.2.1
  have hr₁ := D.h₁.solution.radius_pos (u, v) hp.1
  have hr₂ := D.h₂.solution.radius_pos (u, v) hp.2
  obtain ⟨c, hc, hlam⟩ := D.h₂.lam_bounded_below
  have hnu₂ : D.S₂.nu u v < 0 :=
    (D.h₂.nu_le_neg_lower hc hlam hp.2).trans_lt (neg_lt_zero.mpr hc)
  have hμ := (D.h₂.mass_ratio_bounds hp.2).1
  change 0 ≤ IsBVSolution.mu D.S₂ u v at hμ
  have hg₁ : 0 < 1 - IsBVSolution.mu D.S₁ u v := by
    have hh := (D.h₁.mass_ratio_bounds hp.1).2
    change IsBVSolution.mu D.S₁ u v < 1 at hh
    linarith
  have hg₂ : 0 < 1 - IsBVSolution.mu D.S₂ u v := by
    have hh := (D.h₂.mass_ratio_bounds hp.2).2
    change IsBVSolution.mu D.S₂ u v < 1 at hh
    linarith
  have hdx := D.nu_diff_le_N_good hV.le huv hvG
  have hN : 0 ≤ D.N V := (abs_nonneg _).trans hdx
  have hrad := D.radius_diff_le_N hV huv
  have hdratio :
      |D.S₁.r u v - D.S₂.r u v| / D.S₁.r u v ≤ C * D.N V := by
    calc
      _ ≤ ((v - u) * D.N V) / D.S₁.r u v :=
        div_le_div_of_nonneg_right hrad hr₁.le
      _ = ((v - u) / D.S₁.r u v) * D.N V := by ring
      _ ≤ C * D.N V := mul_le_mul_of_nonneg_right hbounds.2.2.2.1 hN
  have hx₂ : D.S₂.nu u v ≠ 0 := ne_of_lt hnu₂
  have hraw := D.incomingCoeff_difference_abs_le hfull
  have hweighted := coefficient_difference_weighted hd hr₁ hr₂ hg₁ hg₂
    hμ hx₂ hC hdx hdratio hbounds.1 hbounds.2.1
    hbounds.2.2.1 hbounds.2.2.2.1 hbounds.2.2.2.2.1
    hbounds.2.2.2.2.2.1 hbounds.2.2.2.2.2.2 hraw
  have hcoeff : IsBVSolution.incomingCoeff D.S₂ u v =
      IsBVSolution.mu D.S₂ u v * D.S₂.nu u v /
        ((1 - IsBVSolution.mu D.S₂ u v) * D.S₂.r u v) := by
    unfold IsBVSolution.incomingCoeff IsBVSolution.mu
    rfl
  have hq : IsBVSolution.mu D.S₂ u v * |D.S₂.nu u v| /
      ((1 - IsBVSolution.mu D.S₂ u v) * D.S₂.r u v) =
      -IsBVSolution.incomingCoeff D.S₂ u v := by
    rw [abs_of_neg hnu₂, hcoeff]
    ring
  rw [hq] at hweighted
  exact hweighted

end ChristodoulouBV.Uniqueness

end
