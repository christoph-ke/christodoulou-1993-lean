module

public import ChristodoulouBV.Uniqueness.ExtensionStripPower

/-!
# The first signed strip integral

Equation (5.15) uses the mass-ratio bound on the actual incoming segment
and the weighted `α′` bound on that segment.
-/

public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- Monotonicity of the mass-ratio coefficient below the barrier. -/
theorem mass_ratio_fraction_le {μ q : ℝ}
    (hμ : 0 ≤ μ) (hμq : μ ≤ q) (hq : q < 1) :
    0 ≤ μ / (1 - μ) ∧ μ / (1 - μ) ≤ q / (1 - q) := by
  have hdenμ : 0 < 1 - μ := by linarith
  have hdenq : 0 < 1 - q := by linarith
  constructor
  · exact div_nonneg hμ hdenμ.le
  · apply (div_le_div_iff₀ hdenμ hdenq).2
    nlinarith only [hμq]

/-- Equation (5.15) for one candidate C¹ solution on the enlarged domain.
The coefficient is exactly `2q/(1-q)` for exponent `1/2`. -/
theorem strip_integralI₁_le
    {u₁ top : ℝ} {T : Fields}
    (H : IsC1Solution (extensionWorkingDomain u₁ top) T)
    {u₀ u v q A : ℝ} (hu₀ : 0 < u₀) (hu₀u : u₀ < u) (hq : q < 1)
    (hseg : ∀ s ∈ Icc u₀ u, (s, v) ∈ extensionWorkingDomain u₁ top)
    (hμ : ∀ s ∈ Ioc u₀ u, 2 * T.m s v / T.r s v ≤ q)
    (hA : ∀ s ∈ Ioc u₀ u,
      (T.r s v) ^ ((1 : ℝ) / 2) *
        |deriv (fun t => T.alpha s t / T.lam s t) v / T.lam s v| ≤ A) :
    |stripIntegralI₁ u₁ top T u₀ u v hseg| ≤
      (2 * q / (1 - q)) * A * (T.r u v)^(-((1 : ℝ) / 2)) := by
  let C : ℝ := q / (1 - q)
  let δ : ℝ := (1 : ℝ) / 2
  let P : ℝ → ℝ := fun s =>
    deriv (fun t => T.alpha s t / T.lam s t) v / T.lam s v
  let μ : ℝ → ℝ := fun s => 2 * T.m s v / T.r s v
  let F : ℝ → ℝ := fun s =>
    (T.nu s v / T.r s v) * (μ s / (1 - μ s)) * P s
  let G : ℝ → ℝ := fun s =>
    (-T.nu s v) / T.r s v * (T.r s v)^(-δ)
  have hδ : 0 < δ := by dsimp [δ]; norm_num
  have hC : 0 ≤ C := by
    have hs := hseg u (right_mem_Icc.mpr hu₀u.le)
    have hμu := mass_ratio_nonneg_of_c1_domain H hs
    have hq₀ : 0 ≤ q := hμu.trans (hμ u (right_mem_Ioc.mpr hu₀u))
    exact div_nonneg hq₀ (by linarith : 0 ≤ 1 - q)
  have hAnon : 0 ≤ A := by
    have hs := hseg u (right_mem_Icc.mpr hu₀u.le)
    have hr := H.solution.radius_pos (u, v) hs
    exact (mul_nonneg (Real.rpow_nonneg hr.le _) (abs_nonneg _)).trans
      (hA u (right_mem_Ioc.mpr hu₀u))
  obtain ⟨hGI, hGbound⟩ :=
    incoming_radius_power_integral_le_workingDomain H hu₀ hu₀u.le hδ hseg
  have hpoint : ∀ s ∈ Ioc u₀ u, |F s| ≤ C * A * G s := by
    intro s hs
    have hsp := hseg s ⟨hs.1.le, hs.2⟩
    have hr := H.solution.radius_pos (s, v) hsp
    have hnu := nu_neg_of_c1_domain H hsp
    have hμ0 := mass_ratio_nonneg_of_c1_domain H hsp
    have ⟨hcoef0, hcoef⟩ :=
      mass_ratio_fraction_le hμ0 (hμ s hs) hq
    have hnuFactor : 0 ≤ (-T.nu s v) / T.r s v :=
      div_nonneg (le_of_lt (neg_pos.mpr hnu)) hr.le
    have hrpow : 0 < (T.r s v)^δ := Real.rpow_pos_of_pos hr _
    have hP : |P s| ≤ A / (T.r s v)^δ :=
      (le_div_iff₀ hrpow).2 (by simpa only [P, δ, mul_comm] using hA s hs)
    have hnuAbs : |T.nu s v / T.r s v| =
        (-T.nu s v) / T.r s v := by
      rw [abs_div, abs_of_neg hnu, abs_of_pos hr]
    have hFabs : |F s| =
        ((-T.nu s v) / T.r s v) * (μ s / (1 - μ s)) * |P s| := by
      dsimp [F]
      rw [abs_mul, abs_mul, hnuAbs, abs_of_nonneg hcoef0]
    rw [hFabs]
    calc
      ((-T.nu s v) / T.r s v) * (μ s / (1 - μ s)) * |P s|
          ≤ ((-T.nu s v) / T.r s v) * C * |P s| := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hcoef hnuFactor) (abs_nonneg _)
      _ ≤ ((-T.nu s v) / T.r s v) * C * (A / (T.r s v)^δ) := by
            exact mul_le_mul_of_nonneg_left hP
              (mul_nonneg hnuFactor hC)
      _ = C * A * G s := by
            dsimp [G, C]
            rw [Real.rpow_neg hr.le]
            ring
  have hmaj : ∀ᵐ s : ℝ, s ∈ Ioc u₀ u → ‖F s‖ ≤ C * A * G s :=
    Filter.Eventually.of_forall (fun s hs => by
      simpa only [Real.norm_eq_abs] using hpoint s hs)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hu₀u.le
    hmaj (hGI.const_mul (C * A))
  have hmain : |stripIntegralI₁ u₁ top T u₀ u v hseg| ≤
      C * A * ∫ s in u₀..u, G s := by
    simpa only [stripIntegralI₁, abs_neg, Real.norm_eq_abs,
      intervalIntegral.integral_const_mul] using hnorm
  calc
    |stripIntegralI₁ u₁ top T u₀ u v hseg|
        ≤ C * A * ∫ s in u₀..u, G s := hmain
    _ ≤ C * A * ((T.r u v)^(-δ) / δ) :=
      mul_le_mul_of_nonneg_left hGbound (mul_nonneg hC hAnon)
    _ = (2 * q / (1 - q)) * A * (T.r u v)^(-((1 : ℝ) / 2)) := by
      dsimp [C, δ]
      ring

end ChristodoulouBV.Uniqueness

end
