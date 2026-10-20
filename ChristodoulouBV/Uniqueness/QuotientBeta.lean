module

public import ChristodoulouBV.Uniqueness.QuotientAlphaNorm

/-!
# Outgoing scalar quotient integration
-/

@[expose] public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- Integrate the outgoing quotient equation away from the axis. The axis
limit is inserted only after this compact interval estimate. -/
theorem ComparisonData.beta_ratio_le_coefficient_integrals
    (D : ComparisonData) {u x v B P Q : ℝ}
    (huv : (u, v) ∈ triangle D.a D.b)
    (hux : u < x) (hxv : x ≤ v)
    (hB : ∀ t ∈ Icc x v,
      |D.S₁.beta u t / D.S₁.nu u t -
        D.S₂.beta u t / D.S₂.nu u t| ≤ B)
    (hP : ∀ t ∈ Icc x v,
      |D.S₁.phi u t - D.S₂.phi u t| ≤ P)
    (hQ : ∀ t ∈ Icc x v,
      |D.S₂.zeta u t / D.S₂.nu u t| ≤ Q) :
    |(D.S₁.beta u v / D.S₁.nu u v -
        D.S₂.beta u v / D.S₂.nu u v) -
      (D.S₁.beta u x / D.S₁.nu u x -
        D.S₂.beta u x / D.S₂.nu u x)| ≤
      (B + P) * (∫ t in x..v,
        IsBVSolution.nuCoeff D.S₁ u t) +
      Q * (∫ t in x..v,
        |IsBVSolution.nuCoeff D.S₁ u t -
          IsBVSolution.nuCoeff D.S₂ u t|) := by
  let f : ℝ → ℝ := fun t =>
    D.S₁.beta u t / D.S₁.nu u t -
      D.S₂.beta u t / D.S₂.nu u t
  let k : ℝ → ℝ := fun t => IsBVSolution.nuCoeff D.S₁ u t
  let d : ℝ → ℝ := fun t =>
    |IsBVSolution.nuCoeff D.S₁ u t -
      IsBVSolution.nuCoeff D.S₂ u t|
  let g : ℝ → ℝ := fun t => (B + P) * k t + Q * d t
  have hAC := D.beta_ratio_source_ae huv.1 hux hxv huv.2.2
  have hp := D.hT huv
  obtain ⟨M, _, hM⟩ := D.h₁.exists_theta_div_lam_bound_out hp.1
  have hKfull := D.h₁.nu_coeff_integrable_axis hp.1 hM
  have hK : IntervalIntegrable k volume x v := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hxv).2
    exact hKfull.mono_set (Ioc_subset_Ioc hux.le le_rfl)
  have hDfull := D.nuCoeff_difference_integrable huv.2.2
    ⟨huv.1, huv.2.1⟩
  have hD : IntervalIntegrable d volume x v := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hxv).2
    exact hDfull.mono_set (Ioc_subset_Ioc hux.le le_rfl)
  have hG : IntervalIntegrable g volume x v :=
    (hK.const_mul (B + P)).add (hD.const_mul Q)
  have hder : ∀ᵐ t ∂volume, t ∈ Icc x v → |deriv f t| ≤ g t := by
    filter_upwards [hAC.2] with t htder ht
    have htT : (u, t) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨huv.1, hux.trans_le ht.1,
        ht.2.trans_lt huv.2.2⟩
    have hpt := D.beta_ratio_forcing_abs_le htT
      (hB t ht) (hP t ht) (hQ t ht)
    simpa only [f, g, k, d, htder ht, mul_comm] using hpt
  have hbound := quotient_transport_abs_le_integral hxv hAC.1 hG hder
  have hsum : (∫ t in x..v, g t) =
      (B + P) * (∫ t in x..v, k t) +
        Q * (∫ t in x..v, d t) := by
    have hadd := intervalIntegral.integral_add
      (hK.const_mul (B + P)) (hD.const_mul Q)
    calc
      (∫ t in x..v, g t) =
          (∫ t in x..v, (B + P) * k t + Q * d t) := rfl
      _ = (∫ t in x..v, (B + P) * k t) +
          (∫ t in x..v, Q * d t) := by simpa only using hadd
      _ = _ := by rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
  change |f v - f x| ≤ ∫ t in x..v, g t at hbound
  rw [hsum] at hbound
  simpa only [f, k, d] using hbound

end ChristodoulouBV.Uniqueness

end
