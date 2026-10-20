module

public import ChristodoulouBV.Uniqueness.IncomingMassIntegrability

/-!
# Corrected terminal-value formula for incoming mass difference

The diagonal mass is a trace, and the coefficient is integrable on the full
half-open incoming ray. The sign in the exponent is positive relative to
`ζ₂²/(ν₂ r₁)`; this quantity is nonpositive because `ν₂ < 0`.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The corrected terminal mass formula on a full augmented comparison
triangle. The exponent is nonpositive and therefore defines a decaying
integrating factor. -/
theorem ComparisonData.mass_in_terminal_formula (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    D.S₁.m u v - D.S₂.m u v =
      -(1 / 2 : ℝ) *
        (∫ s in u..v,
          Real.exp (∫ t in u..s,
            D.S₂.zeta t v ^ 2 /
              (D.S₂.nu t v * D.S₁.r t v)) *
            incomingMassForcing D s v) := by
  let k : ℝ → ℝ := fun s => incomingMassCoefficient D s v
  let g : ℝ → ℝ := fun s => incomingMassForcing D s v / 2
  let y : ℝ → ℝ := fun s => D.S₁.m s v - D.S₂.m s v
  have hT₁ : triangle D.a D.b ⊆ D.U₁ := fun p hp => (D.hT hp).1
  have hT₂ : triangle D.a D.b ⊆ D.U₂ := fun p hp => (D.hT hp).2
  have haccess₁ := IsBVSolution.incoming_axis_access_of_triangle hT₁ huv
  have haccess₂ := IsBVSolution.incoming_axis_access_of_triangle hT₂ huv
  have hk : IntervalIntegrable k volume u v :=
    D.incomingMassCoefficient_integrable huv
  have hg : IntervalIntegrable g volume u v :=
    D.incomingMassForcing_integrable huv
  have hyAC : ∀ w, u ≤ w → w < v →
      AbsolutelyContinuousOnInterval y u w := by
    intro w huw hwv
    have hseg₁ := IsBVSolution.incoming_seg_subset_of_half_open_access
      hwv haccess₁
    have hseg₂ := IsBVSolution.incoming_seg_subset_of_half_open_access
      hwv haccess₂
    exact (D.h₁.solution.mass_in_ac_ae huw hseg₁).1.sub
      (D.h₂.solution.mass_in_ac_ae huw hseg₂).1
  have hy' : ∀ w, u ≤ w → w < v →
      ∀ᵐ s ∂volume, s ∈ uIcc u w →
        HasDerivAt y (k s * y s + g s) s := by
    intro w huw hwv
    filter_upwards [(hyAC w huw hwv).ae_differentiableAt,
      D.mass_in_difference_ae huv huw hwv] with s hd hdiff hs
    have hsIcc : s ∈ Icc u w := by
      simpa only [uIcc_of_le huw] using hs
    have heq := hdiff hsIcc
    have hderiv := (hd hs).hasDerivAt
    change HasDerivAt y (deriv y s) s at hderiv
    rw [heq] at hderiv
    exact hderiv
  have hlim₁ := D.h₁.incoming_mass_axis_trace_of_triangle hT₁ huv
  have hlim₂ := D.h₂.incoming_mass_axis_trace_of_triangle hT₂ huv
  have hlim : Tendsto y (𝓝[<] v) (𝓝 (0 : ℝ)) := by
    simpa only [y, sub_self] using hlim₁.sub hlim₂
  have hformula := terminal_integral_formula_of_ae_hasDerivAt
    huv.2.1 hk hg hyAC hy' hlim
  have hinner (s : ℝ) :
      -(∫ t in u..s, k t) =
        ∫ t in u..s, D.S₂.zeta t v ^ 2 /
          (D.S₂.nu t v * D.S₁.r t v) := by
    unfold k incomingMassCoefficient
    rw [intervalIntegral.integral_neg]
    ring
  have hIntegrand :
      (fun s => Real.exp (-(∫ t in u..s, k t)) * g s) =
        (fun s => (1 / 2 : ℝ) *
          (Real.exp (∫ t in u..s,
            D.S₂.zeta t v ^ 2 /
              (D.S₂.nu t v * D.S₁.r t v)) *
            incomingMassForcing D s v)) := by
    funext s
    rw [hinner]
    dsimp [g]
    ring
  rw [hIntegrand, intervalIntegral.integral_const_mul] at hformula
  dsimp only [y] at hformula
  convert hformula using 1; ring

/-- The corrected terminal integrating factor lies between zero and one
on every subsegment of a full incoming ray. -/
theorem ComparisonData.incoming_mass_factor_le_one (D : ComparisonData)
    {u s v : ℝ} (huv : (u, v) ∈ triangle D.a D.b)
    (hs : s ∈ Icc u v) :
    Real.exp (∫ t in u..s,
      D.S₂.zeta t v ^ 2 /
        (D.S₂.nu t v * D.S₁.r t v)) ≤ 1 := by
  have hT₂ : triangle D.a D.b ⊆ D.U₂ := fun p hp => (D.hT hp).2
  have hT₁ : triangle D.a D.b ⊆ D.U₁ := fun p hp => (D.hT hp).1
  have hk := D.incomingMassCoefficient_integrable huv
  have hbase : ∀ t ∈ Ico u v,
      D.S₂.zeta t v ^ 2 /
        (D.S₂.nu t v * D.S₁.r t v) ≤ 0 := by
    intro t ht
    have hpt : (t, v) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨huv.1.trans ht.1, ht.2, huv.2.2⟩
    have hp := D.hT hpt
    obtain ⟨c, hc, hlam⟩ := D.h₂.lam_bounded_below
    have hnu := D.h₂.nu_le_neg_lower hc hlam hp.2
    have hr := D.h₁.solution.radius_pos (t, v) hp.1
    exact div_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) hr.le)
  have hint : IntervalIntegrable
      (fun t => D.S₂.zeta t v ^ 2 /
        (D.S₂.nu t v * D.S₁.r t v)) volume u s := by
    have hsub : uIcc u s ⊆ uIcc u v := by
      rw [uIcc_of_le hs.1, uIcc_of_le huv.2.1.le]
      exact Icc_subset_Icc_right hs.2
    have h := hk.mono_set hsub
    have heq : (fun t => D.S₂.zeta t v ^ 2 /
        (D.S₂.nu t v * D.S₁.r t v)) =
        -(fun t => incomingMassCoefficient D t v) := by
      funext t
      unfold incomingMassCoefficient
      simp only [Pi.neg_apply, neg_neg]
    simpa only [heq] using h.neg
  have hnonpos : (∫ t in u..s,
      D.S₂.zeta t v ^ 2 /
        (D.S₂.nu t v * D.S₁.r t v)) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hs.1]
    apply integral_nonpos_of_ae
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    have hne : ∀ᵐ t : ℝ ∂volume, t ≠ v := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with t hne ht
    have htv : t < v := lt_of_le_of_ne (ht.2.trans hs.2) hne
    exact hbase t ⟨ht.1.le, htv⟩
  exact (Real.exp_le_one_iff).2 hnonpos

end ChristodoulouBV.Uniqueness

end
