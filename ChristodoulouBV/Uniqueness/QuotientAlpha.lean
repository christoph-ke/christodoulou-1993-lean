module

public import ChristodoulouBV.Uniqueness.QuotientIntegral

/-!
# Incoming scalar quotient integration

The quotient is integrated on each fixed good incoming ray. Its initial
value agrees because both initial primitive densities agree there.
-/

@[expose] public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- Integrate the incoming difference equation against bounds for the two
quotient terms and the scalar difference on one characteristic. -/
theorem ComparisonData.alpha_ratio_le_coefficient_integrals
    (D : ComparisonData) (ha : D.a = 0)
    {u v A P Q : ℝ} (huv : (u, v) ∈ triangle D.a D.b)
    (hvG : v ∈ D.goodV)
    (hA : ∀ s ∈ Icc D.a u,
      |D.S₁.alpha s v / D.S₁.lam s v -
        D.S₂.alpha s v / D.S₂.lam s v| ≤ A)
    (hP : ∀ s ∈ Icc D.a u,
      |D.S₁.phi s v - D.S₂.phi s v| ≤ P)
    (hQ : ∀ s ∈ Icc D.a u,
      |D.S₂.theta s v / D.S₂.lam s v| ≤ Q) :
    |D.S₁.alpha u v / D.S₁.lam u v -
      D.S₂.alpha u v / D.S₂.lam u v| ≤
      (A + P) * (∫ s in D.a..u,
        -IsBVSolution.incomingCoeff D.S₁ s v) +
      Q * (∫ s in D.a..u,
        |IsBVSolution.incomingCoeff D.S₁ s v -
          IsBVSolution.incomingCoeff D.S₂ s v|) := by
  let f : ℝ → ℝ := fun s =>
    D.S₁.alpha s v / D.S₁.lam s v -
      D.S₂.alpha s v / D.S₂.lam s v
  let k : ℝ → ℝ := fun s => IsBVSolution.incomingCoeff D.S₁ s v
  let d : ℝ → ℝ := fun s =>
    |IsBVSolution.incomingCoeff D.S₁ s v -
      IsBVSolution.incomingCoeff D.S₂ s v|
  let g : ℝ → ℝ := fun s => (A + P) * (-k s) + Q * d s
  have hAC := D.alpha_ratio_source_ae le_rfl huv.1 huv.2.1 huv.2.2
  have hK := D.incomingCoeff_integrable_pair ha v
    ⟨huv.1.trans_lt huv.2.1, huv.2.2⟩
  have hK₁ : IntervalIntegrable k volume D.a u := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.1).2
    exact hK.1.mono_set (Ioc_subset_Ioc_right huv.2.1.le)
  have hK₂ : IntervalIntegrable
      (fun s => IsBVSolution.incomingCoeff D.S₂ s v)
      volume D.a u := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.1).2
    exact hK.2.mono_set (Ioc_subset_Ioc_right huv.2.1.le)
  have hD : IntervalIntegrable d volume D.a u :=
    (hK₁.sub hK₂).abs
  have hG : IntervalIntegrable g volume D.a u :=
    (hK₁.neg.const_mul (A + P)).add (hD.const_mul Q)
  have hder : ∀ᵐ s ∂volume, s ∈ Icc D.a u → |deriv f s| ≤ g s := by
    filter_upwards [hAC.2] with s hsder hs
    have hsT : (s, v) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨hs.1, hs.2.trans_lt huv.2.1, huv.2.2⟩
    have hpt := D.alpha_ratio_forcing_abs_le hsT
      (hA s hs) (hP s hs) (hQ s hs)
    simpa only [f, g, k, d, hsder hs, mul_comm] using hpt
  have hbound := quotient_transport_abs_le_integral huv.1 hAC.1 hG hder
  have hvab : v ∈ Ioo D.a D.b :=
    ⟨huv.1.trans_lt huv.2.1, huv.2.2⟩
  obtain ⟨hLam, hAlpha⟩ := hvG hvab
  have hzero : f D.a = 0 := by
    dsimp [f]
    rw [hLam, hAlpha]
    ring
  have hsum : (∫ s in D.a..u, g s) =
      (A + P) * (∫ s in D.a..u, -k s) +
        Q * (∫ s in D.a..u, d s) := by
    have hadd := intervalIntegral.integral_add
      (hK₁.neg.const_mul (A + P)) (hD.const_mul Q)
    calc
      (∫ s in D.a..u, g s) =
          (∫ s in D.a..u, (A + P) * (-k s) + Q * d s) := rfl
      _ = (∫ s in D.a..u, (A + P) * (-k s)) +
          (∫ s in D.a..u, Q * d s) := by
            simpa only [Pi.neg_apply] using hadd
      _ = _ := by rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
  change |f u - f D.a| ≤ ∫ s in D.a..u, g s at hbound
  rw [hzero, sub_zero, hsum] at hbound
  simpa only [f, k, d] using hbound

end ChristodoulouBV.Uniqueness

end
