module

public import ChristodoulouBV.Uniqueness.UniformThresholdIncomingMassForcing
public import ChristodoulouBV.Uniqueness.IncomingMassHardy

/-!
# Package-uniform incoming mass difference

The terminal integrating factor transfers the package-based forcing estimate
to the mass difference on each compact top.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The decaying terminal factor turns the corrected mass equation into the
source estimate `|Δm| ≤ C(B+N) I*`, uniformly in the compact top. -/
theorem UniformThresholdBounds.mass_in_difference_le_IStar
    (P : UniformThresholdBounds) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ P.gapThreshold) →
        ∀ V u v, D.a < V → V < D.b →
          (u, v) ∈ triangle D.a V →
          |D.S₁.m u v - D.S₂.m u v| ≤
            C * (D.B V + D.N V) * IStar D u v) := by
  obtain ⟨Cforce, hCforce, hforce⟩ := P.incoming_mass_forcing_le
  let C := 3 * Cforce ^ 2
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [sq_nonneg Cforce]
  refine ⟨C, hC, ?_⟩
  intro D ha hb hP hsmall V u v haV hVb huv
  have hfull : (u, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨huv.1, huv.2.1, huv.2.2.trans hVb⟩
  have hT₁ : triangle D.a D.b ⊆ D.U₁ := fun p hp => (D.hT hp).1
  have hT₂ : triangle D.a D.b ⊆ D.U₂ := fun p hp => (D.hT hp).2
  have hf₁ := zeta_abs_integrable D.h₁ hT₁ hfull
  have hf₂ := zeta_abs_integrable D.h₂ hT₂ hfull
  have hf : IntervalIntegrable
      (fun s => |D.S₁.zeta s v| + |D.S₂.zeta s v|) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).2
      (hf₁.add hf₂)
  have hFhalf := D.incomingMassForcing_integrable hfull
  have hF : IntervalIntegrable (fun s => incomingMassForcing D s v)
      volume u v := by
    have hh := hFhalf.const_mul 2
    convert hh using 1
    funext s
    ring
  let k : ℝ → ℝ := fun s => D.S₂.zeta s v ^ 2 /
    (D.S₂.nu s v * D.S₁.r s v)
  have hk : IntervalIntegrable k volume u v := by
    have hh := (D.incomingMassCoefficient_integrable hfull).neg
    convert hh using 1
    funext s
    unfold k incomingMassCoefficient
    simp
  let E : ℝ → ℝ := fun s => Real.exp (∫ t in u..s, k t)
  have hE : AbsolutelyContinuousOnInterval E u v :=
    (hk.absolutelyContinuousOnInterval_intervalIntegral (by simp)).exp
  have hEF : IntervalIntegrable (fun s => E s * incomingMassForcing D s v)
      volume u v := hF.continuousOn_mul hE.continuousOn
  have hBN : 0 ≤ D.B V + D.N V :=
    add_nonneg (D.B_nonneg ha hVb.le) (D.N_nonneg haV hVb)
  have hconst : 0 ≤ C * (D.B V + D.N V) :=
    mul_nonneg (by linarith) hBN
  have hbound : ∀ s ∈ Ioo u v,
      |E s * incomingMassForcing D s v| ≤
        C * (D.B V + D.N V) *
          (|D.S₁.zeta s v| + |D.S₂.zeta s v|) := by
    intro s hs
    have hst : (s, v) ∈ triangle D.a V :=
      (mem_triangle).2 ⟨huv.1.trans hs.1.le, hs.2, huv.2.2⟩
    have hfactor := D.incoming_mass_factor_le_one hfull
      (show s ∈ Icc u v from ⟨hs.1.le, hs.2.le⟩)
    have hforce' := hforce D ha hb hP hsmall V s v haV hVb hst
    calc
      |E s * incomingMassForcing D s v| =
          E s * |incomingMassForcing D s v| := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ |incomingMassForcing D s v| := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hfactor (abs_nonneg _)
      _ ≤ C * (D.B V + D.N V) *
          (|D.S₁.zeta s v| + |D.S₂.zeta s v|) := hforce'
  have hI : (∫ s in u..v, |E s * incomingMassForcing D s v|) ≤
      C * (D.B V + D.N V) * IStar D u v := by
    have hright : IntervalIntegrable
        (fun s => C * (D.B V + D.N V) *
          (|D.S₁.zeta s v| + |D.S₂.zeta s v|)) volume u v :=
      hf.const_mul _
    have hh := intervalIntegral.integral_mono_on_of_le_Ioo
      huv.2.1.le hEF.abs hright hbound
    rw [intervalIntegral.integral_const_mul] at hh
    exact hh
  have hmass := D.mass_in_terminal_formula hfull
  rw [hmass, abs_mul, abs_neg, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  have hInt := intervalIntegral.abs_integral_le_integral_abs (μ := volume) huv.2.1.le
    (f := fun s => E s * incomingMassForcing D s v)
  have hIstar : 0 ≤ IStar D u v := by
    unfold IStar
    apply intervalIntegral.integral_nonneg huv.2.1.le
    intro s _
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hright : 0 ≤ C * (D.B V + D.N V) * IStar D u v :=
    mul_nonneg hconst hIstar
  change (1 / 2 : ℝ) *
    |∫ s in u..v, E s * incomingMassForcing D s v| ≤
      C * (D.B V + D.N V) * IStar D u v
  calc
    (1 / 2 : ℝ) * |∫ s in u..v, E s * incomingMassForcing D s v| ≤
        (1 / 2 : ℝ) * (∫ s in u..v,
          |E s * incomingMassForcing D s v|) :=
      mul_le_mul_of_nonneg_left hInt (by norm_num)
    _ ≤ (1 / 2 : ℝ) *
        (C * (D.B V + D.N V) * IStar D u v) :=
      mul_le_mul_of_nonneg_left hI (by norm_num)
    _ ≤ C * (D.B V + D.N V) * IStar D u v := by
      linarith only [hright]


end ChristodoulouBV.Uniqueness

end
