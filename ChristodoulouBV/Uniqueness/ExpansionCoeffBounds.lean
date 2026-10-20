module

public import ChristodoulouBV.Uniqueness.ExpansionEquations

/-!
# Uniform transport coefficient bounds for expansion comparison

The outgoing coefficient bound applies to both members of the fixed pair.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

private def ComparisonData.swapped (D : ComparisonData) : ComparisonData where
  U₁ := D.U₂
  U₂ := D.U₁
  S₁ := D.S₂
  S₂ := D.S₁
  a := D.a
  b := D.b
  hab := D.hab
  h₁ := D.h₂
  h₂ := D.h₁
  hT := fun _ hp => (D.hT hp).symm
  hdata := fun v hv => ⟨(D.hdata v hv).1.symm, (D.hdata v hv).2.symm⟩

private theorem nuCoeff_real_le_of_lintegral
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u V M : ℝ} (huv : (u, V) ∈ U) (hM : 0 ≤ M)
    (hlin : (∫⁻ t in Ioc u V,
      ENNReal.ofReal (IsBVSolution.nuCoeff S u t)) ≤ ENNReal.ofReal M) :
    (∫ t in u..V, IsBVSolution.nuCoeff S u t) ≤ M := by
  have hlt : u < V := (h.solution.development.wedge huv).2
  obtain ⟨Q, _, hQ⟩ := h.exists_theta_div_lam_bound_out huv
  have hint : IntegrableOn (IsBVSolution.nuCoeff S u) (Ioc u V) :=
    h.nu_coeff_integrable_axis huv hQ
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc u V)]
      (IsBVSolution.nuCoeff S u) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro t ht
    exact h.nu_coeff_nonneg h.solution.development
      (h.solution.development.outgoing_mem huv ht.1 ht.2)
  have hreal : 0 ≤ ∫ t in Ioc u V, IsBVSolution.nuCoeff S u t :=
    integral_nonneg_of_ae hnonneg
  have heq : ENNReal.ofReal
      (∫ t in Ioc u V, IsBVSolution.nuCoeff S u t) =
      ∫⁻ t in Ioc u V, ENNReal.ofReal (IsBVSolution.nuCoeff S u t) :=
    ofReal_integral_eq_lintegral_ofReal hint hnonneg
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top (heq.trans_le hlin)
  rw [ENNReal.toReal_ofReal hreal, ENNReal.toReal_ofReal hM] at hle
  simpa only [intervalIntegral.integral_of_le hlt.le] using hle

/-- Both nonnegative outgoing transport coefficients have one common finite
integral bound, uniform in the compact top. -/
theorem ComparisonData.nuCoeff_integral_uniform_pair (D : ComparisonData) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ V, D.a < V → V < D.b →
        ∀ u ∈ Ico D.a V,
          (∫ t in u..V, IsBVSolution.nuCoeff D.S₁ u t) ≤ M ∧
          (∫ t in u..V, IsBVSolution.nuCoeff D.S₂ u t) ≤ M := by
  obtain ⟨M₁, hM₁, hlin₁⟩ := D.swapped.nuCoeff_lintegral_uniform
  obtain ⟨M₂, hM₂, hlin₂⟩ := D.nuCoeff_lintegral_uniform
  refine ⟨max M₁ M₂, hM₁.trans (le_max_left _ _), ?_⟩
  intro V haV hVb u hu
  have hpoint : (u, V) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨hu.1, hu.2, hVb⟩
  have hp := D.hT hpoint
  have hbound₁ : (∫⁻ t in Ioc u V,
      ENNReal.ofReal (IsBVSolution.nuCoeff D.S₁ u t)) ≤
      ENNReal.ofReal M₁ := by
    simpa only [ComparisonData.swapped] using hlin₁ V haV hVb u hu
  exact ⟨(nuCoeff_real_le_of_lintegral D.h₁ hp.1 hM₁ hbound₁).trans
      (le_max_left _ _),
    (nuCoeff_real_le_of_lintegral D.h₂ hp.2 hM₂
      (hlin₂ V haV hVb u hu)).trans (le_max_right _ _)⟩

theorem exp_abs_sub_le_of_Icc
    {x y M : ℝ} (hx : x ∈ Icc 0 M) (hy : y ∈ Icc 0 M) :
    |Real.exp x - Real.exp y| ≤ Real.exp M * |x - y| := by
  have hderiv (t : ℝ) (ht : t ∈ Icc 0 M) :
      ‖deriv Real.exp t‖ ≤ Real.exp M := by
    rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
    exact Real.exp_le_exp.mpr ht.2
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := Real.exp) (s := Icc 0 M) (C := Real.exp M)
    (fun t _ => Real.differentiableAt_exp) hderiv
    (convex_Icc 0 M) hy hx
  simpa only [Real.norm_eq_abs] using h

theorem nuCoeff_integral_nonneg
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    0 ≤ ∫ t in u..v, IsBVSolution.nuCoeff S u t := by
  have hlt : u < v := (h.solution.development.wedge huv).2
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc u v)]
      (IsBVSolution.nuCoeff S u) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro t ht
    exact h.nu_coeff_nonneg h.solution.development
      (h.solution.development.outgoing_mem huv ht.1 ht.2)
  have hh : 0 ≤ ∫ t in Ioc u v, IsBVSolution.nuCoeff S u t :=
    integral_nonneg_of_ae hnonneg
  simpa only [intervalIntegral.integral_of_le hlt.le] using hh

/-- The outgoing expansion difference is bounded by the good-ray axis trace
and an integral of the absolute coefficient difference. The same constant
works as the compact top approaches the open top of the triangle. -/
theorem ComparisonData.nu_difference_le_integral_coeff (D : ComparisonData) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ V, D.a < V → V < D.b →
        ∀ u v, (u, v) ∈ triangle D.a V → v ∈ D.goodV →
          |D.S₁.nu u v - D.S₂.nu u v| ≤
            C * (D.L V +
              ∫ t in u..v,
                |IsBVSolution.nuCoeff D.S₁ u t -
                  IsBVSolution.nuCoeff D.S₂ u t|) := by
  obtain ⟨M, hM, hcoeff⟩ := D.nuCoeff_integral_uniform_pair
  obtain ⟨K, hK, _⟩ := D.h₂.exists_uniform_radius_upper
  let C : ℝ := Real.exp M * (1 + max K 0)
  have hExp : 1 ≤ Real.exp M := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hM
  have hKnonneg : 0 ≤ max K 0 := le_max_right _ _
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [mul_nonneg (sub_nonneg.mpr hExp) hKnonneg]
  refine ⟨C, hC, ?_⟩
  intro V haV hVb u v huv hvG
  have hfull : (u, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨huv.1, huv.2.1, huv.2.2.trans hVb⟩
  have hp := D.hT hfull
  obtain ⟨l₁, l₂, haxis, hlim₂, hformula⟩ :=
    D.nu_difference_axis_formula haV hVb huv
  have htrace₂ : |l₂| ≤ max K 0 := by
    have hevent : ∀ᶠ t in 𝓝[>] u, |D.S₂.lam u t| ≤ max K 0 := by
      filter_upwards [Ioo_mem_nhdsGT hfull.2.1] with t ht
      have htU := D.h₂.solution.development.outgoing_mem hp.2 ht.1 ht.2.le
      rw [abs_of_pos (D.h₂.solution.lam_pos (u, t) htU)]
      exact (hK (u, t) htU).trans (le_max_left _ _)
    exact le_of_tendsto hlim₂.abs hevent
  have hA₁ : 0 ≤ ∫ t in u..v, IsBVSolution.nuCoeff D.S₁ u t :=
    nuCoeff_integral_nonneg D.h₁ hp.1
  have hA₂ : 0 ≤ ∫ t in u..v, IsBVSolution.nuCoeff D.S₂ u t :=
    nuCoeff_integral_nonneg D.h₂ hp.2
  have hupper := hcoeff v (huv.1.trans_lt huv.2.1)
    (huv.2.2.trans hVb) u ⟨huv.1, huv.2.1⟩
  have hExpDiff := exp_abs_sub_le_of_Icc
    ⟨hA₁, hupper.1⟩ ⟨hA₂, hupper.2⟩
  obtain ⟨Q₁, _, hQ₁⟩ := D.h₁.exists_theta_div_lam_bound_out hp.1
  obtain ⟨Q₂, _, hQ₂⟩ := D.h₂.exists_theta_div_lam_bound_out hp.2
  have hk₁ : IntervalIntegrable (IsBVSolution.nuCoeff D.S₁ u) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).2
      (D.h₁.nu_coeff_integrable_axis hp.1 hQ₁)
  have hk₂ : IntervalIntegrable (IsBVSolution.nuCoeff D.S₂ u) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).2
      (D.h₂.nu_coeff_integrable_axis hp.2 hQ₂)
  have hIntEq :
      (∫ t in u..v, IsBVSolution.nuCoeff D.S₁ u t) -
        (∫ t in u..v, IsBVSolution.nuCoeff D.S₂ u t) =
      ∫ t in u..v,
        (IsBVSolution.nuCoeff D.S₁ u t -
          IsBVSolution.nuCoeff D.S₂ u t) :=
    (intervalIntegral.integral_sub hk₁ hk₂).symm
  have hIntAbs :
      |(∫ t in u..v, IsBVSolution.nuCoeff D.S₁ u t) -
        (∫ t in u..v, IsBVSolution.nuCoeff D.S₂ u t)| ≤
      ∫ t in u..v,
        |IsBVSolution.nuCoeff D.S₁ u t -
          IsBVSolution.nuCoeff D.S₂ u t| := by
    rw [hIntEq]
    exact intervalIntegral.abs_integral_le_integral_abs huv.2.1.le
  have hLnonneg : 0 ≤ D.L V := (abs_nonneg _).trans haxis
  have hInonneg : 0 ≤ ∫ t in u..v,
      |IsBVSolution.nuCoeff D.S₁ u t -
        IsBVSolution.nuCoeff D.S₂ u t| :=
    intervalIntegral.integral_nonneg huv.2.1.le (fun _ _ => abs_nonneg _)
  rw [hformula]
  calc
    |-(l₁ - l₂) * Real.exp (∫ t in u..v, IsBVSolution.nuCoeff D.S₁ u t) -
        l₂ * (Real.exp (∫ t in u..v, IsBVSolution.nuCoeff D.S₁ u t) -
          Real.exp (∫ t in u..v, IsBVSolution.nuCoeff D.S₂ u t))| ≤
      |l₁ - l₂| * Real.exp M +
        |l₂| * (Real.exp M *
          ∫ t in u..v,
            |IsBVSolution.nuCoeff D.S₁ u t -
              IsBVSolution.nuCoeff D.S₂ u t|) := by
      have hExpBound := Real.exp_le_exp.mpr hupper.1
      calc
        _ ≤ |l₁ - l₂| *
            Real.exp (∫ t in u..v, IsBVSolution.nuCoeff D.S₁ u t) +
          |l₂| *
            |Real.exp (∫ t in u..v, IsBVSolution.nuCoeff D.S₁ u t) -
              Real.exp (∫ t in u..v, IsBVSolution.nuCoeff D.S₂ u t)| := by
          simpa only [abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)] using
            abs_sub (-(l₁ - l₂) * Real.exp
              (∫ t in u..v, IsBVSolution.nuCoeff D.S₁ u t))
              (l₂ * (Real.exp
                (∫ t in u..v, IsBVSolution.nuCoeff D.S₁ u t) -
                Real.exp
                (∫ t in u..v, IsBVSolution.nuCoeff D.S₂ u t)))
        _ ≤ _ := add_le_add
          (mul_le_mul_of_nonneg_left hExpBound (abs_nonneg _))
          (mul_le_mul_of_nonneg_left
            (hExpDiff.trans (mul_le_mul_of_nonneg_left hIntAbs
              (Real.exp_pos _).le)) (abs_nonneg _))
    _ ≤ C * (D.L V +
        ∫ t in u..v,
          |IsBVSolution.nuCoeff D.S₁ u t -
            IsBVSolution.nuCoeff D.S₂ u t|) := by
      dsimp [C]
      nlinarith [mul_nonneg hKnonneg hLnonneg,
        mul_nonneg hKnonneg hInonneg,
        mul_nonneg (Real.exp_pos M).le hLnonneg,
        mul_nonneg (Real.exp_pos M).le hInonneg]

end ChristodoulouBV.Uniqueness

end
