module

public import ChristodoulouBV.BVSolution.LogCoefficient
import ChristodoulouBV.ForMathlib.BoundedVariation.SliceFacts

/-!
# Outgoing expansion at the regular axis

The bounded-variation expansion has a one-sided trace. The outgoing linear
equation and the integrable radial coefficient transport that trace to each
point of the characteristic.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.IsBVSolution

/-- The outgoing expansion has a finite one-sided trace at every accessible
regular-axis point. -/
theorem exists_lam_axis_limit_out
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    ∃ L : ℝ, Tendsto (S.lam u) (𝓝[>] u) (𝓝 L) := by
  have hBV : BoundedVariationOn (S.lam u) {t | (u, t) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item1.choose_spec.1 u)
  obtain ⟨L, hL⟩ := hBV.exists_tendsto_right u
  refine ⟨L, ?_⟩
  have hfilter : 𝓝[{t | (u, t) ∈ U} ∩ Ioi u] u = 𝓝[>] u := by
    calc
      𝓝[{t | (u, t) ∈ U} ∩ Ioi u] u =
          𝓝[>] u ⊓ 𝓟 {t | (u, t) ∈ U} := by
            simp only [nhdsWithin, ← Filter.inf_principal]
            ac_rfl
      _ = 𝓝[>] u := h.solution.development.axis_filter_eq huv
  simpa only [hfilter] using hL

/-- The scalar-amplitude BV bound and the positive expansion bound give a
finite outgoing quotient bound on every full axis-to-point slice. -/
theorem exists_theta_div_lam_bound_out
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ t ∈ Ioc u v, |S.theta u t / S.lam u t| ≤ M := by
  have hBV : BoundedVariationOn (S.theta u) {t | (u, t) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item5.choose_spec.1 u)
  obtain ⟨B, hB, hbound⟩ := hBV.exists_bound_on
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  refine ⟨B / c, div_nonneg hB hc.le, ?_⟩
  intro t ht
  have htU := h.solution.development.outgoing_mem huv ht.1 ht.2
  have hl : 0 < S.lam u t := h.solution.lam_pos (u, t) htU
  have hcl : c ≤ S.lam u t := hlam (u, t) htU
  have hθ := hbound t htU
  rw [abs_div, abs_of_pos hl]
  apply (div_le_div_iff₀ hl hc).2
  calc
    |S.theta u t| * c ≤ B * c :=
      mul_le_mul_of_nonneg_right hθ hc.le
    _ ≤ B * S.lam u t := mul_le_mul_of_nonneg_left hcl hB

/-- The one-sided axis expansion is the coefficient of the outgoing
exponential solution for the incoming expansion. -/
theorem nu_axis_exponential
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    ∃ L : ℝ,
      Tendsto (S.lam u) (𝓝[>] u) (𝓝 L) ∧
      S.nu u v =
        -L * Real.exp (∫ t in u..v, nuCoeff S u t) := by
  obtain ⟨L, hLam⟩ := h.exists_lam_axis_limit_out huv
  obtain ⟨M, _, hM⟩ := h.exists_theta_div_lam_bound_out huv
  have huvlt := (h.solution.development.wedge huv).2
  have hcoeff : IntervalIntegrable (nuCoeff S u) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huvlt.le).2
      (h.nu_coeff_integrable_axis huv hM)
  let F : ℝ → ℝ := fun a => ∫ t in u..a, nuCoeff S u t
  have hFAC : AbsolutelyContinuousOnInterval F u v :=
    hcoeff.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hright : Tendsto (fun a : ℝ => a) (𝓝[>] u) (𝓝[Icc u v] u) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left inf_le_left,
      mem_of_superset (Ioo_mem_nhdsGT huvlt)
        (fun a ha => ⟨ha.1.le, ha.2.le⟩)⟩
  have hF : Tendsto F (𝓝[>] u) (𝓝 (0 : ℝ)) := by
    have hcont : ContinuousOn F (Icc u v) := by
      simpa only [uIcc_of_le huvlt.le] using hFAC.continuousOn
    have hh := (hcont.continuousWithinAt
      (show u ∈ Icc u v from ⟨le_rfl, huvlt.le⟩)).tendsto.comp hright
    simpa only [F, Function.comp_def, intervalIntegral.integral_same] using hh
  have hnuAxis : Tendsto (S.nu u) (𝓝[>] u) (𝓝 (-L)) := by
    have haxis : Tendsto (fun t => S.nu u t + S.lam u t)
        (𝓝[>] u) (𝓝 (0 : ℝ)) := by
      simpa only [h.solution.development.axis_filter_eq huv] using
        h.item2 u (h.solution.development.axis_mem huv)
    simpa only [add_sub_cancel_right, zero_sub] using haxis.sub hLam
  have hsplit : ∀ᶠ a in 𝓝[>] u,
      (∫ t in a..v, nuCoeff S u t) =
        (∫ t in u..v, nuCoeff S u t) - F a := by
    filter_upwards [Ioo_mem_nhdsGT huvlt] with a ha
    have hleft : IntervalIntegrable (nuCoeff S u) volume u a :=
      hcoeff.mono_set (by
        rw [uIcc_of_le huvlt.le, uIcc_of_le ha.1.le]
        exact Icc_subset_Icc_right ha.2.le)
    have hright' : IntervalIntegrable (nuCoeff S u) volume a v :=
      hcoeff.mono_set (by
        rw [uIcc_of_le huvlt.le, uIcc_of_le ha.2.le]
        exact Icc_subset_Icc_left ha.1.le)
    have hh := intervalIntegral.integral_add_adjacent_intervals hleft hright'
    dsimp [F]
    linarith
  have hIntLim : Tendsto (fun a => ∫ t in a..v, nuCoeff S u t)
      (𝓝[>] u) (𝓝 (∫ t in u..v, nuCoeff S u t)) := by
    have hh : Tendsto (fun a => (∫ t in u..v, nuCoeff S u t) - F a)
        (𝓝[>] u) (𝓝 (∫ t in u..v, nuCoeff S u t)) := by
      simpa using tendsto_const_nhds.sub hF
    exact hh.congr' (hsplit.mono fun _ heq => heq.symm)
  have hformula : ∀ᶠ a in 𝓝[>] u,
      S.nu u v = Real.exp (∫ t in a..v, nuCoeff S u t) * S.nu u a := by
    filter_upwards [Ioo_mem_nhdsGT huvlt] with a ha
    exact nu_eq_exp_mul h.solution.development h huv ha.1 ha.2.le le_rfl
  have hRHS : Tendsto
      (fun a => Real.exp (∫ t in a..v, nuCoeff S u t) * S.nu u a)
      (𝓝[>] u)
      (𝓝 (Real.exp (∫ t in u..v, nuCoeff S u t) * -L)) :=
    (Real.continuous_exp.tendsto _ |>.comp hIntLim).mul hnuAxis
  have heq : S.nu u v =
      Real.exp (∫ t in u..v, nuCoeff S u t) * -L :=
    tendsto_nhds_unique tendsto_const_nhds
      (hRHS.congr' (hformula.mono fun _ he => he.symm))
  refine ⟨L, hLam, ?_⟩
  rw [heq]
  ring

end ChristodoulouBV.IsBVSolution

end
