module

public import ChristodoulouBV.Uniqueness.UniformThresholdOutgoingMassHardy
public import ChristodoulouBV.Uniqueness.OutgoingMassBasis

/-!
# Scalar Hardy estimate from a shared numerical package

The radius upper bound is supplied by the package on the normalized triangle;
the BV variation argument is independent of the transport constants.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

private theorem scalar_deriv_integral_le_variation
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    (∫ t in u..v, |deriv (S.phi u) t|) ≤
      (eVariationOn (S.phi u) (Ioc u v)).toReal := by
  have hlt := (h.solution.development.wedge huv).2
  have hφ := h.scalar_deriv_integrable_on_axis_slice huv
  have hvarFinite : eVariationOn (S.phi u) (Ioc u v) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((eVariationOn.mono (S.phi u) (by
        intro t ht
        exact h.solution.development.outgoing_mem huv ht.1 ht.2)).trans
        (h.item3_variation.choose_spec.1 u))
  let W := (eVariationOn (S.phi u) (Ioc u v)).toReal
  have hW : 0 ≤ W := ENNReal.toReal_nonneg
  let a : ℕ → ℝ := fun n => u + (v - u) / ((n : ℝ) + 1)
  have hau (n : ℕ) : u < a n := by
    dsimp [a]
    have hp : 0 < ((n : ℝ) + 1) := by positivity
    have hd : 0 < (v - u) / ((n : ℝ) + 1) :=
      div_pos (sub_pos.mpr hlt) hp
    linarith
  have hav (n : ℕ) : a n ≤ v := by
    dsimp [a]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hp : 1 ≤ ((n : ℝ) + 1) := by linarith
    have hone : (v - u) / ((n : ℝ) + 1) ≤ v - u := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [mul_nonneg (sub_pos.mpr hlt).le hn]
    linarith
  have ha : Tendsto a atTop (𝓝 u) := by
    have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hconst : Tendsto (fun _ : ℕ => v - u) atTop (𝓝 (v - u)) :=
      tendsto_const_nhds
    have hh := (tendsto_const_nhds (x := u)).add (hconst.mul hzero)
    simpa only [a, div_eq_mul_inv, one_mul, mul_zero, add_zero] using hh
  have hInt : IntegrableOn (fun t => |deriv (S.phi u) t|)
      (Ioc u v) volume := hφ.abs
  have hlim := (aecover_Ioc_of_Ioc (μ := volume)
    ha (tendsto_const_nhds (x := v))).integral_tendsto_of_countably_generated hInt
  have hboundVar : ∀ n : ℕ,
      (∫ t in Ioc (a n) v, |deriv (S.phi u) t| ∂volume.restrict (Ioc u v)) ≤
        W := by
    intro n
    have hsubset : Icc (a n) v ⊆ Ioc u v := by
      intro t ht
      exact ⟨(hau n).trans_le ht.1, ht.2⟩
    have hBV : BoundedVariationOn (S.phi u) (Icc (a n) v) :=
      ne_top_of_le_ne_top hvarFinite
        (eVariationOn.mono (S.phi u) hsubset)
    have hvar : (eVariationOn (S.phi u) (Icc (a n) v)).toReal ≤ W :=
      ENNReal.toReal_mono hvarFinite
        (eVariationOn.mono (S.phi u) hsubset)
    have hderiv := hBV.integral_abs_deriv_le_eVariationOn (hav n)
    have hsubI : Ioc (a n) v ⊆ Ioc u v := by
      intro t ht
      exact ⟨(hau n).trans ht.1, ht.2⟩
    have heq : (∫ t in Ioc (a n) v, |deriv (S.phi u) t|
        ∂volume.restrict (Ioc u v)) =
        ∫ t in a n..v, |deriv (S.phi u) t| := by
      rw [Measure.restrict_restrict measurableSet_Ioc]
      rw [Set.inter_eq_self_of_subset_left hsubI]
      exact (intervalIntegral.integral_of_le (hav n)).symm
    rw [heq]
    exact hderiv.trans hvar
  have hresult := le_of_tendsto hlim (Filter.Eventually.of_forall hboundVar)
  have hderivBound : (∫ t in u..v, |deriv (S.phi u) t|) ≤ W := by
    rw [intervalIntegral.integral_of_le hlt.le]
    exact hresult
  exact hderivBound

/-- The reciprocal-distance outgoing scalar amplitude has a Hardy bound
whose constant is chosen from the package radius bound before comparison
data are selected. -/
theorem UniformThresholdBounds.theta_div_distance_integral_le_variation
    (P : UniformThresholdBounds) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        ∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (∫ t in u..v, |S.theta u t| / (t - u)) ≤
              K * (eVariationOn (S.phi u) (Ioc u v)).toReal := by
  let K := max P.radiusUpper 0
  have hK : 0 ≤ K := le_max_right _ _
  refine ⟨K, hK, ?_⟩
  intro D ha hb hP u v huv S hS
  have hboundOne (U : Set (ℝ × ℝ)) (h : IsBVSolution U S)
      (hp : (u, v) ∈ U) :
      (∫ t in u..v, |S.theta u t| / (t - u)) ≤
        K * (eVariationOn (S.phi u) (Ioc u v)).toReal := by
    have hlt := (h.solution.development.wedge hp).2
    have hθ := theta_div_distance_integrable h hp
    have hφ := h.scalar_deriv_integrable_on_axis_slice hp
    have hae : ∀ᵐ t ∂volume, t ∈ Ioc u v →
        |S.theta u t| / (t - u) ≤ K * |deriv (S.phi u) t| := by
      filter_upwards [h.scalar_ae_deriv_out_on_slice hp] with t hder ht
      have htU := h.solution.development.outgoing_mem hp ht.1 ht.2
      have htT : (u, t) ∈ triangle D.a D.b :=
        (mem_triangle).2 ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩
      have htT' : (u, t) ∈ triangle 0 1 := by
        simpa only [ha, hb] using htT
      have hrhi := (hP u t htT' S hS).2.2.2.2.2.2.2.2
      have hd : 0 < t - u := sub_pos.mpr ht.1
      have hr : 0 < S.r u t := h.solution.radius_pos (u, t) htU
      have hrK : S.r u t ≤ K * (t - u) :=
        hrhi.trans (mul_le_mul_of_nonneg_right
          (le_max_left P.radiusUpper 0) hd.le)
      rw [hder ht, abs_div, abs_of_pos hr]
      apply (div_le_iff₀ hd).2
      have hh := mul_le_mul_of_nonneg_right hrK
        (abs_nonneg (S.theta u t / S.r u t))
      have heq : S.r u t * |S.theta u t / S.r u t| =
          |S.theta u t| := by
        rw [abs_div, abs_of_pos hr]
        field_simp [hr.ne']
      rw [heq] at hh
      rw [abs_div, abs_of_pos hr] at hh
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hh
    have hle := integral_mono_ae hθ (hφ.abs.const_mul K)
      ((ae_restrict_iff' measurableSet_Ioc).mpr hae)
    rw [← intervalIntegral.integral_of_le hlt.le] at hle
    have hright : (∫ t in Ioc u v, K * |deriv (S.phi u) t|) =
        K * (∫ t in u..v, |deriv (S.phi u) t|) := by
      rw [← intervalIntegral.integral_of_le hlt.le,
        intervalIntegral.integral_const_mul]
    rw [hright] at hle
    exact hle.trans (mul_le_mul_of_nonneg_left
      (scalar_deriv_integral_le_variation h hp) hK)
  rcases hS with rfl | rfl
  · exact hboundOne D.U₁ D.h₁ (D.hT huv).1
  · exact hboundOne D.U₂ D.h₂ (D.hT huv).2

end ChristodoulouBV.Uniqueness

end
