module

public import ChristodoulouBV.Uniqueness.IncomingMassEquation
public import ChristodoulouBV.ForMathlib.MeasureTheory.HardyIntegral
import ChristodoulouBV.ForMathlib.BoundedVariation.SliceFacts
import Mathlib.Tactic.FunProp

/-!
# Incoming scalar kernel and terminal Hardy endpoint

The full comparison triangle gives each half-open incoming characteristic.
The weighted scalar kernel is integrable there because `ζ/r` is the scalar
derivative almost everywhere and the radius is at most linear in axis distance.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- The incoming scalar amplitude kernel in the paper's equation (3.17). -/
noncomputable def IStar (D : ComparisonData) (u v : ℝ) : ℝ :=
  ∫ s in u..v, |D.S₁.zeta s v| + |D.S₂.zeta s v|

private theorem abs_div_distance_le
    {z r d K : ℝ} (hr : 0 < r) (hd : 0 < d)
    (hrK : r ≤ K * d) : |z| / d ≤ K * |z / r| := by
  have hK : 0 ≤ K := by nlinarith [hrK]
  have hratio : r / d ≤ K := (div_le_iff₀ hd).2 (by
    simpa only [mul_comm] using hrK)
  have hnonneg : 0 ≤ |z| / r := div_nonneg (abs_nonneg _) hr.le
  calc
    |z| / d = (r / d) * (|z| / r) := by field_simp
    _ ≤ K * (|z| / r) := mul_le_mul_of_nonneg_right hratio hnonneg
    _ = K * |z / r| := by rw [abs_div, abs_of_pos hr]

/-- The reciprocal-terminal-distance weighted incoming `ζ` amplitude is
integrable on every full half-open ray of the triangle. -/
theorem zeta_abs_div_distance_integrable
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b u v : ℝ} (hT : triangle a b ⊆ U)
    (huv : (u, v) ∈ triangle a b) :
    IntegrableOn (fun s => |S.zeta s v| / (v - s)) (Ioc u v) volume := by
  obtain ⟨K₀, _, hrad⟩ := h.exists_uniform_radius_upper
  let K := max K₀ 0
  have hK : 0 ≤ K := le_max_right _ _
  have haccess := IsBVSolution.incoming_axis_access_of_triangle hT huv
  have hderiv : IntegrableOn (deriv (fun s => S.phi s v)) (Ioo u v) volume := by
    change Integrable _ (volume.restrict (Ioo u v))
    rw [restrict_Ioo_eq_restrict_Ioc]
    exact h.scalar_deriv_integrable_on_incoming_axis_slice huv.2.1 haccess
  have hBV : BoundedVariationOn (fun s => S.zeta s v) {s | (s, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item5.choose_spec.2 v)
  have hsub : Ioo u v ⊆ {s | (s, v) ∈ U} := by
    intro s hs
    exact haccess s ⟨hs.1.le, hs.2⟩
  have hmeasZ : Measurable ((Ioo u v).indicator (fun s => S.zeta s v)) :=
    hBV.measurable_indicator_Ioo hsub
  have hmeas : AEStronglyMeasurable
      (fun s => |S.zeta s v| / (v - s)) (volume.restrict (Ioo u v)) := by
    have hmeas' : Measurable (fun s =>
        |(Ioo u v).indicator (fun t => S.zeta t v) s| / (v - s)) :=
      hmeasZ.abs.div (by fun_prop)
    apply hmeas'.aestronglyMeasurable.congr
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => by
      simp only [Set.indicator_of_mem hs])
  have hbound : ∀ᵐ s ∂volume.restrict (Ioo u v),
      ‖|S.zeta s v| / (v - s)‖ ≤
        K * |deriv (fun t => S.phi t v) s| := by
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    filter_upwards [h.scalar_ae_deriv_in_on_half_open_access
      huv.2.1 haccess] with s hφ hs
    have hsco : s ∈ Ico u v := ⟨hs.1.le, hs.2⟩
    have hsU := haccess s hsco
    have hr := h.solution.radius_pos (s, v) hsU
    have hd : 0 < v - s := sub_pos.mpr hs.2
    have hrK : S.r s v ≤ K * (v - s) :=
      (hrad s v hsU).trans
        (mul_le_mul_of_nonneg_right (le_max_left K₀ 0) hd.le)
    have hh := abs_div_distance_le hr hd hrK (z := S.zeta s v)
    rw [← hφ hsco] at hh
    have hnonneg : 0 ≤ |S.zeta s v| / (v - s) :=
      div_nonneg (abs_nonneg _) hd.le
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hh
  have hi : Integrable (fun s => |S.zeta s v| / (v - s))
      (volume.restrict (Ioo u v)) :=
    Integrable.mono' (hderiv.abs.const_mul K) hmeas hbound
  change Integrable _ (volume.restrict (Ioc u v))
  rw [← restrict_Ioo_eq_restrict_Ioc]
  exact hi

/-- Weighted integrability also supplies ordinary integrability of the
incoming amplitude on the half-open ray. -/
theorem zeta_abs_integrable
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b u v : ℝ} (hT : triangle a b ⊆ U)
    (huv : (u, v) ∈ triangle a b) :
    IntegrableOn (fun s => |S.zeta s v|) (Ioc u v) volume := by
  have hw := zeta_abs_div_distance_integrable h hT huv
  have hwi : IntervalIntegrable (fun s => |S.zeta s v| / (v - s))
      volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).2 hw
  have hprod : IntervalIntegrable
      (fun s => (|S.zeta s v| / (v - s)) * (v - s)) volume u v :=
    hwi.mul_continuousOn (by fun_prop)
  have hprodOn :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).1 hprod
  apply hprodOn.congr_fun_ae
  apply (ae_restrict_iff' measurableSet_Ioc).mpr
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ v := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with s hne hs
  have hvs : v - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  field_simp

/-- On each incoming ray, the terminal Hardy primitive has a vanishing
distance quotient and its reciprocal-distance density is integrable. -/
theorem hardy_in_endpoint (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    IntervalIntegrable
      (fun s => (|D.S₁.zeta s v| + |D.S₂.zeta s v|) / (v - s))
      volume u v ∧
    Tendsto (fun w => IStar D w v / (v - w)) (𝓝[<] v) (𝓝 0) := by
  let f : ℝ → ℝ := fun s => |D.S₁.zeta s v| + |D.S₂.zeta s v|
  have hT₁ : triangle D.a D.b ⊆ D.U₁ := fun p hp => (D.hT hp).1
  have hT₂ : triangle D.a D.b ⊆ D.U₂ := fun p hp => (D.hT hp).2
  have hw₁ := zeta_abs_div_distance_integrable D.h₁ hT₁ huv
  have hw₂ := zeta_abs_div_distance_integrable D.h₂ hT₂ huv
  have hf₁ := zeta_abs_integrable D.h₁ hT₁ huv
  have hf₂ := zeta_abs_integrable D.h₂ hT₂ huv
  have hf : IntervalIntegrable f volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).2
      (hf₁.add hf₂)
  have hw : IntervalIntegrable (fun s => f s / (v - s)) volume u v := by
    have hwi₁ : IntervalIntegrable
        (fun s => |D.S₁.zeta s v| / (v - s)) volume u v :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).2 hw₁
    have hwi₂ : IntervalIntegrable
        (fun s => |D.S₂.zeta s v| / (v - s)) volume u v :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).2 hw₂
    convert hwi₁.add hwi₂ using 1
    funext s
    dsimp [f]
    ring
  have hfn : ∀ s ∈ Icc u v, 0 ≤ f s :=
    fun s _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
  refine ⟨hw, ?_⟩
  exact intervalIntegral.tendsto_integral_div_sub_left huv.2.1 hf hw hfn

/-- The scalar derivative on a full incoming ray is controlled by its
variation on that ray, retaining the local smallness parameter. -/
theorem scalar_deriv_integral_le_local_variation_in
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b u v L : ℝ} (hT : triangle a b ⊆ U)
    (huv : (u, v) ∈ triangle a b)
    (hvar : (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ L) :
    (∫ s in u..v, |deriv (fun t => S.phi t v) s|) ≤ L := by
  let t : ℕ → ℝ := fun n => v - (v - u) / ((n : ℝ) + 1)
  have htu (n : ℕ) : u ≤ t n := by
    dsimp [t]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hone : (v - u) / ((n : ℝ) + 1) ≤ v - u := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [mul_nonneg (sub_pos.mpr huv.2.1).le hn]
    linarith
  have htv (n : ℕ) : t n < v := by
    dsimp [t]
    have hd : 0 < (v - u) / ((n : ℝ) + 1) :=
      div_pos (sub_pos.mpr huv.2.1) (by positivity)
    linarith
  have ht : Tendsto t atTop (𝓝 v) := by
    have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hconst : Tendsto (fun _ : ℕ => v - u) atTop (𝓝 (v - u)) :=
      tendsto_const_nhds
    have hh := (tendsto_const_nhds (x := v)).sub (hconst.mul hzero)
    simpa only [t, div_eq_mul_inv, one_mul, mul_zero, sub_zero] using hh
  have haccess : ∀ s ∈ Ico u v, (s, v) ∈ U := by
    intro s hs
    exact hT ((mem_triangle).2 ⟨huv.1.trans hs.1, hs.2, huv.2.2⟩)
  have hInt : IntegrableOn (fun s => |deriv (fun t => S.phi t v) s|)
      (Ioc u v) volume :=
    (h.scalar_deriv_integrable_on_incoming_axis_slice huv.2.1 haccess).abs
  have hlim := (aecover_Ioc_of_Ioc (μ := volume)
    (tendsto_const_nhds (x := u)) ht).integral_tendsto_of_countably_generated hInt
  have hbound : ∀ n : ℕ,
      (∫ s in Ioc u (t n), |deriv (fun y => S.phi y v) s|
        ∂volume.restrict (Ioc u v)) ≤ L := by
    intro n
    have hsubset : Icc u (t n) ⊆ Ico u v := by
      intro s hs
      exact ⟨hs.1, hs.2.trans_lt (htv n)⟩
    have hcoU : Ico u v ⊆ {s | (s, v) ∈ U} := by
      intro s hs
      exact haccess s hs
    have hfinite : eVariationOn (fun s => S.phi s v) (Ico u v) < ⊤ :=
      lt_of_le_of_lt
        ((eVariationOn.mono (fun s => S.phi s v) hcoU).trans
          (h.item3_variation.choose_spec.2 v))
        ENNReal.ofReal_lt_top
    have hBV : BoundedVariationOn (fun s => S.phi s v) (Icc u (t n)) :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        ((eVariationOn.mono (fun s => S.phi s v) hsubset).trans
          ((eVariationOn.mono (fun s => S.phi s v) hcoU).trans
            (h.item3_variation.choose_spec.2 v)))
    have hlocal : (eVariationOn (fun s => S.phi s v) (Icc u (t n))).toReal ≤ L :=
      (ENNReal.toReal_mono hfinite.ne
        (eVariationOn.mono (fun s => S.phi s v) hsubset)).trans hvar
    have hderiv := hBV.integral_abs_deriv_le_eVariationOn (htu n)
    have hsubI : Ioc u (t n) ⊆ Ioc u v := by
      intro s hs
      exact ⟨hs.1, hs.2.trans (htv n).le⟩
    have heq : (∫ s in Ioc u (t n), |deriv (fun y => S.phi y v) s|
        ∂volume.restrict (Ioc u v)) =
        ∫ s in u..t n, |deriv (fun y => S.phi y v) s| := by
      rw [Measure.restrict_restrict measurableSet_Ioc]
      rw [Set.inter_eq_self_of_subset_left hsubI]
      exact (intervalIntegral.integral_of_le (htu n)).symm
    rw [heq]
    exact hderiv.trans hlocal
  have hresult := le_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  rw [intervalIntegral.integral_of_le huv.2.1.le]
  exact hresult

/-- The terminal-distance weighted incoming amplitude retains the local
incoming variation bound, with a geometric constant fixed globally. -/
theorem zeta_abs_div_distance_integral_le_local_variation
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b : ℝ} (hT : triangle a b ⊆ U) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u v L, (u, v) ∈ triangle a b →
      (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ L →
      (∫ s in u..v, |S.zeta s v| / (v - s)) ≤ K * L := by
  obtain ⟨K₀, _, hrad⟩ := h.exists_uniform_radius_upper
  let K := max K₀ 0
  have hK : 0 ≤ K := le_max_right _ _
  refine ⟨K, hK, ?_⟩
  intro u v L huv hvar
  have hInt := zeta_abs_div_distance_integrable h hT huv
  have hInt' : IntegrableOn (fun s => |S.zeta s v| / (v - s))
      (Ioo u v) volume := by
    change Integrable _ (volume.restrict (Ioo u v))
    rw [restrict_Ioo_eq_restrict_Ioc]
    exact hInt
  have haccess := IsBVSolution.incoming_axis_access_of_triangle hT huv
  have hderiv : IntegrableOn (fun s => K * |deriv (fun t => S.phi t v) s|)
      (Ioo u v) volume := by
    change Integrable _ (volume.restrict (Ioo u v))
    rw [restrict_Ioo_eq_restrict_Ioc]
    exact ((h.scalar_deriv_integrable_on_incoming_axis_slice huv.2.1 haccess).abs).const_mul K
  have hae : (fun s => |S.zeta s v| / (v - s)) ≤ᵐ[volume.restrict (Ioo u v)]
      (fun s => K * |deriv (fun t => S.phi t v) s|) := by
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    filter_upwards [h.scalar_ae_deriv_in_on_half_open_access
      huv.2.1 haccess] with s hφ hs
    have hsco : s ∈ Ico u v := ⟨hs.1.le, hs.2⟩
    have hsU := haccess s hsco
    have hr := h.solution.radius_pos (s, v) hsU
    have hd : 0 < v - s := sub_pos.mpr hsco.2
    have hrK : S.r s v ≤ K * (v - s) :=
      (hrad s v hsU).trans
        (mul_le_mul_of_nonneg_right (le_max_left K₀ 0) hd.le)
    have hh := abs_div_distance_le hr hd hrK (z := S.zeta s v)
    rw [← hφ hsco] at hh
    exact hh
  have hle := integral_mono_ae hInt' hderiv hae
  change (∫ s in Ioo u v, |S.zeta s v| / (v - s)) ≤
    (∫ s in Ioo u v, K * |deriv (fun t => S.phi t v) s|) at hle
  rw [restrict_Ioo_eq_restrict_Ioc] at hle
  rw [← intervalIntegral.integral_of_le huv.2.1.le,
    ← intervalIntegral.integral_of_le huv.2.1.le,
    intervalIntegral.integral_const_mul] at hle
  exact hle.trans (mul_le_mul_of_nonneg_left
    (scalar_deriv_integral_le_local_variation_in h hT huv hvar) hK)

end ChristodoulouBV.Uniqueness

end
