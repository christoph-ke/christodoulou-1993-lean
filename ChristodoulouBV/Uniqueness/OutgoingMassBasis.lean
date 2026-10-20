module

public import ChristodoulouBV.Uniqueness.ThetaGood
public import ChristodoulouBV.Uniqueness.GammaFinite
public import ChristodoulouBV.Uniqueness.ExpansionCoeffIntegrals
import ChristodoulouBV.ForMathlib.BoundedVariation.SliceFacts

/-!
# Outgoing mass comparison at the regular axis

The outgoing scalar amplitude has an integrable reciprocal-distance weight.
This supplies the endpoint and weighted Hardy ingredients of the outgoing
mass comparison without a separate singular assumption.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The outgoing kernel in Christodoulou's estimate (3.16). -/
noncomputable def ComparisonData.I (D : ComparisonData) (u v : ℝ) : ℝ :=
  ∫ t in u..v, (|D.S₁.theta u t| + |D.S₂.theta u t|)

/-- A single radius bound controls the reciprocal-distance scalar amplitude
by the absolute scalar derivative almost everywhere on every outgoing ray. -/
theorem theta_div_distance_le_scalar_deriv_ae
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u v, (u, v) ∈ U →
      ∀ᵐ t ∂volume, t ∈ Ioc u v →
        |S.theta u t| / (t - u) ≤ K * |deriv (S.phi u) t| := by
  obtain ⟨K₀, hK₀, _⟩ := h.exists_uniform_radius_upper
  let K := max K₀ 0
  have hK : 0 ≤ K := le_max_right _ _
  refine ⟨K, hK, ?_⟩
  intro u v huv
  filter_upwards [h.scalar_ae_deriv_out_on_slice huv] with t hder ht
  have htU := h.solution.development.outgoing_mem huv ht.1 ht.2
  have hd : 0 < t - u := sub_pos.mpr ht.1
  have hr : 0 < S.r u t := h.solution.radius_pos (u, t) htU
  have hrK : S.r u t ≤ K * (t - u) :=
    (h.radius_upper_of_lam_le hK₀ htU).trans
      (mul_le_mul_of_nonneg_right (le_max_left K₀ 0) hd.le)
  rw [hder ht, abs_div, abs_of_pos hr]
  apply (div_le_iff₀ hd).2
  have hh := mul_le_mul_of_nonneg_right hrK (abs_nonneg (S.theta u t / S.r u t))
  have heq : S.r u t * |S.theta u t / S.r u t| = |S.theta u t| := by
    rw [abs_div, abs_of_pos hr]
    field_simp [hr.ne']
  rw [heq] at hh
  rw [abs_div, abs_of_pos hr] at hh
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hh

/-- The reciprocal-distance outgoing scalar amplitude is integrable up to
the excluded regular axis. -/
theorem theta_div_distance_integrable
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    IntegrableOn (fun t => |S.theta u t| / (t - u)) (Ioc u v) volume := by
  obtain ⟨K, hK, hbound⟩ := theta_div_distance_le_scalar_deriv_ae h
  have hBV : BoundedVariationOn (S.theta u) {t | (u, t) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.item5.choose_spec.1 u)
  have hsub : Ioc u v ⊆ {t | (u, t) ∈ U} := by
    intro t ht
    exact h.solution.development.outgoing_mem huv ht.1 ht.2
  have hmeas : AEStronglyMeasurable
      (fun t => |S.theta u t| / (t - u)) (volume.restrict (Ioc u v)) := by
    have hθ : AEStronglyMeasurable (S.theta u) (volume.restrict (Ioc u v)) := by
      have hi := hBV.measurable_indicator_Ioc hsub
      have heq : EqOn ((Ioc u v).indicator (S.theta u)) (S.theta u) (Ioc u v) := by
        intro t ht
        exact Set.indicator_of_mem ht _
      exact hi.aestronglyMeasurable.congr
        (ae_restrict_of_forall_mem measurableSet_Ioc heq)
    have hd : AEStronglyMeasurable (fun t : ℝ => t - u)
        (volume.restrict (Ioc u v)) := (measurable_id.sub_const u).aestronglyMeasurable
    exact hθ.norm.div₀ hd
  apply Integrable.mono' ((h.scalar_deriv_integrable_on_axis_slice huv).abs.const_mul K)
    hmeas
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hbound u v huv] with t ht htI
  have hpos : 0 ≤ |S.theta u t| / (t - u) :=
    div_nonneg (abs_nonneg _) (sub_nonneg.mpr htI.1.le)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hpos] using ht htI

/-- The reciprocal-distance outgoing scalar integral is bounded uniformly by
one BV-dependent multiple of the scalar variation. -/
theorem theta_div_distance_integral_le_variation
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u v, (huv : (u, v) ∈ U) →
      (∫ t in u..v, |S.theta u t| / (t - u)) ≤
        K * (eVariationOn (S.phi u) (Ioc u v)).toReal := by
  obtain ⟨K, hK, hbound⟩ := theta_div_distance_le_scalar_deriv_ae h
  refine ⟨K, hK, ?_⟩
  intro u v huv
  have hlt := (h.solution.development.wedge huv).2
  have hθ := theta_div_distance_integrable h huv
  have hφ := h.scalar_deriv_integrable_on_axis_slice huv
  have hle := integral_mono_ae hθ (hφ.abs.const_mul K)
    ((ae_restrict_iff' measurableSet_Ioc).mpr (hbound u v huv))
  rw [← intervalIntegral.integral_of_le hlt.le] at hle
  have hright : (∫ t in Ioc u v, K * |deriv (S.phi u) t|) =
      K * (∫ t in u..v, |deriv (S.phi u) t|) := by
    rw [← intervalIntegral.integral_of_le hlt.le,
      intervalIntegral.integral_const_mul]
  rw [hright] at hle
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
  exact hle.trans (mul_le_mul_of_nonneg_left hderivBound hK)

/-- The same weighted scalar amplitude is integrable up to the open top
when every interior point of the characteristic lies in the BV domain. -/
theorem theta_div_distance_integrable_to_top
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u b : ℝ} (hub : u < b)
    (hpoint : ∀ v, u < v → v < b → (u, v) ∈ U) :
    IntegrableOn (fun t => |S.theta u t| / (t - u)) (Ioc u b) volume := by
  obtain ⟨K, hK, hbound⟩ := theta_div_distance_integral_le_variation h
  have hfinite : eVariationOn (S.phi u) {t | (u, t) ∈ U} ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (h.item3_variation.choose_spec.1 u)
  let W := (eVariationOn (S.phi u) {t | (u, t) ∈ U}).toReal
  let v : ℕ → ℝ := fun n => b - (b - u) / ((n : ℝ) + 1)
  have hv0 : v 0 = u := by simp [v]
  have hvi (n : ℕ) (hn : 0 < n) : u < v n ∧ v n < b := by
    have hd : 0 < b - u := sub_pos.mpr hub
    have hnreal : 1 < ((n : ℝ) + 1) := by exact_mod_cast Nat.lt_add_one_iff.mpr hn
    constructor
    · dsimp [v]
      have hdiv : (b - u) / ((n : ℝ) + 1) < b - u := by
        apply (div_lt_iff₀ (by positivity)).2
        nlinarith
      linarith
    · dsimp [v]
      have hp : 0 < (b - u) / ((n : ℝ) + 1) := by positivity
      linarith
  have hv : Tendsto v atTop (𝓝 b) := by
    have hz : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Tendsto (fun _ : ℕ => b - u) atTop (𝓝 (b - u)) :=
      tendsto_const_nhds
    have hh := (tendsto_const_nhds (x := b)).sub (hc.mul hz)
    simpa only [v, div_eq_mul_inv, one_mul, mul_zero, sub_zero] using hh
  apply integrableOn_Ioc_of_intervalIntegral_norm_bounded_right
    (l := (atTop : Filter ℕ)) (a := u) (b := v)
    (I := K * W)
  · intro n
    by_cases hn : n = 0
    · subst n
      simpa only [hv0, Set.Ioc_self, Measure.restrict_empty] using
        (integrableOn_empty : IntegrableOn
          (fun t => |S.theta u t| / (t - u)) (∅ : Set ℝ) volume)
    · exact theta_div_distance_integrable h
        (hpoint (v n) (hvi n (Nat.pos_of_ne_zero hn)).1
          (hvi n (Nat.pos_of_ne_zero hn)).2)
  · exact hv
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    have hnpos : 0 < n := hn
    have hnv := hvi n hnpos
    have hpt := hpoint (v n) hnv.1 hnv.2
    have hsub : Ioc u (v n) ⊆ {t | (u, t) ∈ U} := by
      intro t ht
      exact h.solution.development.outgoing_mem hpt ht.1 ht.2
    have hvar : (eVariationOn (S.phi u) (Ioc u (v n))).toReal ≤ W :=
      ENNReal.toReal_mono hfinite (eVariationOn.mono (S.phi u) hsub)
    have hle := hbound u (v n) hpt
    have hnonneg : ∀ t ∈ Ioc u (v n),
        0 ≤ |S.theta u t| / (t - u) := by
      intro t ht
      exact div_nonneg (abs_nonneg _) (sub_nonneg.mpr ht.1.le)
    have hnorm : (∫ t in Ioc u (v n),
        ‖|S.theta u t| / (t - u)‖) =
        ∫ t in Ioc u (v n), |S.theta u t| / (t - u) := by
      apply integral_congr_ae
      exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (hnonneg t ht)])
    rw [intervalIntegral.integral_of_le hnv.1.le] at hle
    rw [hnorm]
    exact hle.trans (mul_le_mul_of_nonneg_left hvar hK)

/-- On a finite half-open interval, an integrable reciprocal-distance
weight makes the unweighted function integrable too. -/
theorem integrableOn_of_div_sub_integrable
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hw : IntegrableOn (fun t => f t / (t - a)) (Ioc a b) volume) :
    IntegrableOn f (Ioc a b) volume := by
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioc a b)) := by
    have hprod := hw.aestronglyMeasurable.mul
      ((measurable_id.sub_const a).aestronglyMeasurable :
        AEStronglyMeasurable (fun t : ℝ => t - a) (volume.restrict (Ioc a b)))
    apply hprod.congr
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro t ht
    have hd : t - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt ht.1)
    dsimp
    field_simp [hd]
  have hD : 0 ≤ b - a := sub_nonneg.mpr hab.le
  apply Integrable.mono' (hw.abs.const_mul (b - a)) hmeas
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards with t ht
  have hd : 0 < t - a := sub_pos.mpr ht.1
  have hle : t - a ≤ b - a := sub_le_sub_right ht.2 a
  have hf : |f t| = (t - a) * |f t / (t - a)| := by
    rw [abs_div, abs_of_pos hd]
    field_simp [hd.ne']
  rw [Real.norm_eq_abs]
  rw [hf]
  exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)

/-- The two outgoing scalar amplitudes have an integrable
reciprocal-distance weight on every axis-to-point ray. -/
theorem ComparisonData.theta_sum_div_distance_integrable
    (D : ComparisonData) {u v : ℝ}
    (huv : (u, v) ∈ triangle D.a D.b) :
    IntegrableOn (fun t =>
      (|D.S₁.theta u t| + |D.S₂.theta u t|) / (t - u))
      (Ioc u v) volume := by
  have hp := D.hT huv
  have h₁ := theta_div_distance_integrable D.h₁ hp.1
  have h₂ := theta_div_distance_integrable D.h₂ hp.2
  have heq : (fun t => |D.S₁.theta u t| / (t - u)) +
      (fun t => |D.S₂.theta u t| / (t - u)) =
      (fun t => (|D.S₁.theta u t| + |D.S₂.theta u t|) / (t - u)) := by
    funext t
    simp only [Pi.add_apply, add_div]
  rw [← heq]
  exact h₁.add h₂

/-- The outgoing Hardy endpoint vanishes, and the two scalar amplitudes
have a finite reciprocal-distance integral on the full half-open ray. -/
theorem ComparisonData.hardy_out_endpoint
    (D : ComparisonData) {u v : ℝ}
    (huv : (u, v) ∈ triangle D.a D.b) :
    Tendsto (fun t => D.I u t / (t - u)) (𝓝[>] u) (𝓝 0) ∧
      IntegrableOn (fun t =>
        (|D.S₁.theta u t| + |D.S₂.theta u t|) / (t - u))
        (Ioc u v) volume := by
  let f : ℝ → ℝ := fun t => |D.S₁.theta u t| + |D.S₂.theta u t|
  let g : ℝ → ℝ := fun t => if t = u then 0 else f t
  have hlt : u < v := huv.2.1
  have hw := D.theta_sum_div_distance_integrable huv
  have hf : IntegrableOn f (Ioc u v) volume :=
    integrableOn_of_div_sub_integrable hlt hw
  have heq : EqOn f g (Ioc u v) := by
    intro t ht
    simp [g, ne_of_gt ht.1]
  have hfi : IntervalIntegrable g volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le).2
      (hf.congr_fun heq measurableSet_Ioc)
  have hweq : EqOn (fun t => f t / (t - u))
      (fun t => g t / (t - u)) (Ioc u v) := by
    intro t ht
    change f t / (t - u) = g t / (t - u)
    rw [heq ht]
  have hwi : IntervalIntegrable (fun t => g t / (t - u)) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le).2
      (hw.congr_fun hweq measurableSet_Ioc)
  have hnonneg : ∀ t ∈ Icc u v, 0 ≤ g t := by
    intro t ht
    by_cases htu : t = u
    · simp [g, htu]
    · have hut : u < t := lt_of_le_of_ne ht.1 (by
        intro htu'; exact htu htu'.symm)
      rw [← heq ⟨hut, ht.2⟩]
      change 0 ≤ |D.S₁.theta u t| + |D.S₂.theta u t|
      exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hend := intervalIntegral.tendsto_integral_div_sub_right
    hlt hfi hwi hnonneg
  have hcongr : ∀ᶠ t in 𝓝[>] u,
      D.I u t / (t - u) = (∫ s in u..t, g s) / (t - u) := by
    filter_upwards [Ioc_mem_nhdsGT hlt] with t ht
    have hinner : (∫ s in u..t, f s) = ∫ s in u..t, g s := by
      apply intervalIntegral.integral_congr_Ioo_of_le ht.1.le
      intro s hs
      exact heq ⟨hs.1, hs.2.le.trans ht.2⟩
    exact congrArg (fun x : ℝ => x / (t - u)) hinner
  constructor
  · exact hend.congr' (hcongr.mono fun _ he => he.symm)
  · exact hw

/-- The outgoing Hardy endpoint condition and reciprocal-distance
integrability on the complete characteristic up to the open comparison top. -/
theorem ComparisonData.hardy_out_endpoint_full
    (D : ComparisonData) {u : ℝ} (hu : u ∈ Ico D.a D.b) :
    Tendsto (fun t => D.I u t / (t - u)) (𝓝[>] u) (𝓝 0) ∧
      IntegrableOn (fun t =>
        (|D.S₁.theta u t| + |D.S₂.theta u t|) / (t - u))
        (Ioc u D.b) volume := by
  let w := (u + D.b) / 2
  have huw : u < w ∧ w < D.b := by
    dsimp [w]
    constructor <;> linarith [hu.2]
  have hmid : (u, w) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨hu.1, huw.1, huw.2⟩
  have hlim := (D.hardy_out_endpoint hmid).1
  have h₁ := theta_div_distance_integrable_to_top D.h₁ hu.2
    (by
      intro v huv hvb
      exact (D.hT ((mem_triangle).2 ⟨hu.1, huv, hvb⟩)).1)
  have h₂ := theta_div_distance_integrable_to_top D.h₂ hu.2
    (by
      intro v huv hvb
      exact (D.hT ((mem_triangle).2 ⟨hu.1, huv, hvb⟩)).2)
  constructor
  · exact hlim
  · have heq : (fun t => |D.S₁.theta u t| / (t - u) +
        |D.S₂.theta u t| / (t - u)) =
        (fun t => (|D.S₁.theta u t| + |D.S₂.theta u t|) /
          (t - u)) := by
      funext t
      simp only [add_div]
    rw [← heq]
    exact h₁.add h₂

/-- Real-integral Hardy bound for a nonnegative density on a half-open ray;
the value at the excluded initial endpoint is unrestricted. -/
theorem hardy_integral_le_weighted_Ioc
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : IntegrableOn f (Ioc a b) volume)
    (hw : IntegrableOn (fun t => f t / (t - a)) (Ioc a b) volume)
    (hfn : ∀ t ∈ Ioc a b, 0 ≤ f t) :
    (∫ t in Ioc a b, (∫ s in a..t, f s) / (t - a) ^ 2) ≤
      ∫ t in Ioc a b, f t / (t - a) := by
  have hG := hardy_integrable_Ioc_nonneg hab hf hw hfn
  have hGn : 0 ≤ᵐ[volume.restrict (Ioc a b)]
      (fun t => (∫ s in a..t, f s) / (t - a) ^ 2) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro t ht
    have hinner : 0 ≤ ∫ s in a..t, f s := by
      apply intervalIntegral.integral_nonneg_of_ae_restrict ht.1.le
      rw [← restrict_Ioo_eq_restrict_Icc]
      apply ae_restrict_of_forall_mem measurableSet_Ioo
      intro s hs
      exact hfn s ⟨hs.1, hs.2.le.trans ht.2⟩
    exact div_nonneg hinner (sq_nonneg _)
  have hWn : 0 ≤ᵐ[volume.restrict (Ioc a b)]
      (fun t => f t / (t - a)) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro t ht
    exact div_nonneg (hfn t ht) (sub_nonneg.mpr ht.1.le)
  have hGI : 0 ≤ ∫ t in Ioc a b, (∫ s in a..t, f s) / (t - a) ^ 2 :=
    integral_nonneg_of_ae hGn
  have hWI : 0 ≤ ∫ t in Ioc a b, f t / (t - a) :=
    integral_nonneg_of_ae hWn
  have hWI' : 0 ≤ ∫ t in a..b, f t / (t - a) := by
    rw [intervalIntegral.integral_of_le hab.le]
    exact hWI
  have hlin := hardy_lintegral_le_weighted_Ioc hab hf hw hfn
  have hreal := ofReal_integral_eq_lintegral_ofReal hG hGn
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (hreal.trans_le hlin)
  rw [ENNReal.toReal_ofReal hGI, ENNReal.toReal_ofReal hWI'] at hle
  rw [intervalIntegral.integral_of_le hab.le] at hle
  exact hle

/-- The outgoing `I` Hardy kernel is integrable, and its weighted integral
is bounded by the reciprocal-distance scalar integral. -/
theorem ComparisonData.I_hardy_le
    (D : ComparisonData) {u v : ℝ}
    (huv : (u, v) ∈ triangle D.a D.b) :
    IntegrableOn (fun t => D.I u t / (t - u) ^ 2) (Ioc u v) volume ∧
      (∫ t in u..v, D.I u t / (t - u) ^ 2) ≤
        ∫ t in u..v,
          (|D.S₁.theta u t| + |D.S₂.theta u t|) / (t - u) := by
  let f : ℝ → ℝ := fun t => |D.S₁.theta u t| + |D.S₂.theta u t|
  have hlt := huv.2.1
  have hw := D.theta_sum_div_distance_integrable huv
  have hf : IntegrableOn f (Ioc u v) volume :=
    integrableOn_of_div_sub_integrable hlt hw
  have hfn : ∀ t ∈ Ioc u v, 0 ≤ f t := by
    intro t ht
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hG := hardy_integrable_Ioc_nonneg hlt hf hw hfn
  have hle := hardy_integral_le_weighted_Ioc hlt hf hw hfn
  have hI : (fun t => (∫ s in u..t, f s) / (t - u) ^ 2) =
      (fun t => D.I u t / (t - u) ^ 2) := by
    rfl
  rw [hI] at hG hle
  constructor
  · exact hG
  · rw [intervalIntegral.integral_of_le hlt.le,
      intervalIntegral.integral_of_le hlt.le]
    exact hle

/-- A fixed radius constant bounds the Hardy integral of `I` by the
outgoing scalar variation. It is chosen before the smallness parameter and
works on every ray and every compact comparison top. -/
theorem ComparisonData.I_hardy_le_small_variation
    (D : ComparisonData) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, 0 ≤ ε →
      (∀ u v, (u, v) ∈ triangle D.a D.b →
        (eVariationOn (D.S₁.phi u) (Ioc u v)).toReal ≤ ε ∧
        (eVariationOn (D.S₂.phi u) (Ioc u v)).toReal ≤ ε) →
      ∀ u v, (huv : (u, v) ∈ triangle D.a D.b) →
        (∫ t in u..v, D.I u t / (t - u) ^ 2) ≤ K * ε := by
  obtain ⟨K₁, hK₁, h₁⟩ := theta_div_distance_integral_le_variation D.h₁
  obtain ⟨K₂, hK₂, h₂⟩ := theta_div_distance_integral_le_variation D.h₂
  refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, ?_⟩
  intro ε hε hsmall u v huv
  have hp := D.hT huv
  have hlt := huv.2.1
  have hi₁ : IntervalIntegrable
      (fun t => |D.S₁.theta u t| / (t - u)) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le).2
      (theta_div_distance_integrable D.h₁ hp.1)
  have hi₂ : IntervalIntegrable
      (fun t => |D.S₂.theta u t| / (t - u)) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le).2
      (theta_div_distance_integrable D.h₂ hp.2)
  have hsum : (∫ t in u..v,
      (|D.S₁.theta u t| + |D.S₂.theta u t|) / (t - u)) =
      (∫ t in u..v, |D.S₁.theta u t| / (t - u)) +
        (∫ t in u..v, |D.S₂.theta u t| / (t - u)) := by
    rw [← intervalIntegral.integral_add hi₁ hi₂]
    congr 1
    funext t
    simp only [add_div]
  have hsmallPair := hsmall u v huv
  calc
    (∫ t in u..v, D.I u t / (t - u) ^ 2) ≤
        ∫ t in u..v,
          (|D.S₁.theta u t| + |D.S₂.theta u t|) / (t - u) :=
      (D.I_hardy_le huv).2
    _ = (∫ t in u..v, |D.S₁.theta u t| / (t - u)) +
          (∫ t in u..v, |D.S₂.theta u t| / (t - u)) := hsum
    _ ≤ K₁ * (eVariationOn (D.S₁.phi u) (Ioc u v)).toReal +
          K₂ * (eVariationOn (D.S₂.phi u) (Ioc u v)).toReal :=
      add_le_add (h₁ u v hp.1) (h₂ u v hp.2)
    _ ≤ (K₁ + K₂) * ε := by
      nlinarith only [hsmallPair.1, hsmallPair.2, hK₁, hK₂]

/-- The nonnegative coefficient of the outgoing mass difference, appearing
with a minus sign in the linear equation. -/
noncomputable def ComparisonData.outgoingMassDamping
    (D : ComparisonData) (u t : ℝ) : ℝ :=
  D.S₂.theta u t ^ 2 / (D.S₂.lam u t * D.S₁.r u t)

/-- The three forcing terms of the outgoing Hawking mass difference equation. -/
noncomputable def ComparisonData.outgoingMassForcing
    (D : ComparisonData) (u t : ℝ) : ℝ :=
  (1 / 2) * (D.S₂.theta u t ^ 2 / D.S₂.lam u t) *
      (IsBVSolution.mu D.S₂ u t *
        ((D.S₁.r u t - D.S₂.r u t) / D.S₁.r u t) -
        ((1 - IsBVSolution.mu D.S₁ u t) / D.S₁.lam u t) *
          (D.S₁.lam u t - D.S₂.lam u t)) +
    (1 / 2) * ((1 - IsBVSolution.mu D.S₁ u t) / D.S₁.lam u t) *
      (D.S₁.theta u t + D.S₂.theta u t) *
        (D.S₁.theta u t - D.S₂.theta u t)

private theorem mass_out_difference_algebra
    {m₁ m₂ r₁ r₂ l₁ l₂ q₁ q₂ : ℝ}
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0) :
    (1 - 2 * m₁ / r₁) * q₁ ^ 2 / (2 * l₁) -
      (1 - 2 * m₂ / r₂) * q₂ ^ 2 / (2 * l₂) =
    -(q₂ ^ 2 / (l₂ * r₁)) * (m₁ - m₂) +
      (1 / 2) * (q₂ ^ 2 / l₂) *
        ((2 * m₂ / r₂) * ((r₁ - r₂) / r₁) -
          ((1 - 2 * m₁ / r₁) / l₁) * (l₁ - l₂)) +
      (1 / 2) * ((1 - 2 * m₁ / r₁) / l₁) *
        (q₁ + q₂) * (q₁ - q₂) := by
  field_simp [hr₁, hr₂, hl₁, hl₂]
  ring

/-- The outgoing mass-density difference is a linear equation in the mass
difference with a nonpositive homogeneous term. This holds at every actual
point; the differential equation holds at the a.e. primitive derivative. -/
theorem ComparisonData.mass_out_difference_linear
    (D : ComparisonData) {u t : ℝ}
    (hut : (u, t) ∈ triangle D.a D.b) :
    IsBVSolution.massV D.S₁ u t - IsBVSolution.massV D.S₂ u t =
      -D.outgoingMassDamping u t * (D.S₁.m u t - D.S₂.m u t) +
        D.outgoingMassForcing u t := by
  have hp := D.hT hut
  have hr₁ := (D.h₁.solution.radius_pos (u, t) hp.1).ne'
  have hr₂ := (D.h₂.solution.radius_pos (u, t) hp.2).ne'
  have hl₁ := (D.h₁.solution.lam_pos (u, t) hp.1).ne'
  have hl₂ := (D.h₂.solution.lam_pos (u, t) hp.2).ne'
  simpa only [IsBVSolution.massV, IsBVSolution.mu,
    ComparisonData.outgoingMassDamping, ComparisonData.outgoingMassForcing,
    add_assoc]
    using (mass_out_difference_algebra (m₁ := D.S₁.m u t)
      (m₂ := D.S₂.m u t) (r₁ := D.S₁.r u t) (r₂ := D.S₂.r u t)
      (l₁ := D.S₁.lam u t) (l₂ := D.S₂.lam u t)
      (q₁ := D.S₁.theta u t) (q₂ := D.S₂.theta u t)
      hr₁ hr₂ hl₁ hl₂)

/-- The outgoing mass damping is nonnegative throughout the comparison
triangle, so its contribution to the linear equation is nonpositive. -/
theorem ComparisonData.outgoingMassDamping_nonneg
    (D : ComparisonData) {u t : ℝ}
    (hut : (u, t) ∈ triangle D.a D.b) :
    0 ≤ D.outgoingMassDamping u t := by
  have hp := D.hT hut
  exact div_nonneg (sq_nonneg _)
    (mul_nonneg (D.h₂.solution.lam_pos (u, t) hp.2).le
      (D.h₁.solution.radius_pos (u, t) hp.1).le)

/-- The axis-zero outgoing mass difference satisfies the full linear
integral equation. All terms are integrated together, as supplied by the
two frozen mass primitives. -/
theorem ComparisonData.mass_out_difference_integral
    (D : ComparisonData) {u v : ℝ}
    (huv : (u, v) ∈ triangle D.a D.b) :
    D.S₁.m u v - D.S₂.m u v =
      ∫ t in u..v,
        (-D.outgoingMassDamping u t *
            (D.S₁.m u t - D.S₂.m u t) +
          D.outgoingMassForcing u t) := by
  have hp := D.hT huv
  have hlt := huv.2.1
  have h₁ := D.h₁.mass_out_integral_from_axis hp.1
  have h₂ := D.h₂.mass_out_integral_from_axis hp.2
  have hi₁ : IntervalIntegrable (IsBVSolution.massV D.S₁ u) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le).2
      (D.h₁.mass_density_integrable_on_axis_slice hp.1)
  have hi₂ : IntervalIntegrable (IsBVSolution.massV D.S₂ u) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le).2
      (D.h₂.mass_density_integrable_on_axis_slice hp.2)
  calc
    D.S₁.m u v - D.S₂.m u v =
        (∫ t in u..v, IsBVSolution.massV D.S₁ u t) -
          (∫ t in u..v, IsBVSolution.massV D.S₂ u t) := by rw [h₁, h₂]
    _ = ∫ t in u..v,
        (IsBVSolution.massV D.S₁ u t -
          IsBVSolution.massV D.S₂ u t) :=
      (intervalIntegral.integral_sub hi₁ hi₂).symm
    _ = ∫ t in u..v,
        (-D.outgoingMassDamping u t *
            (D.S₁.m u t - D.S₂.m u t) +
          D.outgoingMassForcing u t) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hlt.le
      intro t ht
      exact D.mass_out_difference_linear
        ((mem_triangle).2 ⟨huv.1, ht.1, ht.2.trans huv.2.2⟩)

end ChristodoulouBV.Uniqueness

end
