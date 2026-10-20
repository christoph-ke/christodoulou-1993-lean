module

public import ChristodoulouBV.Uniqueness.RadiusScalar
public import ChristodoulouBV.ForMathlib.MeasureTheory.HardyIntegral

/-!
# Weighted mass densities near the regular axis

Uniform BV control of the scalar and the axis radius bounds the mass density
by the scalar derivative after division by the axis distance.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

private theorem mass_density_distance_le
    {mu theta lam r d c K B : ℝ}
    (hmu : 0 ≤ mu ∧ mu < 1) (hLam : c ≤ lam) (hc : 0 < c)
    (hr : 0 < r) (hd : 0 < d) (hrK : r ≤ K * d)
    (hθ : |theta| ≤ B) :
    (1 - mu) * theta ^ 2 / (2 * lam * d) ≤
      (K * B / c) * |theta / r| := by
  have hB : 0 ≤ B := (abs_nonneg _).trans hθ
  have hK : 0 ≤ K := by nlinarith [hrK, hr, hd]
  have hgap : 0 ≤ 1 - mu ∧ 1 - mu ≤ 1 := by constructor <;> linarith [hmu.1, hmu.2]
  have hstep : (1 - mu) * |theta| * r * c ≤ B * K * d * lam := by
    calc
      (1 - mu) * |theta| * r * c ≤ |theta| * r * c := by
        have hh := mul_le_mul_of_nonneg_right hgap.2
          (mul_nonneg (mul_nonneg (abs_nonneg theta) hr.le) hc.le)
        nlinarith only [hh]
      _ ≤ B * r * c := by gcongr
      _ ≤ B * (K * d) * c := by gcongr
      _ ≤ B * (K * d) * lam := by gcongr
      _ = B * K * d * lam := by ring
  rw [abs_div, abs_of_pos hr, ← sq_abs theta]
  have hLamPos : 0 < lam := hc.trans_le hLam
  have hden : 0 < 2 * lam * d := by positivity
  apply (div_le_iff₀ hden).2
  have hfactor : (1 - mu) * |theta| * r * c * |theta| ≤
      B * K * d * lam * |theta| :=
    mul_le_mul_of_nonneg_right hstep (abs_nonneg _)
  have hRHS : 0 ≤ B * K * d * lam * |theta| := by positivity
  field_simp [hr.ne', hc.ne']
  nlinarith only [hfactor, hRHS]

/-- On each outgoing axis-to-point ray, the reciprocal-distance weighted
mass density is bounded almost everywhere by one uniform multiple of the
absolute scalar derivative. The constant depends only on this BV solution. -/
theorem massV_div_distance_le_scalar_deriv_ae
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v, (u, v) ∈ U →
      ∀ᵐ t ∂volume, t ∈ Ioc u v →
        IsBVSolution.massV S u t / (t - u) ≤
          C * |deriv (S.phi u) t| := by
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  obtain ⟨K₀, _, hrK₀⟩ := h.exists_uniform_radius_upper
  let K := max K₀ 0
  have hrK : ∀ u v, (u, v) ∈ U → S.r u v ≤ K * (v - u) := by
    intro u v huv
    have hd : 0 ≤ v - u := sub_nonneg.mpr
      (h.solution.development.wedge huv).2.le
    exact (hrK₀ u v huv).trans
      (mul_le_mul_of_nonneg_right (le_max_left K₀ 0) hd)
  let B := max h.item5.choose 0
  have hB : 0 ≤ B := le_max_right _ _
  have hK : 0 ≤ K := le_max_right _ _
  refine ⟨K * B / c, div_nonneg (mul_nonneg hK hB) hc.le, ?_⟩
  intro u v huv
  filter_upwards [h.scalar_ae_deriv_out_on_slice huv] with t hder ht
  have hut : (u, t) ∈ U :=
    h.solution.development.outgoing_mem huv ht.1 ht.2
  have hmu := h.mass_ratio_bounds hut
  have htheta := h.theta_abs_le_global_variation hut
  have hr := h.solution.radius_pos (u, t) hut
  have hd : 0 < t - u := sub_pos.mpr ht.1
  have hbound := mass_density_distance_le hmu (hlam (u, t) hut) hc hr hd
    (hrK u t hut) htheta
  rw [hder ht]
  convert hbound using 1
  simp only [IsBVSolution.massV, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The outgoing mass density divided by the axis distance is integrable on
every full axis-to-point slice. -/
theorem massV_div_distance_integrable
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    IntegrableOn (fun t => IsBVSolution.massV S u t / (t - u))
      (Ioc u v) volume := by
  obtain ⟨C, hC, hbound⟩ := massV_div_distance_le_scalar_deriv_ae h
  have hmass := h.mass_density_integrable_on_axis_slice huv
  have hderiv := h.scalar_deriv_integrable_on_axis_slice huv
  have hmeas : AEStronglyMeasurable
      (fun t => IsBVSolution.massV S u t / (t - u))
      (volume.restrict (Ioc u v)) := by
    have hrec : Measurable (fun t : ℝ => (t - u)⁻¹) := by fun_prop
    have hprod : AEStronglyMeasurable
        (fun t => IsBVSolution.massV S u t * (t - u)⁻¹)
        (volume.restrict (Ioc u v)) := by
      convert hmass.aestronglyMeasurable.mul hrec.aestronglyMeasurable using 1
    simpa only [div_eq_mul_inv] using hprod
  apply Integrable.mono' (hderiv.abs.const_mul C) hmeas
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hbound u v huv] with t ht htI
  have htU : (u, t) ∈ U :=
    h.solution.development.outgoing_mem huv htI.1 htI.2
  have hnonneg : 0 ≤ IsBVSolution.massV S u t / (t - u) :=
    div_nonneg (h.mass_density_nonneg h.solution.development htU)
      (sub_nonneg.mpr htI.1.le)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using ht htI

/-- The full outgoing derivative integral is bounded by the uniform BV
variation, including the improper axis endpoint. -/
theorem scalar_deriv_integral_le_variation_out
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    (∫ t in u..v, |deriv (S.phi u) t|) ≤
      max h.item3_variation.choose 0 := by
  have huvlt := (h.solution.development.wedge huv).2
  let B : ℝ := max h.item3_variation.choose 0
  have hB : 0 ≤ B := le_max_right _ _
  let a : ℕ → ℝ := fun n => u + (v - u) / ((n : ℝ) + 1)
  have hau (n : ℕ) : u < a n := by
    dsimp [a]
    have hp : 0 < ((n : ℝ) + 1) := by positivity
    have hd : 0 < (v - u) / ((n : ℝ) + 1) :=
      div_pos (sub_pos.mpr huvlt) hp
    linarith
  have hav (n : ℕ) : a n ≤ v := by
    dsimp [a]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hp : 1 ≤ ((n : ℝ) + 1) := by linarith
    have hone : (v - u) / ((n : ℝ) + 1) ≤ v - u := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [mul_nonneg (sub_pos.mpr huvlt).le hn]
    linarith
  have ha : Tendsto a atTop (𝓝 u) := by
    have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hconst : Tendsto (fun _ : ℕ => v - u) atTop (𝓝 (v - u)) :=
      tendsto_const_nhds
    have hh := (tendsto_const_nhds (x := u)).add (hconst.mul hzero)
    simpa only [a, div_eq_mul_inv, one_mul, mul_zero, add_zero] using hh
  have hInt : IntegrableOn (fun t => |deriv (S.phi u) t|)
      (Ioc u v) volume :=
    (h.scalar_deriv_integrable_on_axis_slice huv).abs
  have hlim := (aecover_Ioc_of_Ioc (μ := volume)
    ha (tendsto_const_nhds (x := v))).integral_tendsto_of_countably_generated hInt
  have hbound : ∀ n : ℕ,
      (∫ t in Ioc (a n) v, |deriv (S.phi u) t| ∂volume.restrict (Ioc u v)) ≤
        B := by
    intro n
    have hsubset : Icc (a n) v ⊆ {t | (u, t) ∈ U} := by
      intro t ht
      exact h.solution.development.outgoing_mem huv
        ((hau n).trans_le ht.1) ht.2
    have hBV : BoundedVariationOn (S.phi u) (Icc (a n) v) :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        ((eVariationOn.mono (S.phi u) hsubset).trans
          (h.item3_variation.choose_spec.1 u))
    have hvar : (eVariationOn (S.phi u) (Icc (a n) v)).toReal ≤ B :=
      ENNReal.toReal_le_of_le_ofReal hB
        ((eVariationOn.mono (S.phi u) hsubset).trans
          ((h.item3_variation.choose_spec.1 u).trans
            (ENNReal.ofReal_le_ofReal (le_max_left _ _))))
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
  have hresult := le_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  rw [intervalIntegral.integral_of_le huvlt.le]
  exact hresult

/-- A single BV-dependent constant bounds every outgoing reciprocal-distance
mass-density integral. It is uniform in both the outgoing coordinate and the
compact upper endpoint. -/
theorem massV_div_distance_integral_uniform
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u v, (u, v) ∈ U →
      (∫ t in u..v, IsBVSolution.massV S u t / (t - u)) ≤ M := by
  obtain ⟨C, hC, hbound⟩ := massV_div_distance_le_scalar_deriv_ae h
  let V : ℝ := max h.item3_variation.choose 0
  have hV : 0 ≤ V := le_max_right _ _
  refine ⟨C * V, mul_nonneg hC hV, ?_⟩
  intro u v huv
  have huvlt := (h.solution.development.wedge huv).2
  have hmass := massV_div_distance_integrable h huv
  have hderiv := (h.scalar_deriv_integrable_on_axis_slice huv).abs.const_mul C
  have hae : (fun t => IsBVSolution.massV S u t / (t - u)) ≤ᵐ[
      volume.restrict (Ioc u v)]
      (fun t => C * |deriv (S.phi u) t|) := by
    exact (ae_restrict_iff' measurableSet_Ioc).mpr (hbound u v huv)
  have hle := integral_mono_ae hmass hderiv hae
  rw [← intervalIntegral.integral_of_le huvlt.le] at hle
  have hright : (∫ t in Ioc u v, C * |deriv (S.phi u) t|) =
      C * (∫ t in u..v, |deriv (S.phi u) t|) := by
    rw [← intervalIntegral.integral_of_le huvlt.le,
      intervalIntegral.integral_const_mul]
  rw [hright] at hle
  have hscalar := scalar_deriv_integral_le_variation_out h huv
  exact hle.trans (mul_le_mul_of_nonneg_left hscalar hC)

/-- On a full augmented triangle, the terminal-distance weighted incoming
mass density is bounded almost everywhere by a uniform multiple of the
absolute incoming scalar derivative. -/
theorem negMassIn_div_distance_le_scalar_deriv_ae
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b : ℝ} (hT : triangle a b ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v, (u, v) ∈ triangle a b →
      ∀ᵐ s ∂volume, s ∈ Ico u v →
        -IsBVSolution.massInDensity S s v / (v - s) ≤
          C * |deriv (fun t => S.phi t v) s| := by
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  obtain ⟨K₀, _, hrK₀⟩ := h.exists_uniform_radius_upper
  let K := max K₀ 0
  have hrK : ∀ u v, (u, v) ∈ U → S.r u v ≤ K * (v - u) := by
    intro u v huv
    have hd : 0 ≤ v - u := sub_nonneg.mpr
      (h.solution.development.wedge huv).2.le
    exact (hrK₀ u v huv).trans
      (mul_le_mul_of_nonneg_right (le_max_left K₀ 0) hd)
  let B := max h.item5.choose 0
  have hB : 0 ≤ B := le_max_right _ _
  have hK : 0 ≤ K := le_max_right _ _
  refine ⟨K * B / c, div_nonneg (mul_nonneg hK hB) hc.le, ?_⟩
  intro u v huv
  have haccess : ∀ s ∈ Ico u v, (s, v) ∈ U := by
    intro s hs
    exact hT ((mem_triangle).2
      ⟨huv.1.trans hs.1, hs.2, huv.2.2⟩)
  filter_upwards [h.scalar_ae_deriv_in_on_half_open_access huv.2.1 haccess]
    with s hder hs
  have hst : (s, v) ∈ triangle a b :=
    (mem_triangle).2 ⟨huv.1.trans hs.1, hs.2, huv.2.2⟩
  have hsU : (s, v) ∈ U := hT hst
  have hmu := h.mass_ratio_bounds hsU
  have hzeta := h.zeta_abs_le_global_variation_of_triangle hT hst
  have hr := h.solution.radius_pos (s, v) hsU
  have hd : 0 < v - s := sub_pos.mpr hs.2
  have hnu : c ≤ -S.nu s v := by
    have hh := h.nu_le_neg_lower hc hlam hsU
    linarith
  have hbound := mass_density_distance_le hmu hnu hc hr hd
    (hrK s v hsU) hzeta
  rw [hder hs]
  convert hbound using 1
  simp only [IsBVSolution.massInDensity, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The terminal-distance weighted incoming mass density is integrable on
each full half-open incoming ray of the augmented triangle. -/
theorem negMassIn_div_distance_integrable
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b u v : ℝ} (hT : triangle a b ⊆ U)
    (huv : (u, v) ∈ triangle a b) :
    IntegrableOn (fun s => -IsBVSolution.massInDensity S s v / (v - s))
      (Ico u v) volume := by
  obtain ⟨C, hC, hbound⟩ := negMassIn_div_distance_le_scalar_deriv_ae h hT
  have haccess : ∀ s ∈ Ico u v, (s, v) ∈ U := by
    intro s hs
    exact hT ((mem_triangle).2
      ⟨huv.1.trans hs.1, hs.2, huv.2.2⟩)
  have hmass : IntegrableOn (fun s => IsBVSolution.massInDensity S s v)
      (Ico u v) volume := by
    change Integrable (fun s => IsBVSolution.massInDensity S s v)
      (volume.restrict (Ico u v))
    rw [restrict_Ico_eq_restrict_Ioc]
    exact h.massInDensity_integrable_of_half_open_access huv.2.1 haccess
  have hderiv : IntegrableOn (deriv (fun s => S.phi s v))
      (Ico u v) volume := by
    change Integrable (deriv (fun s => S.phi s v))
      (volume.restrict (Ico u v))
    rw [restrict_Ico_eq_restrict_Ioc]
    exact h.scalar_deriv_integrable_on_incoming_axis_slice huv.2.1 haccess
  have hmeas : AEStronglyMeasurable
      (fun s => -IsBVSolution.massInDensity S s v / (v - s))
      (volume.restrict (Ico u v)) := by
    have hrec : Measurable (fun s : ℝ => (v - s)⁻¹) := by fun_prop
    have hprod : AEStronglyMeasurable
        (fun s => -(IsBVSolution.massInDensity S s v) * (v - s)⁻¹)
        (volume.restrict (Ico u v)) := by
      convert hmass.neg.aestronglyMeasurable.mul hrec.aestronglyMeasurable using 1
    simpa only [div_eq_mul_inv] using hprod
  apply Integrable.mono' (hderiv.abs.const_mul C) hmeas
  exact (ae_restrict_iff' measurableSet_Ico).mpr (by
    filter_upwards [hbound u v huv] with s hs hsI
    have hsU := haccess s hsI
    have hnonpos := h.massInDensity_nonpos hsU
    have hnonneg : 0 ≤ -IsBVSolution.massInDensity S s v / (v - s) :=
      div_nonneg (by linarith) (sub_nonneg.mpr hsI.2.le)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hs hsI)

/-- The full incoming scalar derivative integral is bounded by the uniform
BV variation on every complete terminal characteristic of a triangle. -/
theorem scalar_deriv_integral_le_variation_in
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b u v : ℝ} (hT : triangle a b ⊆ U)
    (huv : (u, v) ∈ triangle a b) :
    (∫ s in u..v, |deriv (fun t => S.phi t v) s|) ≤
      max h.item3_variation.choose 0 := by
  let B : ℝ := max h.item3_variation.choose 0
  have hB : 0 ≤ B := le_max_right _ _
  let t : ℕ → ℝ := fun n => v - (v - u) / ((n : ℝ) + 1)
  have htu (n : ℕ) : u ≤ t n := by
    dsimp [t]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hp : 1 ≤ ((n : ℝ) + 1) := by linarith
    have hone : (v - u) / ((n : ℝ) + 1) ≤ v - u := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [mul_nonneg (sub_pos.mpr huv.2.1).le hn]
    linarith
  have htv (n : ℕ) : t n < v := by
    dsimp [t]
    have hp : 0 < ((n : ℝ) + 1) := by positivity
    have hd : 0 < (v - u) / ((n : ℝ) + 1) :=
      div_pos (sub_pos.mpr huv.2.1) hp
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
    exact hT ((mem_triangle).2
      ⟨huv.1.trans hs.1, hs.2, huv.2.2⟩)
  have hInt : IntegrableOn (fun s => |deriv (fun t => S.phi t v) s|)
      (Ioc u v) volume :=
    (h.scalar_deriv_integrable_on_incoming_axis_slice huv.2.1 haccess).abs
  have hlim := (aecover_Ioc_of_Ioc (μ := volume)
    (tendsto_const_nhds (x := u)) ht).integral_tendsto_of_countably_generated hInt
  have hbound : ∀ n : ℕ,
      (∫ s in Ioc u (t n), |deriv (fun y => S.phi y v) s|
        ∂volume.restrict (Ioc u v)) ≤ B := by
    intro n
    have hsubset : Icc u (t n) ⊆ {s | (s, v) ∈ U} := by
      intro s hs
      exact haccess s ⟨hs.1, hs.2.trans_lt (htv n)⟩
    have hBV : BoundedVariationOn (fun s => S.phi s v) (Icc u (t n)) :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        ((eVariationOn.mono (fun s => S.phi s v) hsubset).trans
          (h.item3_variation.choose_spec.2 v))
    have hvar : (eVariationOn (fun s => S.phi s v) (Icc u (t n))).toReal ≤ B :=
      ENNReal.toReal_le_of_le_ofReal hB
        ((eVariationOn.mono (fun s => S.phi s v) hsubset).trans
          ((h.item3_variation.choose_spec.2 v).trans
            (ENNReal.ofReal_le_ofReal (le_max_left _ _))))
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
    exact hderiv.trans hvar
  have hresult := le_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  rw [intervalIntegral.integral_of_le huv.2.1.le]
  exact hresult

/-- One constant bounds the terminal-distance weighted incoming mass density
on every complete incoming ray of a full comparison triangle. -/
theorem negMassIn_div_distance_integral_uniform
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {a b : ℝ} (hT : triangle a b ⊆ U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u v, (u, v) ∈ triangle a b →
      (∫ s in u..v, -IsBVSolution.massInDensity S s v / (v - s)) ≤ M := by
  obtain ⟨C, hC, hbound⟩ := negMassIn_div_distance_le_scalar_deriv_ae h hT
  let V : ℝ := max h.item3_variation.choose 0
  have hV : 0 ≤ V := le_max_right _ _
  refine ⟨C * V, mul_nonneg hC hV, ?_⟩
  intro u v huv
  have hin := negMassIn_div_distance_integrable h hT huv
  have haccess : ∀ s ∈ Ico u v, (s, v) ∈ U := by
    intro s hs
    exact hT ((mem_triangle).2
      ⟨huv.1.trans hs.1, hs.2, huv.2.2⟩)
  have hderiv : IntegrableOn (deriv (fun s => S.phi s v))
      (Ico u v) volume := by
    change Integrable (deriv (fun s => S.phi s v))
      (volume.restrict (Ico u v))
    rw [restrict_Ico_eq_restrict_Ioc]
    exact h.scalar_deriv_integrable_on_incoming_axis_slice huv.2.1 haccess
  have hae : (fun s => -IsBVSolution.massInDensity S s v / (v - s)) ≤ᵐ[
      volume.restrict (Ico u v)]
      (fun s => C * |deriv (fun t => S.phi t v) s|) :=
    (ae_restrict_iff' measurableSet_Ico).mpr (hbound u v huv)
  have hle := integral_mono_ae hin (hderiv.abs.const_mul C) hae
  change (∫ s : ℝ, -IsBVSolution.massInDensity S s v / (v - s)
      ∂volume.restrict (Ico u v)) ≤
      (∫ s : ℝ, C * |deriv (fun t => S.phi t v) s|
        ∂volume.restrict (Ico u v)) at hle
  rw [restrict_Ico_eq_restrict_Ioc] at hle
  change (∫ s in Ioc u v, -IsBVSolution.massInDensity S s v / (v - s)) ≤
      (∫ s in Ioc u v, C * |deriv (fun t => S.phi t v) s|) at hle
  rw [← intervalIntegral.integral_of_le huv.2.1.le] at hle
  have hright : (∫ s in Ioc u v, C * |deriv (fun t => S.phi t v) s|) =
      C * (∫ s in u..v, |deriv (fun t => S.phi t v) s|) := by
    rw [← intervalIntegral.integral_of_le huv.2.1.le,
      intervalIntegral.integral_const_mul]
  rw [hright] at hle
  exact hle.trans (mul_le_mul_of_nonneg_left
    (scalar_deriv_integral_le_variation_in h hT huv) hC)

end ChristodoulouBV.Uniqueness

end
