module

public import ChristodoulouBV.Uniqueness.OutgoingMassBasis

/-!
# Outgoing mass transport and Hardy comparison

The damping in the mass difference equation is controlled by the same
reciprocal-distance scalar amplitude used in the Hardy step.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The outgoing radius is measurable on each full half-open characteristic.
Its axis-integral representation gives a continuous representative there. -/
theorem outgoing_radius_aestronglyMeasurable
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    AEStronglyMeasurable (S.r u) (volume.restrict (Ioc u v)) := by
  have hlt := (h.solution.development.wedge huv).2
  have hLam := h.lam_integrable_outgoing_axis huv
  have hAC := hLam.absolutelyContinuousOnInterval_intervalIntegral
    (c := u) (by simp)
  have hcont : ContinuousOn (fun t => ∫ s in u..t, S.lam u s)
      (Ioc u v) :=
    hAC.continuousOn.mono (by
      rw [uIcc_of_le hlt.le]
      exact Ioc_subset_Icc_self)
  have hR : AEStronglyMeasurable
      (fun t => ∫ s in u..t, S.lam u s) (volume.restrict (Ioc u v)) :=
    hcont.aestronglyMeasurable measurableSet_Ioc
  apply hR.congr
  apply ae_restrict_of_forall_mem measurableSet_Ioc
  intro t ht
  exact (h.radius_eq_outgoing_axis_integral
    (h.solution.development.outgoing_mem huv ht.1 ht.2)).symm

/-- The nonnegative damping coefficient is integrable all the way to the
axis. Its bound uses the ordinary BV scalar derivative, not a singular
Hardy assumption. -/
theorem ComparisonData.outgoingMassDamping_integrable
    (D : ComparisonData) {u v : ℝ}
    (huv : (u, v) ∈ triangle D.a D.b) :
    IntegrableOn (D.outgoingMassDamping u) (Ioc u v) volume := by
  have hp := D.hT huv
  have hlt := huv.2.1
  obtain ⟨clam, hclam, hlam⟩ := D.h₂.lam_bounded_below
  obtain ⟨cR, _, hcR, hrad⟩ := D.h₁.exists_uniform_radius_bounds
  let B := max D.h₂.item5.choose 0
  have hB : 0 ≤ B := le_max_right _ _
  have hθbound : ∀ t ∈ Ioc u v, |D.S₂.theta u t| ≤ B := by
    intro t ht
    have htU := D.h₂.solution.development.outgoing_mem hp.2 ht.1 ht.2
    exact D.h₂.theta_abs_le_global_variation htU
  have hθBV : BoundedVariationOn (D.S₂.theta u)
      {t | (u, t) ∈ D.U₂} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (D.h₂.item5.choose_spec.1 u)
  have hθsub : Ioc u v ⊆ {t | (u, t) ∈ D.U₂} := by
    intro t ht
    exact D.h₂.solution.development.outgoing_mem hp.2 ht.1 ht.2
  have hθmeas : AEStronglyMeasurable (D.S₂.theta u)
      (volume.restrict (Ioc u v)) := by
    have hi := hθBV.measurable_indicator_Ioc hθsub
    apply hi.aestronglyMeasurable.congr
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro t ht
    exact Set.indicator_of_mem ht _
  have hlamMeas : AEStronglyMeasurable (D.S₂.lam u)
      (volume.restrict (Ioc u v)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le).1
      (D.h₂.lam_integrable_outgoing_axis hp.2)).aestronglyMeasurable
  have hrMeas := outgoing_radius_aestronglyMeasurable D.h₁ hp.1
  have hmeas : AEStronglyMeasurable (D.outgoingMassDamping u)
      (volume.restrict (Ioc u v)) := by
    exact (hθmeas.pow 2).div₀ (hlamMeas.mul hrMeas)
  have hweight := theta_div_distance_integrable D.h₂ hp.2
  let C := B / (clam * cR)
  have hC : 0 ≤ C := div_nonneg hB (mul_nonneg hclam.le hcR.le)
  apply Integrable.mono' (hweight.const_mul C) hmeas
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards with t ht
  have htT : (u, t) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩
  have htU := D.hT htT
  have hd : 0 < t - u := sub_pos.mpr ht.1
  have hr : 0 < D.S₁.r u t := D.h₁.solution.radius_pos (u, t) htU.1
  have hl : 0 < D.S₂.lam u t := D.h₂.solution.lam_pos (u, t) htU.2
  have hden : 0 < D.S₂.lam u t * D.S₁.r u t := mul_pos hl hr
  have hbase : 0 < clam * cR * (t - u) := by positivity
  have hdenlo : clam * cR * (t - u) ≤
      D.S₂.lam u t * D.S₁.r u t := by
    calc
      clam * cR * (t - u) = clam * (cR * (t - u)) := by ring
      _ ≤ clam * D.S₁.r u t :=
        mul_le_mul_of_nonneg_left (hrad u t htU.1).1 hclam.le
      _ ≤ D.S₂.lam u t * D.S₁.r u t :=
        mul_le_mul_of_nonneg_right (hlam (u, t) htU.2) hr.le
  have hnum : D.S₂.theta u t ^ 2 ≤ B * |D.S₂.theta u t| := by
    calc
      D.S₂.theta u t ^ 2 = |D.S₂.theta u t| * |D.S₂.theta u t| := by
        rw [← sq_abs]
        ring
      _ ≤ B * |D.S₂.theta u t| :=
        mul_le_mul_of_nonneg_right (hθbound t ht) (abs_nonneg _)
  have hk : D.outgoingMassDamping u t ≤
      C * (|D.S₂.theta u t| / (t - u)) := by
    change D.S₂.theta u t ^ 2 /
      (D.S₂.lam u t * D.S₁.r u t) ≤ _
    calc
      D.S₂.theta u t ^ 2 /
          (D.S₂.lam u t * D.S₁.r u t) ≤
          (B * |D.S₂.theta u t|) /
            (D.S₂.lam u t * D.S₁.r u t) :=
        div_le_div_of_nonneg_right hnum hden.le
      _ ≤ (B * |D.S₂.theta u t|) / (clam * cR * (t - u)) :=
        div_le_div_of_nonneg_left
          (mul_nonneg hB (abs_nonneg _)) hbase hdenlo
      _ = C * (|D.S₂.theta u t| / (t - u)) := by
        dsimp [C]
        field_simp [hclam.ne', hcR.ne', hd.ne']
  have hnonneg := D.outgoingMassDamping_nonneg htT
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hk

/-- The outgoing mass has a measurable axis-integral representative on each
half-open characteristic. -/
theorem outgoing_mass_aestronglyMeasurable
    {U : Set (ℝ × ℝ)} {S : Fields} (h : IsBVSolution U S)
    {u v : ℝ} (huv : (u, v) ∈ U) :
    AEStronglyMeasurable (S.m u) (volume.restrict (Ioc u v)) := by
  have hlt := (h.solution.development.wedge huv).2
  have hmass : IntervalIntegrable (IsBVSolution.massV S u) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le).2
      (h.mass_density_integrable_on_axis_slice huv)
  have hAC := hmass.absolutelyContinuousOnInterval_intervalIntegral
    (c := u) (by simp)
  have hcont : ContinuousOn
      (fun t => ∫ s in u..t, IsBVSolution.massV S u s) (Ioc u v) :=
    hAC.continuousOn.mono (by
      rw [uIcc_of_le hlt.le]
      exact Ioc_subset_Icc_self)
  have hM : AEStronglyMeasurable
      (fun t => ∫ s in u..t, IsBVSolution.massV S u s)
      (volume.restrict (Ioc u v)) :=
    hcont.aestronglyMeasurable measurableSet_Ioc
  apply hM.congr
  apply ae_restrict_of_forall_mem measurableSet_Ioc
  intro t ht
  exact (h.mass_out_integral_from_axis
    (h.solution.development.outgoing_mem huv ht.1 ht.2)).symm

/-- The damping times the mass difference is integrable on a complete
outgoing ray; the mass is bounded by a uniform multiple of axis distance. -/
theorem ComparisonData.outgoingMassDamping_mul_diff_integrable
    (D : ComparisonData) {u v : ℝ}
    (huv : (u, v) ∈ triangle D.a D.b) :
    IntegrableOn (fun t => D.outgoingMassDamping u t *
      (D.S₁.m u t - D.S₂.m u t)) (Ioc u v) volume := by
  have hp := D.hT huv
  obtain ⟨K₁, hK₁, _⟩ := D.h₁.exists_uniform_radius_upper
  obtain ⟨K₂, hK₂, _⟩ := D.h₂.exists_uniform_radius_upper
  have hK₁nonneg : 0 ≤ K₁ := by
    have hlam := D.h₁.solution.lam_pos (u, v) hp.1
    linarith [hK₁ (u, v) hp.1]
  have hK₂nonneg : 0 ≤ K₂ := by
    have hlam := D.h₂.solution.lam_pos (u, v) hp.2
    linarith [hK₂ (u, v) hp.2]
  let M := (K₁ + K₂) * (v - u) / 2
  have hM : 0 ≤ M := by
    dsimp [M]
    have hd : 0 ≤ v - u := sub_nonneg.mpr huv.2.1.le
    positivity
  have hk := D.outgoingMassDamping_integrable huv
  have hmeas : AEStronglyMeasurable
      (fun t => D.outgoingMassDamping u t *
        (D.S₁.m u t - D.S₂.m u t)) (volume.restrict (Ioc u v)) :=
    hk.aestronglyMeasurable.mul
      ((outgoing_mass_aestronglyMeasurable D.h₁ hp.1).sub
        (outgoing_mass_aestronglyMeasurable D.h₂ hp.2))
  apply Integrable.mono' (hk.const_mul M) hmeas
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards with t ht
  have htT : (u, t) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩
  have htU := D.hT htT
  have hd : 0 ≤ t - u := sub_nonneg.mpr ht.1.le
  have hdV : t - u ≤ v - u := sub_le_sub_right ht.2 u
  have hm₁ := D.h₁.mass_le_axis_distance hK₁ htU.1
  have hm₂ := D.h₂.mass_le_axis_distance hK₂ htU.2
  have hm₁V : D.S₁.m u t ≤ K₁ * (v - u) / 2 := by
    have hh := mul_le_mul_of_nonneg_left hdV hK₁nonneg
    linarith only [hm₁.2, hh]
  have hm₂V : D.S₂.m u t ≤ K₂ * (v - u) / 2 := by
    have hh := mul_le_mul_of_nonneg_left hdV hK₂nonneg
    linarith only [hm₂.2, hh]
  have hdiff : |D.S₁.m u t - D.S₂.m u t| ≤ M := by
    calc
      |D.S₁.m u t - D.S₂.m u t| ≤
          |D.S₁.m u t| + |D.S₂.m u t| := abs_sub _ _
      _ = D.S₁.m u t + D.S₂.m u t := by
        rw [abs_of_nonneg hm₁.1, abs_of_nonneg hm₂.1]
      _ ≤ M := by dsimp [M]; linarith only [hm₁V, hm₂V]
  have hk0 := D.outgoingMassDamping_nonneg htT
  calc
    ‖D.outgoingMassDamping u t * (D.S₁.m u t - D.S₂.m u t)‖ =
        D.outgoingMassDamping u t * |D.S₁.m u t - D.S₂.m u t| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk0]
    _ ≤ D.outgoingMassDamping u t * M :=
      mul_le_mul_of_nonneg_left hdiff hk0
    _ = M * D.outgoingMassDamping u t := by ring

/-- The outgoing forcing is integrable as the difference of the two frozen
mass densities plus the integrable damping term. -/
theorem ComparisonData.outgoingMassForcing_integrable
    (D : ComparisonData) {u v : ℝ}
    (huv : (u, v) ∈ triangle D.a D.b) :
    IntegrableOn (D.outgoingMassForcing u) (Ioc u v) volume := by
  have hp := D.hT huv
  have h₁ := D.h₁.mass_density_integrable_on_axis_slice hp.1
  have h₂ := D.h₂.mass_density_integrable_on_axis_slice hp.2
  have hprod := D.outgoingMassDamping_mul_diff_integrable huv
  have heq : EqOn
      (fun t => IsBVSolution.massV D.S₁ u t -
        IsBVSolution.massV D.S₂ u t +
        D.outgoingMassDamping u t * (D.S₁.m u t - D.S₂.m u t))
      (D.outgoingMassForcing u) (Ioc u v) := by
    intro t ht
    have htT : (u, t) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩
    have hlin := D.mass_out_difference_linear htT
    linarith only [hlin]
  exact ((h₁.sub h₂).add hprod).congr_fun heq measurableSet_Ioc

/-- Duhamel's axis-zero formula for the outgoing mass difference. The
integrating factor is at most one because the damping is nonnegative. -/
theorem ComparisonData.mass_out_difference_duhamel
    (D : ComparisonData) {u v : ℝ}
    (huv : (u, v) ∈ triangle D.a D.b) :
    D.S₁.m u v - D.S₂.m u v =
      ∫ s in u..v,
        Real.exp (-(∫ t in s..v, D.outgoingMassDamping u t)) *
          D.outgoingMassForcing u s := by
  let y : ℝ → ℝ := fun t => if t = u then 0 else
    D.S₁.m u t - D.S₂.m u t
  let k : ℝ → ℝ := fun t => -D.outgoingMassDamping u t
  let g : ℝ → ℝ := D.outgoingMassForcing u
  have hlt := huv.2.1
  have hk : IntervalIntegrable k volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le).2
      (D.outgoingMassDamping_integrable huv).neg
  have hg : IntervalIntegrable g volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le).2
      (D.outgoingMassForcing_integrable huv)
  have hky : IntervalIntegrable (fun t => k t * y t) volume u v := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le).2
    have hp := D.outgoingMassDamping_mul_diff_integrable huv
    apply hp.neg.congr_fun _ measurableSet_Ioc
    intro t ht
    change -(D.outgoingMassDamping u t *
      (D.S₁.m u t - D.S₂.m u t)) = k t * y t
    have htu : t ≠ u := ne_of_gt ht.1
    simp only [k, y, ite_eq_right htu, neg_mul]
  have hy : ∀ t ∈ Icc u v,
      y t - y u = ∫ s in u..t, (k s * y s + g s) := by
    intro t ht
    by_cases htu : t = u
    · subst t
      simp
    · have hut : u < t := lt_of_le_of_ne ht.1 (by
        intro h; exact htu h.symm)
      have htT : (u, t) ∈ triangle D.a D.b :=
        (mem_triangle).2 ⟨huv.1, hut, ht.2.trans_lt huv.2.2⟩
      have hm := D.mass_out_difference_integral htT
      have hcongr : (∫ s in u..t,
          (-D.outgoingMassDamping u s *
              (D.S₁.m u s - D.S₂.m u s) +
            D.outgoingMassForcing u s)) =
          ∫ s in u..t, (k s * y s + g s) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hut.le
        intro s hs
        have hsu : s ≠ u := ne_of_gt hs.1
        simp only [k, y, g, ite_eq_right hsu, neg_mul]
      simpa only [y, ite_eq_right htu, ite_eq_left, sub_zero] using hm.trans hcongr
  have hrepr := intervalIntegral.eq_mul_exp_add_integral_exp hlt.le
    hk hg hky hy (show v ∈ Icc u v from ⟨hlt.le, le_rfl⟩)
  have hgoal : y v =
      ∫ s in u..v,
        Real.exp (-(∫ t in s..v, D.outgoingMassDamping u t)) *
          D.outgoingMassForcing u s := by
    simpa only [y, ite_eq_left, zero_mul, zero_add, k, g,
      intervalIntegral.integral_neg] using hrepr
  simpa only [y, ite_eq_right (ne_of_gt hlt)] using hgoal

/-- Nonnegative damping bounds the outgoing mass difference by the absolute
forcing integral, with no exponential loss. -/
theorem ComparisonData.mass_out_difference_le_integral_forcing
    (D : ComparisonData) {u v : ℝ}
    (huv : (u, v) ∈ triangle D.a D.b) :
    |D.S₁.m u v - D.S₂.m u v| ≤
      ∫ s in u..v, |D.outgoingMassForcing u s| := by
  have hlt := huv.2.1
  have hk : IntervalIntegrable (D.outgoingMassDamping u) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le).2
      (D.outgoingMassDamping_integrable huv)
  have hg : IntervalIntegrable (D.outgoingMassForcing u) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlt.le).2
      (D.outgoingMassForcing_integrable huv)
  have hK : ContinuousOn
      (fun s => ∫ t in s..v, D.outgoingMassDamping u t) (uIcc u v) := by
    have hAC := hk.absolutelyContinuousOnInterval_intervalIntegral
      (c := v) (by simp)
    have hEq : (fun s => ∫ t in s..v, D.outgoingMassDamping u t) =
        (fun s => -(∫ t in v..s, D.outgoingMassDamping u t)) := by
      funext s
      exact intervalIntegral.integral_symm v s
    rw [hEq]
    exact hAC.continuousOn.neg
  have hE : ContinuousOn
      (fun s => Real.exp (-(∫ t in s..v, D.outgoingMassDamping u t)))
      (uIcc u v) := Real.continuous_exp.continuousOn.comp hK.neg
        (fun _ _ => mem_univ _)
  have hEg : IntervalIntegrable
      (fun s => Real.exp (-(∫ t in s..v, D.outgoingMassDamping u t)) *
        D.outgoingMassForcing u s) volume u v :=
    hg.continuousOn_mul hE
  have hEle : ∀ s ∈ Icc u v,
      Real.exp (-(∫ t in s..v, D.outgoingMassDamping u t)) ≤ 1 := by
    intro s hs
    have hcoeff : 0 ≤ ∫ t in s..v, D.outgoingMassDamping u t := by
      apply intervalIntegral.integral_nonneg_of_ae_restrict hs.2
      rw [← restrict_Ioo_eq_restrict_Icc]
      apply ae_restrict_of_forall_mem measurableSet_Ioo
      intro t ht
      exact D.outgoingMassDamping_nonneg
        ((mem_triangle).2 ⟨huv.1, hs.1.trans_lt ht.1,
          ht.2.trans huv.2.2⟩)
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hcoeff)
  have hpoint : ∀ s ∈ Icc u v,
      |Real.exp (-(∫ t in s..v, D.outgoingMassDamping u t)) *
          D.outgoingMassForcing u s| ≤
        |D.outgoingMassForcing u s| := by
    intro s hs
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (abs_nonneg _) (hEle s hs)
  rw [D.mass_out_difference_duhamel huv]
  calc
    |∫ s in u..v,
        Real.exp (-(∫ t in s..v, D.outgoingMassDamping u t)) *
          D.outgoingMassForcing u s| ≤
        ∫ s in u..v,
          |Real.exp (-(∫ t in s..v, D.outgoingMassDamping u t)) *
            D.outgoingMassForcing u s| :=
      intervalIntegral.abs_integral_le_integral_abs hlt.le
    _ ≤ ∫ s in u..v, |D.outgoingMassForcing u s| :=
      intervalIntegral.integral_mono_on hlt.le hEg.abs hg.abs hpoint

theorem outgoing_forcing_algebra
    {q R T θ₁ θ₂ A L C : ℝ}
    (hC : 1 ≤ C) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hq : 0 ≤ q ∧ q ≤ C ^ 2 * |θ₂|)
    (hR : 0 ≤ R ∧ R ≤ C)
    (hT : |T| ≤ 2 * C * L)
    (hθ : |θ₁ - θ₂| ≤ C * (A + L)) :
    |(1 / 2) * q * T + (1 / 2) * R * (θ₁ + θ₂) * (θ₁ - θ₂)| ≤
      2 * C ^ 3 * (A + L) * (|θ₁| + |θ₂|) := by
  have hC0 : 0 ≤ C := by linarith
  have hCsq : 0 ≤ C ^ 2 := sq_nonneg _
  have hCcube : 0 ≤ C ^ 3 := by positivity
  have hAL : 0 ≤ A + L := add_nonneg hA hL
  have hsum : 0 ≤ |θ₁| + |θ₂| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hθsum : |θ₁ + θ₂| ≤ |θ₁| + |θ₂| := abs_add_le _ _
  have hqT : q * |T| ≤ 2 * C ^ 3 * L * |θ₂| := by
    calc
      q * |T| ≤ (C ^ 2 * |θ₂|) * |T| :=
        mul_le_mul_of_nonneg_right hq.2 (abs_nonneg _)
      _ ≤ (C ^ 2 * |θ₂|) * (2 * C * L) :=
        mul_le_mul_of_nonneg_left hT (mul_nonneg hCsq (abs_nonneg _))
      _ = 2 * C ^ 3 * L * |θ₂| := by ring
  have hRθ : R * |θ₁ + θ₂| * |θ₁ - θ₂| ≤
      C ^ 2 * (A + L) * (|θ₁| + |θ₂|) := by
    calc
      R * |θ₁ + θ₂| * |θ₁ - θ₂| ≤
          C * (|θ₁| + |θ₂|) * (C * (A + L)) := by
        have h₁ := mul_le_mul_of_nonneg_right hR.2 (abs_nonneg (θ₁ + θ₂))
        have h₂ := mul_le_mul_of_nonneg_left hθsum hC0
        have h₃ := mul_le_mul_of_nonneg_right (h₁.trans h₂) (abs_nonneg (θ₁ - θ₂))
        have h₄ := mul_le_mul_of_nonneg_left hθ
          (mul_nonneg hC0 hsum)
        exact h₃.trans h₄
      _ = C ^ 2 * (A + L) * (|θ₁| + |θ₂|) := by ring
  have hLAL : L ≤ A + L := by linarith
  have hθ₂sum : |θ₂| ≤ |θ₁| + |θ₂| := by linarith [abs_nonneg θ₁]
  have hfirst : 2 * C ^ 3 * L * |θ₂| ≤
      2 * C ^ 3 * (A + L) * (|θ₁| + |θ₂|) := by
    have h₁ := mul_le_mul_of_nonneg_left hLAL
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hCcube)
    have h₂ := mul_le_mul_of_nonneg_left hθ₂sum
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hCcube) hAL)
    have h₃ := mul_le_mul_of_nonneg_right h₁ (abs_nonneg θ₂)
    nlinarith only [h₂, h₃]
  have hsecond : C ^ 2 * (A + L) * (|θ₁| + |θ₂|) ≤
      2 * C ^ 3 * (A + L) * (|θ₁| + |θ₂|) := by
    have hpower : C ^ 2 ≤ 2 * C ^ 3 := by
      nlinarith [mul_nonneg hCsq (by linarith : 0 ≤ C - 1)]
    have h₁ := mul_le_mul_of_nonneg_right hpower hAL
    exact mul_le_mul_of_nonneg_right h₁ hsum
  calc
    |(1 / 2) * q * T + (1 / 2) * R * (θ₁ + θ₂) * (θ₁ - θ₂)| ≤
        (1 / 2) * q * |T| +
          (1 / 2) * R * |θ₁ + θ₂| * |θ₁ - θ₂| := by
      simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
        abs_of_nonneg hq.1, abs_of_nonneg hR.1] using
        (abs_add_le ((1 / 2) * q * T)
          ((1 / 2) * R * (θ₁ + θ₂) * (θ₁ - θ₂)))
    _ ≤ (1 / 2) * (2 * C ^ 3 * L * |θ₂|) +
          (1 / 2) * (C ^ 2 * (A + L) * (|θ₁| + |θ₂|)) := by
      have hh := add_le_add
        (mul_le_mul_of_nonneg_left hqT
          (show 0 ≤ (1 / 2 : ℝ) by norm_num))
        (mul_le_mul_of_nonneg_left hRθ
          (show 0 ≤ (1 / 2 : ℝ) by norm_num))
      convert hh using 1; ring
    _ ≤ 2 * C ^ 3 * (A + L) * (|θ₁| + |θ₂|) := by
      linarith only [hfirst, hsecond]

/-- The outgoing quotient norm is nonnegative even when the sampled set is
unbounded; zero belongs to its defining supremum set. -/
theorem ComparisonData.A_nonneg (D : ComparisonData) (V : ℝ) :
    0 ≤ D.A V := by
  unfold ComparisonData.A ComparisonData.goodVNorm
  apply Real.sSup_nonneg'
  exact ⟨0, mem_insert 0 _, le_rfl⟩

/-- On good incoming rays, the source of the damped mass equation is bounded
by the stable quotient and expansion norms times the outgoing θ amplitude.
All constants are chosen before the final smallness parameter. -/
theorem ComparisonData.outgoingMassForcing_goodV_le
    (D : ComparisonData) (ha : D.a = 0) (hb : D.b = 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 1 ≤ C ∧
      ((∀ u v, (u, v) ∈ triangle D.a D.b →
        ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
          (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀ ∧
          (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε₀) →
        ∀ V u t, D.a < V → V < D.b →
          (u, t) ∈ triangle D.a V → t ∈ D.goodV →
          |D.outgoingMassForcing u t| ≤
            2 * C ^ 3 * (D.A V + D.L V) *
              (|D.S₁.theta u t| + |D.S₂.theta u t|)) := by
  obtain ⟨_, _, ε₀, hε₀, Cθ, hCθ, hθgood⟩ :=
    D.theta_diff_goodV_le ha hb
  obtain ⟨c₁, hc₁, hlam₁⟩ := D.h₁.lam_bounded_below
  obtain ⟨c₂, hc₂, hlam₂⟩ := D.h₂.lam_bounded_below
  obtain ⟨cR, _, hcR, hrad⟩ := D.h₁.exists_uniform_radius_bounds
  let B := max D.h₂.item5.choose 0
  let C := max 1 (max Cθ (max B (max (1 / c₁) (max (1 / c₂) (1 / cR)))))
  have hC : 1 ≤ C := le_max_left _ _
  have hCθ' : Cθ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hB : B ≤ C :=
    (le_max_left _ _).trans (le_max_right _ _) |>.trans (le_max_right _ _)
  have hc₁inv : 1 / c₁ ≤ C := by
    exact (le_max_left _ _).trans (le_max_right _ _) |>.trans
      (le_max_right _ _) |>.trans (le_max_right _ _)
  have hc₂inv : 1 / c₂ ≤ C := by
    exact (le_max_left _ _).trans (le_max_right _ _) |>.trans
      (le_max_right _ _) |>.trans (le_max_right _ _) |>.trans
      (le_max_right _ _)
  have hcRinv : 1 / cR ≤ C := by
    exact (le_max_right _ _).trans (le_max_right _ _) |>.trans
      (le_max_right _ _) |>.trans (le_max_right _ _) |>.trans
      (le_max_right _ _)
  refine ⟨ε₀, hε₀, C, hC, ?_⟩
  intro hsmall V u t haV hVb hut htG
  have hfull : (u, t) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨hut.1, hut.2.1, hut.2.2.trans hVb⟩
  have hp := D.hT hfull
  have hd : 0 < t - u := sub_pos.mpr hut.2.1
  have hr : 0 < D.S₁.r u t := D.h₁.solution.radius_pos (u, t) hp.1
  have hl₁ : 0 < D.S₁.lam u t := D.h₁.solution.lam_pos (u, t) hp.1
  have hl₂ : 0 < D.S₂.lam u t := D.h₂.solution.lam_pos (u, t) hp.2
  have hL : 0 ≤ D.L V := D.L_nonneg haV hVb
  have hA : 0 ≤ D.A V := D.A_nonneg V
  have hAL : 0 ≤ D.A V + D.L V := add_nonneg hA hL
  have hC0 : 0 ≤ C := by linarith
  have hmu₁ := D.h₁.mass_ratio_bounds hp.1
  have hmu₂ := D.h₂.mass_ratio_bounds hp.2
  change 0 ≤ IsBVSolution.mu D.S₁ u t ∧
    IsBVSolution.mu D.S₁ u t < 1 at hmu₁
  change 0 ≤ IsBVSolution.mu D.S₂ u t ∧
    IsBVSolution.mu D.S₂ u t < 1 at hmu₂
  have hR0 : 0 ≤ (1 - IsBVSolution.mu D.S₁ u t) / D.S₁.lam u t :=
    div_nonneg (by linarith [hmu₁.2]) hl₁.le
  have hRle : (1 - IsBVSolution.mu D.S₁ u t) / D.S₁.lam u t ≤ C := by
    have hgap : 1 - IsBVSolution.mu D.S₁ u t ≤ 1 := by linarith [hmu₁.1]
    have hdiv : (1 - IsBVSolution.mu D.S₁ u t) / D.S₁.lam u t ≤
        1 / D.S₁.lam u t :=
      div_le_div_of_nonneg_right hgap hl₁.le
    have hrec : 1 / D.S₁.lam u t ≤ 1 / c₁ :=
      one_div_le_one_div_of_le hc₁ (hlam₁ (u, t) hp.1)
    exact hdiv.trans (hrec.trans hc₁inv)
  have hq0 : 0 ≤ D.S₂.theta u t ^ 2 / D.S₂.lam u t :=
    div_nonneg (sq_nonneg _) hl₂.le
  have hqle : D.S₂.theta u t ^ 2 / D.S₂.lam u t ≤
      C ^ 2 * |D.S₂.theta u t| := by
    have hθB : |D.S₂.theta u t| ≤ B :=
      D.h₂.theta_abs_le_global_variation hp.2
    have hθC : |D.S₂.theta u t| ≤ C := hθB.trans hB
    have hnum : D.S₂.theta u t ^ 2 ≤ C * |D.S₂.theta u t| := by
      calc
        D.S₂.theta u t ^ 2 = |D.S₂.theta u t| * |D.S₂.theta u t| := by
          rw [← sq_abs]
          ring
        _ ≤ C * |D.S₂.theta u t| :=
          mul_le_mul_of_nonneg_right hθC (abs_nonneg _)
    have hrec : 1 / D.S₂.lam u t ≤ C :=
      (one_div_le_one_div_of_le hc₂ (hlam₂ (u, t) hp.2)).trans hc₂inv
    calc
      D.S₂.theta u t ^ 2 / D.S₂.lam u t ≤
          (C * |D.S₂.theta u t|) / D.S₂.lam u t :=
        div_le_div_of_nonneg_right hnum hl₂.le
      _ = (C * |D.S₂.theta u t|) * (1 / D.S₂.lam u t) := by ring
      _ ≤ (C * |D.S₂.theta u t|) * C :=
        mul_le_mul_of_nonneg_left hrec (mul_nonneg hC0 (abs_nonneg _))
      _ = C ^ 2 * |D.S₂.theta u t| := by ring
  have hradlo : cR * (t - u) ≤ D.S₁.r u t := (hrad u t hp.1).1
  have hΔr := D.radius_diff_le_L hVb.le hut
  have hΔlam := D.lam_diff_le_L_good hVb.le hut htG
  have hrterm : IsBVSolution.mu D.S₂ u t *
      |D.S₁.r u t - D.S₂.r u t| / D.S₁.r u t ≤ C * D.L V := by
    have hradquot : |D.S₁.r u t - D.S₂.r u t| / D.S₁.r u t ≤
        D.L V / cR := by
      have h₁ : |D.S₁.r u t - D.S₂.r u t| / D.S₁.r u t ≤
          ((t - u) * D.L V) / D.S₁.r u t :=
        div_le_div_of_nonneg_right hΔr hr.le
      have h₂ : ((t - u) * D.L V) / D.S₁.r u t ≤
          ((t - u) * D.L V) / (cR * (t - u)) :=
        div_le_div_of_nonneg_left (mul_nonneg hd.le hL)
          (mul_pos hcR hd) hradlo
      have h₃ : ((t - u) * D.L V) / (cR * (t - u)) =
          D.L V / cR := by field_simp [hcR.ne', hd.ne']
      exact h₁.trans (h₂.trans_eq h₃)
    have hrec : D.L V / cR ≤ C * D.L V := by
      have hh := mul_le_mul_of_nonneg_right hcRinv hL
      simpa only [div_eq_mul_inv, one_div, one_mul, mul_one, mul_comm] using hh
    have hm : IsBVSolution.mu D.S₂ u t ≤ 1 := hmu₂.2.le
    calc
      IsBVSolution.mu D.S₂ u t *
          |D.S₁.r u t - D.S₂.r u t| / D.S₁.r u t =
          IsBVSolution.mu D.S₂ u t *
            (|D.S₁.r u t - D.S₂.r u t| / D.S₁.r u t) := by ring
      _ ≤ 1 * (|D.S₁.r u t - D.S₂.r u t| / D.S₁.r u t) :=
        mul_le_mul_of_nonneg_right hm
          (div_nonneg (abs_nonneg _) hr.le)
      _ ≤ C * D.L V := by simpa using hradquot.trans hrec
  have hlterm : ((1 - IsBVSolution.mu D.S₁ u t) / D.S₁.lam u t) *
      |D.S₁.lam u t - D.S₂.lam u t| ≤ C * D.L V := by
    exact (mul_le_mul_of_nonneg_right hRle (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hΔlam hC0)
  have hT : |IsBVSolution.mu D.S₂ u t *
      ((D.S₁.r u t - D.S₂.r u t) / D.S₁.r u t) -
      ((1 - IsBVSolution.mu D.S₁ u t) / D.S₁.lam u t) *
        (D.S₁.lam u t - D.S₂.lam u t)| ≤ 2 * C * D.L V := by
    calc
      _ ≤ |IsBVSolution.mu D.S₂ u t *
          ((D.S₁.r u t - D.S₂.r u t) / D.S₁.r u t)| +
        |((1 - IsBVSolution.mu D.S₁ u t) / D.S₁.lam u t) *
          (D.S₁.lam u t - D.S₂.lam u t)| := abs_sub _ _
      _ ≤ C * D.L V + C * D.L V := by
        have hterm₁ : |IsBVSolution.mu D.S₂ u t *
            ((D.S₁.r u t - D.S₂.r u t) / D.S₁.r u t)| =
            IsBVSolution.mu D.S₂ u t *
              |D.S₁.r u t - D.S₂.r u t| / D.S₁.r u t := by
          rw [abs_mul, abs_div, abs_of_nonneg hmu₂.1, abs_of_pos hr]
          ring
        have hterm₂ : |((1 - IsBVSolution.mu D.S₁ u t) / D.S₁.lam u t) *
            (D.S₁.lam u t - D.S₂.lam u t)| =
            ((1 - IsBVSolution.mu D.S₁ u t) / D.S₁.lam u t) *
              |D.S₁.lam u t - D.S₂.lam u t| := by
          rw [abs_mul, abs_of_nonneg hR0]
        rw [hterm₁, hterm₂]
        exact add_le_add hrterm hlterm
      _ = 2 * C * D.L V := by ring
  have hθdiff := hθgood hsmall V u t hVb hut htG
  have hθdiffC : |D.S₁.theta u t - D.S₂.theta u t| ≤
      C * (D.A V + D.L V) :=
    hθdiff.trans (mul_le_mul_of_nonneg_right hCθ' hAL)
  have hbound := outgoing_forcing_algebra hC hA hL
    ⟨hq0, hqle⟩ ⟨hR0, hRle⟩ hT hθdiffC
  exact hbound

end ChristodoulouBV.Uniqueness

end
