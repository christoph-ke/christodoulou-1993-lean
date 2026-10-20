module

public import ChristodoulouBV.Uniqueness.GammaFinite

/-!
# The weighted radius contribution in the mass-ratio difference

The coefficient in (3.1a) controls the radius-error part of (3.9) on
outgoing characteristics. The estimate is uniform in the compact top.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

private theorem radius_term_le_coeff
    {r1 r2 d mu lam delta L c1 c2 K : ℝ}
    (hr1 : 0 < r1) (hr2 : 0 < r2) (hd : 0 < d)
    (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hmu : 0 ≤ mu ∧ mu < 1) (hlam : c2 ≤ lam)
    (hrlo : c1 * d ≤ r1) (hrhi : r2 ≤ K * d)
    (hdelta : 0 ≤ delta ∧ delta ≤ d * L) :
    mu * delta / (r1 * d) ≤
      (K / (c1 * c2) * L) * (mu * lam / ((1 - mu) * r2)) := by
  have hK : 0 ≤ K := by nlinarith [hrhi, hr2, hd]
  have hL : 0 ≤ L := by nlinarith [hdelta.1, hdelta.2, hd]
  have hlampos : 0 < lam := hc2.trans_le hlam
  have hgap : 0 < 1 - mu := by linarith [hmu.2]
  have hdeltaDiv : delta / d ≤ L := (div_le_iff₀ hd).2 (by nlinarith [hdelta.2])
  have hratio : r2 / r1 ≤ K / c1 := by
    apply (div_le_iff₀ hr1).2
    have hkc : 0 ≤ K / c1 := div_nonneg hK hc1.le
    have hh := mul_le_mul_of_nonneg_left hrlo hkc
    have heq : K / c1 * (c1 * d) = K * d := by field_simp [hc1.ne']
    rw [heq] at hh
    exact hrhi.trans hh
  have hgapOver : (1 - mu) / lam ≤ 1 / c2 := by
    apply (div_le_iff₀ hlampos).2
    have hcl : 1 ≤ (1 / c2) * lam := by
      simpa only [one_div_mul_eq_div] using
        ((le_div_iff₀ hc2).2 (by simpa using hlam) : 1 ≤ lam / c2)
    linarith [hmu.1]
  have hcoeff : 0 ≤ mu * lam / ((1 - mu) * r2) :=
    div_nonneg (mul_nonneg hmu.1 hlampos.le) (mul_nonneg hgap.le hr2.le)
  have hfact : mu * delta / (r1 * d) =
      (delta / d) * (r2 / r1) * ((1 - mu) / lam) *
        (mu * lam / ((1 - mu) * r2)) := by
    field_simp [hr1.ne', hr2.ne', hd.ne', hlampos.ne', hgap.ne']
  rw [hfact]
  calc
    (delta / d) * (r2 / r1) * ((1 - mu) / lam) *
        (mu * lam / ((1 - mu) * r2)) ≤
        L * (K / c1) * (1 / c2) *
          (mu * lam / ((1 - mu) * r2)) := by
            gcongr
    _ = (K / (c1 * c2) * L) * (mu * lam / ((1 - mu) * r2)) := by ring

/-- At each interior outgoing point, the weighted radius term in (3.9) is
bounded by the positive outgoing coefficient from (3.1a). -/
theorem ComparisonData.radius_mass_term_le_nuCoeff (D : ComparisonData)
    {V u t c₁ c₂ K : ℝ} (hV : V ≤ D.b)
    (hut : (u, t) ∈ triangle D.a V)
    (hc₁ : 0 < c₁) (hlam₁ : ∀ p ∈ D.U₁, c₁ ≤ D.S₁.lam p.1 p.2)
    (hc₂ : 0 < c₂) (hlam₂ : ∀ p ∈ D.U₂, c₂ ≤ D.S₂.lam p.1 p.2)
    (hrhi₂ : ∀ x y, (x, y) ∈ D.U₂ → D.S₂.r x y ≤ K * (y - x)) :
    IsBVSolution.mu D.S₂ u t *
      |D.S₁.r u t - D.S₂.r u t| / (D.S₁.r u t * (t - u)) ≤
      (K / (c₁ * c₂) * D.L V) * IsBVSolution.nuCoeff D.S₂ u t := by
  have htT : (u, t) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨hut.1, hut.2.1, hut.2.2.trans_le hV⟩
  have hp := D.hT htT
  have hr₁ := D.h₁.solution.radius_pos (u, t) hp.1
  have hr₂ := D.h₂.solution.radius_pos (u, t) hp.2
  have hd : 0 < t - u := sub_pos.mpr hut.2.1
  have hmu := D.h₂.mass_ratio_bounds hp.2
  have hrlo := D.h₁.radius_lower hlam₁ hp.1
  have hdelta := D.radius_diff_le_L hV hut
  have hbase := radius_term_le_coeff hr₁ hr₂ hd hc₁ hc₂ hmu
    (hlam₂ (u, t) hp.2) hrlo (hrhi₂ u t hp.2)
    ⟨abs_nonneg _, hdelta⟩
  have hcoeff := D.h₂.nuCoeff_eq_mass_ratio_coefficient_out hp.2
  unfold IsBVSolution.mu at hbase ⊢
  rw [hcoeff]
  exact hbase

/-- The outgoing coefficient in (3.1a) has a uniform finite `lintegral`
bound on every compact comparison top. -/
theorem ComparisonData.nuCoeff_lintegral_uniform (D : ComparisonData) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ V, D.a < V → V < D.b →
      ∀ u ∈ Ico D.a V,
        (∫⁻ t in Ioc u V, ENNReal.ofReal
          (IsBVSolution.nuCoeff D.S₂ u t)) ≤ ENNReal.ofReal M := by
  obtain ⟨c, hc, hlam⟩ := D.h₂.lam_bounded_below
  let B := max D.h₂.item5.choose 0
  let W := max D.h₂.item3_variation.choose 0
  have hB : 0 ≤ B := le_max_right _ _
  have hW : 0 ≤ W := le_max_right _ _
  let Q := B / c
  have hQ : 0 ≤ Q := div_nonneg hB hc.le
  refine ⟨Q * W, mul_nonneg hQ hW, ?_⟩
  intro V haV hVb u hu
  have hut : (u, V) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨hu.1, hu.2, hVb⟩
  have hp := (D.hT hut).2
  have hquot : ∀ t ∈ Ioc u V, |D.S₂.theta u t / D.S₂.lam u t| ≤ Q := by
    intro t ht
    have htU := D.h₂.solution.development.outgoing_mem hp ht.1 ht.2
    have hLam := hlam (u, t) htU
    have hLamPos := hc.trans_le hLam
    have hTheta := D.h₂.theta_abs_le_global_variation htU
    rw [abs_div, abs_of_pos hLamPos]
    apply (div_le_iff₀ hLamPos).2
    have hmul := mul_le_mul_of_nonneg_left hLam hQ
    have heq : Q * c = B := by dsimp [Q]; field_simp [hc.ne']
    rw [heq] at hmul
    exact hTheta.trans hmul
  have hInt := D.h₂.nu_coeff_integrable_axis hp hquot
  have hNonneg : 0 ≤ᵐ[volume.restrict (Ioc u V)]
      (IsBVSolution.nuCoeff D.S₂ u) := by
    exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht =>
      D.h₂.nu_coeff_nonneg D.h₂.solution.development
        (D.h₂.solution.development.outgoing_mem hp ht.1 ht.2))
  have hlin : (∫⁻ t in Ioc u V, ENNReal.ofReal
      (IsBVSolution.nuCoeff D.S₂ u t)) =
      ENNReal.ofReal (∫ t in u..V, IsBVSolution.nuCoeff D.S₂ u t) := by
    rw [intervalIntegral.integral_of_le hu.2.le]
    exact (ofReal_integral_eq_lintegral_ofReal hInt hNonneg).symm
  rw [hlin]
  apply ENNReal.ofReal_le_ofReal
  have hvar : (eVariationOn (D.S₂.phi u) (Ioc u V)).toReal ≤ W := by
    have hsub : Ioc u V ⊆ {t | (u, t) ∈ D.U₂} := by
      intro t ht
      exact D.h₂.solution.development.outgoing_mem hp ht.1 ht.2
    exact ENNReal.toReal_le_of_le_ofReal hW
      ((eVariationOn.mono (D.S₂.phi u) hsub).trans
        ((D.h₂.item3_variation.choose_spec.1 u).trans
          (ENNReal.ofReal_le_ofReal (le_max_left _ _))))
  exact (D.h₂.eq3_1a_nuCoeff hp hquot).trans
    (mul_le_mul_of_nonneg_left hvar hQ)

/-- The radius part of the (3.9) contribution to the outgoing `N` estimate
is bounded by a fixed multiple of `L`, uniformly in the compact top. The
integral is expressed as a nonnegative `lintegral` so no endpoint value of a
representative is used. -/
theorem ComparisonData.radius_mass_term_lintegral_uniform
    (D : ComparisonData) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V, D.a < V → V < D.b →
      ∀ u ∈ Ico D.a V,
        (∫⁻ t in Ioc u V, ENNReal.ofReal
          (IsBVSolution.mu D.S₂ u t *
            |D.S₁.r u t - D.S₂.r u t| /
              (D.S₁.r u t * (t - u)))) ≤
          ENNReal.ofReal (C * D.L V) := by
  obtain ⟨c₁, hc₁, hlam₁⟩ := D.h₁.lam_bounded_below
  obtain ⟨c₂, hc₂, hlam₂⟩ := D.h₂.lam_bounded_below
  obtain ⟨K₀, _, hrhi₀⟩ := D.h₂.exists_uniform_radius_upper
  let K := max K₀ 0
  have hK : 0 ≤ K := le_max_right _ _
  have hrhi₂ : ∀ x y, (x, y) ∈ D.U₂ → D.S₂.r x y ≤ K * (y - x) := by
    intro x y hxy
    have hd : 0 ≤ y - x := sub_nonneg.mpr
      (D.h₂.solution.development.wedge hxy).2.le
    exact (hrhi₀ x y hxy).trans
      (mul_le_mul_of_nonneg_right (le_max_left K₀ 0) hd)
  let c₀ := K / (c₁ * c₂)
  have hc₀ : 0 ≤ c₀ := div_nonneg hK (mul_nonneg hc₁.le hc₂.le)
  obtain ⟨M, hM, hcoeff⟩ := D.nuCoeff_lintegral_uniform
  refine ⟨c₀ * M, mul_nonneg hc₀ hM, ?_⟩
  intro V haV hVb u hu
  have hmid : (D.a, (D.a + V) / 2) ∈ triangle D.a V := by
    exact (mem_triangle).2 ⟨le_rfl, by linarith, by linarith⟩
  have hrad := D.radius_diff_le_L hVb.le hmid
  have hL : 0 ≤ D.L V := by
    have hh := abs_nonneg
      (D.S₁.r D.a ((D.a + V) / 2) - D.S₂.r D.a ((D.a + V) / 2))
    have hd : 0 < (D.a + V) / 2 - D.a := by linarith [haV]
    nlinarith [hrad]
  have hfactor : 0 ≤ c₀ * D.L V := mul_nonneg hc₀ hL
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioc u V),
      ENNReal.ofReal
          (IsBVSolution.mu D.S₂ u t *
            |D.S₁.r u t - D.S₂.r u t| /
              (D.S₁.r u t * (t - u))) ≤
        ENNReal.ofReal (c₀ * D.L V) *
          ENNReal.ofReal (IsBVSolution.nuCoeff D.S₂ u t) := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    have hne : ∀ᵐ t : ℝ ∂volume, t ≠ V := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with t htne ht
    have htV : t < V := lt_of_le_of_ne ht.2 htne
    have hut : (u, t) ∈ triangle D.a V :=
      (mem_triangle).2 ⟨hu.1, ht.1, htV⟩
    have hle := D.radius_mass_term_le_nuCoeff hVb.le hut hc₁ hlam₁
      hc₂ hlam₂ hrhi₂
    have hmul : ENNReal.ofReal
        ((c₀ * D.L V) * IsBVSolution.nuCoeff D.S₂ u t) =
        ENNReal.ofReal (c₀ * D.L V) *
          ENNReal.ofReal (IsBVSolution.nuCoeff D.S₂ u t) := by
      exact ENNReal.ofReal_mul hfactor
    rw [← hmul]
    exact ENNReal.ofReal_le_ofReal hle
  calc
    (∫⁻ t in Ioc u V, ENNReal.ofReal
      (IsBVSolution.mu D.S₂ u t *
        |D.S₁.r u t - D.S₂.r u t| /
          (D.S₁.r u t * (t - u)))) ≤
        ∫⁻ t in Ioc u V,
          ENNReal.ofReal (c₀ * D.L V) *
            ENNReal.ofReal (IsBVSolution.nuCoeff D.S₂ u t) :=
      lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (c₀ * D.L V) *
        (∫⁻ t in Ioc u V, ENNReal.ofReal
          (IsBVSolution.nuCoeff D.S₂ u t)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (c₀ * D.L V) * ENNReal.ofReal M := by
      gcongr
      exact hcoeff V haV hVb u hu
    _ = ENNReal.ofReal ((c₀ * M) * D.L V) := by
      rw [← ENNReal.ofReal_mul hfactor]
      congr 1
      ring

/-- The radius-error integrand is measurable on each outgoing half-open
characteristic because `r` and `m` are continuous characteristic primitives. -/
theorem ComparisonData.radius_mass_term_aestronglyMeasurable
    (D : ComparisonData) {V u : ℝ}
    (hVb : V ≤ D.b) (hu : u ∈ Ico D.a V) :
    AEStronglyMeasurable
      (fun t => IsBVSolution.mu D.S₂ u t *
        |D.S₁.r u t - D.S₂.r u t| /
          (D.S₁.r u t * (t - u)))
      (volume.restrict (Ioc u V)) := by
  have hprim₁ := D.outgoing_continuous_primitives hu.1 hVb D.S₁ (Or.inl rfl)
  have hprim₂ := D.outgoing_continuous_primitives hu.1 hVb D.S₂ (Or.inr rfl)
  have hr₁ : ContinuousOn (D.S₁.r u) (Ioo u V) := hprim₁.1
  have hr₂ : ContinuousOn (D.S₂.r u) (Ioo u V) := hprim₂.1
  have hm₂ : ContinuousOn (D.S₂.m u) (Ioo u V) := hprim₂.2.2.1
  have hden₁ : ∀ t ∈ Ioo u V, D.S₁.r u t ≠ 0 := by
    intro t ht
    have htT : (u, t) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨hu.1, ht.1, ht.2.trans_le hVb⟩
    exact (D.h₁.solution.radius_pos (u, t) (D.hT htT).1).ne'
  have hden₂ : ∀ t ∈ Ioo u V, D.S₂.r u t ≠ 0 := by
    intro t ht
    have htT : (u, t) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨hu.1, ht.1, ht.2.trans_le hVb⟩
    exact (D.h₂.solution.radius_pos (u, t) (D.hT htT).2).ne'
  have hmu : ContinuousOn (fun t => IsBVSolution.mu D.S₂ u t)
      (Ioo u V) := by
    unfold IsBVSolution.mu
    exact (continuousOn_const.mul hm₂).div hr₂ hden₂
  have hdiff : ContinuousOn
      (fun t => |D.S₁.r u t - D.S₂.r u t|) (Ioo u V) :=
    (hr₁.sub hr₂).abs
  have hdist : ContinuousOn (fun t : ℝ => t - u) (Ioo u V) := by fun_prop
  have hden : ∀ t ∈ Ioo u V,
      D.S₁.r u t * (t - u) ≠ 0 := by
    intro t ht
    exact mul_ne_zero (hden₁ t ht) (sub_ne_zero.mpr (ne_of_gt ht.1))
  have hcont : ContinuousOn
      (fun t => IsBVSolution.mu D.S₂ u t *
        |D.S₁.r u t - D.S₂.r u t| /
          (D.S₁.r u t * (t - u))) (Ioo u V) :=
    (hmu.mul hdiff).div (hr₁.mul hdist) hden
  have hmeas : AEStronglyMeasurable
      (fun t => IsBVSolution.mu D.S₂ u t *
        |D.S₁.r u t - D.S₂.r u t| /
          (D.S₁.r u t * (t - u)))
      (volume.restrict (Ioo u V)) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  change AEStronglyMeasurable _ (volume.restrict (Ioc u V))
  rw [← restrict_Ioo_eq_restrict_Ioc]
  exact hmeas

/-- The weighted radius contribution is integrable on each outgoing
characteristic. Its half-open endpoint can have any frozen representative. -/
theorem ComparisonData.radius_mass_term_integrable
    (D : ComparisonData) {V u : ℝ}
    (haV : D.a < V) (hVb : V < D.b) (hu : u ∈ Ico D.a V) :
    Integrable
      (fun t => IsBVSolution.mu D.S₂ u t *
        |D.S₁.r u t - D.S₂.r u t| /
          (D.S₁.r u t * (t - u)))
      (volume.restrict (Ioc u V)) := by
  let f : ℝ → ℝ := fun t => IsBVSolution.mu D.S₂ u t *
    |D.S₁.r u t - D.S₂.r u t| /
      (D.S₁.r u t * (t - u))
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc u V)] f := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards with t ht
    have htT : (u, t) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨hu.1, ht.1, ht.2.trans_lt hVb⟩
    have hp := D.hT htT
    have hmu := (D.h₂.mass_ratio_bounds hp.2).1
    have hr := D.h₁.solution.radius_pos (u, t) hp.1
    exact div_nonneg (mul_nonneg hmu (abs_nonneg _))
      (mul_nonneg hr.le (sub_nonneg.mpr ht.1.le))
  obtain ⟨C, _, hC⟩ := D.radius_mass_term_lintegral_uniform
  have hfinite : (∫⁻ t in Ioc u V, ENNReal.ofReal (f t)) < ⊤ :=
    lt_of_le_of_lt (hC V haV hVb u hu) ENNReal.ofReal_lt_top
  exact ⟨D.radius_mass_term_aestronglyMeasurable hVb.le hu,
    (hasFiniteIntegral_iff_ofReal hnonneg).2 hfinite⟩

/-- The weighted radius contribution to (3.9) is bounded in the ordinary
outgoing integral by a uniform multiple of the stable radius norm `L`. -/
theorem ComparisonData.radius_mass_term_integral_uniform (D : ComparisonData) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V, D.a < V → V < D.b →
      ∀ u ∈ Ico D.a V,
        (∫ t in u..V,
          IsBVSolution.mu D.S₂ u t *
            |D.S₁.r u t - D.S₂.r u t| /
              (D.S₁.r u t * (t - u))) ≤ C * D.L V := by
  obtain ⟨C, hCnonneg, hC⟩ := D.radius_mass_term_lintegral_uniform
  refine ⟨C, hCnonneg, ?_⟩
  intro V haV hVb u hu
  let f : ℝ → ℝ := fun t => IsBVSolution.mu D.S₂ u t *
    |D.S₁.r u t - D.S₂.r u t| /
      (D.S₁.r u t * (t - u))
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc u V)] f := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards with t ht
    have htT : (u, t) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨hu.1, ht.1, ht.2.trans_lt hVb⟩
    have hp := D.hT htT
    have hmu := (D.h₂.mass_ratio_bounds hp.2).1
    have hr := D.h₁.solution.radius_pos (u, t) hp.1
    exact div_nonneg (mul_nonneg hmu (abs_nonneg _))
      (mul_nonneg hr.le (sub_nonneg.mpr ht.1.le))
  have hint : Integrable f (volume.restrict (Ioc u V)) :=
    D.radius_mass_term_integrable haV hVb hu
  have hreal : 0 ≤ ∫ t in Ioc u V, f t :=
    integral_nonneg_of_ae hnonneg
  have heq : ENNReal.ofReal (∫ t in Ioc u V, f t) =
      ∫⁻ t in Ioc u V, ENNReal.ofReal (f t) :=
    ofReal_integral_eq_lintegral_ofReal hint hnonneg
  have hle : ENNReal.ofReal (∫ t in Ioc u V, f t) ≤
      ENNReal.ofReal (C * D.L V) :=
    heq.trans_le (hC V haV hVb u hu)
  have hbound := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [ENNReal.toReal_ofReal hreal] at hbound
  have hL : 0 ≤ D.L V := by
    have hmid : (D.a, (D.a + V) / 2) ∈ triangle D.a V :=
      (mem_triangle).2 ⟨le_rfl, by linarith, by linarith⟩
    have hrad := D.radius_diff_le_L hVb.le hmid
    have hh := abs_nonneg
      (D.S₁.r D.a ((D.a + V) / 2) - D.S₂.r D.a ((D.a + V) / 2))
    have hd : 0 < (D.a + V) / 2 - D.a := by linarith [haV]
    nlinarith [hrad]
  rw [ENNReal.toReal_ofReal (mul_nonneg hCnonneg hL)] at hbound
  simpa only [intervalIntegral.integral_of_le hu.2.le] using hbound

end ChristodoulouBV.Uniqueness

end
