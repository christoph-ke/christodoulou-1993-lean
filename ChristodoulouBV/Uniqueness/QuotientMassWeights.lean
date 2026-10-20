module

public import ChristodoulouBV.Uniqueness.QuotientDifferenceAlgebra
public import ChristodoulouBV.Uniqueness.RadiusMassTerm

/-!
# Weighted mass-ratio differences

The mass-ratio identity (3.9) splits the axis-weighted difference into a
weighted mass gap and a radius error on either characteristic family.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

private theorem weighted_mu_alg {d r c dm dr mu q : ℝ}
    (hd : 0 < d) (hr : 0 < r) (hc : 0 < c)
    (hlo : c * d ≤ r)
    (hq : q ≤ 2 * |dm| / r + mu * |dr| / r) :
    q / d ≤ (2 / c) * (|dm| / d ^ 2) +
      mu * |dr| / (r * d) := by
  have hbase : 2 * |dm| / (r * d) ≤
      (2 / c) * (|dm| / d ^ 2) := by
    apply (div_le_iff₀ (mul_pos hr hd)).2
    have hmul := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ 2 * |dm|)
    field_simp [hc.ne', hd.ne']
    nlinarith only [hmul]
  calc
    q / d ≤ (2 * |dm| / r + mu * |dr| / r) / d :=
      div_le_div_of_nonneg_right hq hd.le
    _ = 2 * |dm| / (r * d) + mu * |dr| / (r * d) := by ring
    _ ≤ (2 / c) * (|dm| / d ^ 2) + mu * |dr| / (r * d) :=
      add_le_add_left hbase _

/-- The mass-ratio difference divided by the axis distance splits into the
Hardy mass weight and a radius error at each comparison point. -/
theorem ComparisonData.mu_diff_weighted_pointwise (D : ComparisonData)
    {u v c : ℝ} (hc : 0 < c)
    (hlam : ∀ p ∈ D.U₁, c ≤ D.S₁.lam p.1 p.2)
    (huv : (u, v) ∈ triangle D.a D.b) :
    |IsBVSolution.mu D.S₁ u v - IsBVSolution.mu D.S₂ u v| /
        (v - u) ≤
      (2 / c) *
        (|D.S₁.m u v - D.S₂.m u v| / (v - u) ^ 2) +
      IsBVSolution.mu D.S₂ u v *
        |D.S₁.r u v - D.S₂.r u v| /
          (D.S₁.r u v * (v - u)) := by
  have hp := D.hT huv
  have hd : 0 < v - u := sub_pos.mpr huv.2.1
  have hr := D.h₁.solution.radius_pos (u, v) hp.1
  have hrlo := D.h₁.radius_lower hlam hp.1
  exact weighted_mu_alg hd hr hc hrlo (D.mu_diff_abs_le huv)

/-- The outgoing weighted mass-ratio difference is bounded by the radius
norm and finite outgoing Hardy norm, uniformly over compact comparison tops.
The integral retains the excluded axis as an `Ioc` endpoint. -/
theorem ComparisonData.mu_diff_weighted_outgoing (D : ComparisonData) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V, D.a < V → V < D.b →
      ∀ u ∈ Ico D.a V,
        (∫⁻ t in Ioc u V,
          ENNReal.ofReal
            (|IsBVSolution.mu D.S₁ u t -
                IsBVSolution.mu D.S₂ u t| / (t - u))) ≤
          ENNReal.ofReal (C * (D.L V + (D.Gamma V).toReal)) := by
  obtain ⟨c, hc, hlam⟩ := D.h₁.lam_bounded_below
  obtain ⟨R, hR, hrad⟩ := D.radius_mass_term_lintegral_uniform
  let C := max (2 / c) R + 1
  have hF : 0 ≤ 2 / c := div_nonneg (by norm_num) hc.le
  have hC : 0 ≤ C := by dsimp [C]; linarith [le_max_left (2 / c) R]
  have hFC : 2 / c ≤ C := by dsimp [C]; linarith [le_max_left (2 / c) R]
  have hRC : R ≤ C := by dsimp [C]; linarith [le_max_right (2 / c) R]
  refine ⟨C, hC, ?_⟩
  intro V haV hVb u hu
  let g : ℝ → ℝ := fun t =>
    |D.S₁.m u t - D.S₂.m u t| / (t - u) ^ 2
  let rerr : ℝ → ℝ := fun t =>
    IsBVSolution.mu D.S₂ u t *
      |D.S₁.r u t - D.S₂.r u t| /
        (D.S₁.r u t * (t - u))
  have hL : 0 ≤ D.L V := D.L_nonneg haV hVb
  have hΓ : 0 ≤ (D.Gamma V).toReal := ENNReal.toReal_nonneg
  have hmassMeas : AEMeasurable (fun t => ENNReal.ofReal (g t))
      (volume.restrict (Ioc u V)) :=
    (D.outgoing_mass_diff_weight_integrable hVb hu).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioc u V),
      ENNReal.ofReal
        (|IsBVSolution.mu D.S₁ u t - IsBVSolution.mu D.S₂ u t| /
          (t - u)) ≤
        ENNReal.ofReal (2 / c) * ENNReal.ofReal (g t) +
          ENNReal.ofReal (rerr t) := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    have hne : ∀ᵐ t : ℝ ∂volume, t ≠ V := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with t htne ht
    have htV : t < V := lt_of_le_of_ne ht.2 htne
    have htT : (u, t) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨hu.1, ht.1, htV.trans hVb⟩
    have hp := D.hT htT
    have hmu : 0 ≤ IsBVSolution.mu D.S₂ u t :=
      (D.h₂.mass_ratio_bounds hp.2).1
    have hr := D.h₁.solution.radius_pos (u, t) hp.1
    have hd : 0 < t - u := sub_pos.mpr ht.1
    have hg : 0 ≤ g t := div_nonneg (abs_nonneg _) (sq_nonneg _)
    have he : 0 ≤ rerr t :=
      div_nonneg (mul_nonneg hmu (abs_nonneg _))
        (mul_nonneg hr.le hd.le)
    have hreal := D.mu_diff_weighted_pointwise hc hlam htT
    change _ ≤ (2 / c) * g t + rerr t at hreal
    rw [← ENNReal.ofReal_mul hF, ← ENNReal.ofReal_add
      (mul_nonneg hF hg) he]
    exact ENNReal.ofReal_le_ofReal hreal
  have hΓfinite : D.Gamma V ≠ ⊤ := by
    obtain ⟨M, _, hM⟩ := D.Gamma_uniform_bound
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hM V haV hVb)
  have hmass : (∫⁻ t in Ioc u V, ENNReal.ofReal (g t)) ≤
      ENNReal.ofReal (D.Gamma V).toReal := by
    have hh : (∫⁻ t in Ioc u V, ENNReal.ofReal (g t)) ≤ D.Gamma V := by
      unfold ComparisonData.Gamma
      exact le_iSup_of_le u (le_iSup_of_le hu le_rfl)
    simpa only [ENNReal.ofReal_toReal hΓfinite] using hh
  have hrerr := hrad V haV hVb u hu
  have hfactor : 0 ≤ (2 / c) * (D.Gamma V).toReal :=
    mul_nonneg hF hΓ
  have hradprod : 0 ≤ R * D.L V := mul_nonneg hR hL
  have hreal : (2 / c) * (D.Gamma V).toReal + R * D.L V ≤
      C * (D.L V + (D.Gamma V).toReal) := by
    have h₁ := mul_le_mul_of_nonneg_right hFC hΓ
    have h₂ := mul_le_mul_of_nonneg_right hRC hL
    nlinarith only [h₁, h₂]
  calc
    (∫⁻ t in Ioc u V,
      ENNReal.ofReal
        (|IsBVSolution.mu D.S₁ u t -
            IsBVSolution.mu D.S₂ u t| / (t - u))) ≤
        ∫⁻ t in Ioc u V,
          ENNReal.ofReal (2 / c) * ENNReal.ofReal (g t) +
            ENNReal.ofReal (rerr t) := lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (2 / c) *
          (∫⁻ t in Ioc u V, ENNReal.ofReal (g t)) +
          (∫⁻ t in Ioc u V, ENNReal.ofReal (rerr t)) := by
        rw [lintegral_add_left' (hmassMeas.const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (2 / c) *
          ENNReal.ofReal (D.Gamma V).toReal +
          ENNReal.ofReal (R * D.L V) := by
        gcongr
    _ = ENNReal.ofReal
          ((2 / c) * (D.Gamma V).toReal + R * D.L V) := by
        rw [ENNReal.ofReal_add hfactor hradprod,
          ENNReal.ofReal_mul hF]
    _ ≤ ENNReal.ofReal (C * (D.L V + (D.Gamma V).toReal)) :=
      ENNReal.ofReal_le_ofReal hreal

private theorem incoming_radius_term_le_coeff
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

/-- On every incoming comparison ray, the radius error in the weighted mass
ratio is bounded by the negative incoming coefficient times `N`. -/
theorem ComparisonData.radius_mass_term_le_incomingCoeff (D : ComparisonData)
    {V u v c₁ c₂ K : ℝ} (hV : V < D.b)
    (huv : (u, v) ∈ triangle D.a V)
    (hc₁ : 0 < c₁)
    (hlam₁ : ∀ p ∈ D.U₁, c₁ ≤ D.S₁.lam p.1 p.2)
    (hc₂ : 0 < c₂)
    (hlam₂ : ∀ p ∈ D.U₂, c₂ ≤ D.S₂.lam p.1 p.2)
    (hrhi₂ : ∀ x y, (x, y) ∈ D.U₂ → D.S₂.r x y ≤ K * (y - x)) :
    IsBVSolution.mu D.S₂ u v *
      |D.S₁.r u v - D.S₂.r u v| /
        (D.S₁.r u v * (v - u)) ≤
      (K / (c₁ * c₂) * D.N V) *
        (-IsBVSolution.incomingCoeff D.S₂ u v) := by
  have hfull : (u, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨huv.1, huv.2.1, huv.2.2.trans hV⟩
  have hp := D.hT hfull
  have hr₁ := D.h₁.solution.radius_pos (u, v) hp.1
  have hr₂ := D.h₂.solution.radius_pos (u, v) hp.2
  have hd : 0 < v - u := sub_pos.mpr huv.2.1
  have hmu := D.h₂.mass_ratio_bounds hp.2
  have hnu₂ : c₂ ≤ -D.S₂.nu u v := by
    have hn := D.h₂.nu_le_neg_lower hc₂ hlam₂ hp.2
    linarith
  have hrlo := D.h₁.radius_lower hlam₁ hp.1
  have hdelta := D.radius_diff_le_N hV huv
  have hbase := incoming_radius_term_le_coeff hr₁ hr₂ hd hc₁ hc₂
    hmu hnu₂ hrlo (hrhi₂ u v hp.2) ⟨abs_nonneg _, hdelta⟩
  have hcoeff :
      IsBVSolution.mu D.S₂ u v * (-D.S₂.nu u v) /
        ((1 - IsBVSolution.mu D.S₂ u v) * D.S₂.r u v) =
        -IsBVSolution.incomingCoeff D.S₂ u v := by
    unfold IsBVSolution.incomingCoeff IsBVSolution.mu
    ring
  change IsBVSolution.mu D.S₂ u v *
      |D.S₁.r u v - D.S₂.r u v| /
        (D.S₁.r u v * (v - u)) ≤
      (K / (c₁ * c₂) * D.N V) *
        (IsBVSolution.mu D.S₂ u v * (-D.S₂.nu u v) /
          ((1 - IsBVSolution.mu D.S₂ u v) * D.S₂.r u v)) at hbase
  rw [hcoeff] at hbase
  exact hbase

/-- The incoming radius-error part of the weighted mass-ratio difference is
uniformly bounded by `N` when the local incoming scalar variation is at most
one. The negative coefficient is integrable up to the terminal axis. -/
theorem ComparisonData.radius_mass_term_incoming_lintegral_uniform
    (D : ComparisonData) (ha : D.a = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ((∀ u v, (u, v) ∈ triangle D.a D.b →
        ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
          (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ 1 ∧
          (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ 1) →
      ∀ V, D.a < V → V < D.b →
        ∀ v ∈ Ioo D.a V,
          (∫⁻ s in Ico D.a v,
            ENNReal.ofReal
              (IsBVSolution.mu D.S₂ s v *
                |D.S₁.r s v - D.S₂.r s v| /
                  (D.S₁.r s v * (v - s)))) ≤
            ENNReal.ofReal (C * D.N V)) := by
  let w := (D.a + D.b) / 2
  have hw : w ∈ Ioo D.a D.b := by
    dsimp [w]
    constructor <;> linarith [D.hab]
  have href : (0, w) ∈ D.U₁ ∩ D.U₂ := by
    simpa only [ha] using D.hT ((mem_triangle).2 ⟨le_rfl, hw.1, hw.2⟩)
  have hdata : D.S₁.phi 0 w = D.S₂.phi 0 w := by
    simpa only [ha] using (D.hdata w hw).2
  obtain ⟨J, hJ, hcoef⟩ := D.h₁.eq3_12_usable D.h₂ href hdata
  obtain ⟨c₁, hc₁, hlam₁⟩ := D.h₁.lam_bounded_below
  obtain ⟨c₂, hc₂, hlam₂⟩ := D.h₂.lam_bounded_below
  obtain ⟨K₀, _, hrhi₀⟩ := D.h₂.exists_uniform_radius_upper
  let K := max K₀ 0
  have hK : 0 ≤ K := le_max_right _ _
  have hrhi : ∀ x y, (x, y) ∈ D.U₂ →
      D.S₂.r x y ≤ K * (y - x) := by
    intro x y hxy
    have hd : 0 ≤ y - x :=
      sub_nonneg.mpr (D.h₂.solution.development.wedge hxy).2.le
    exact (hrhi₀ x y hxy).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hd)
  let F := K / (c₁ * c₂)
  have hF : 0 ≤ F := div_nonneg hK (mul_pos hc₁ hc₂).le
  let C := F * J
  have hC : 0 ≤ C := mul_nonneg hF hJ
  refine ⟨C, hC, ?_⟩
  intro hsmall V haV hVb v hv
  have hvb : v < D.b := hv.2.trans hVb
  have hfull : (D.a, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨le_rfl, hv.1, hvb⟩
  have hvar : (eVariationOn (fun s => D.S₂.phi s v)
      (Ico D.a v)).toReal ≤ 1 :=
    (hsmall D.a v hfull D.S₂ (Or.inr rfl)).2
  have hcoefReal : -(∫ s in D.a..v,
      IsBVSolution.incomingCoeff D.S₂ s v) ≤ J := by
    have hh := hcoef 1 (by norm_num) D.a D.b D.a v D.hT hfull D.S₂
      (Or.inr rfl) hvar
    change -(∫ s in D.a..v,
      IsBVSolution.incomingCoeff D.S₂ s v) ≤ J * 1 at hh
    simpa only [mul_one] using hh
  have hInt : IntegrableOn
      (fun s => -IsBVSolution.incomingCoeff D.S₂ s v)
      (Ioc D.a v) volume :=
    ((D.incomingCoeff_integrable_pair ha) v ⟨hv.1, hvb⟩).2.neg
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc D.a v)]
      (fun s => -IsBVSolution.incomingCoeff D.S₂ s v) := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    have hne : ∀ᵐ s : ℝ ∂volume, s ≠ v := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with s hsne hs
    have hsv : (s, v) ∈ D.U₂ :=
      (D.hT ((mem_triangle).2
        ⟨hs.1.le, lt_of_le_of_ne hs.2 hsne, hvb⟩)).2
    exact neg_nonneg.mpr (D.h₂.incomingCoeff_nonpos hsv)
  have hcoefLin : (∫⁻ s in Ico D.a v,
      ENNReal.ofReal (-IsBVSolution.incomingCoeff D.S₂ s v)) ≤
      ENNReal.ofReal J := by
    rw [restrict_Ico_eq_restrict_Ioc]
    have hEq := ofReal_integral_eq_lintegral_ofReal hInt hnonneg
    rw [← hEq]
    apply ENNReal.ofReal_le_ofReal
    rw [← intervalIntegral.integral_of_le hv.1.le,
      intervalIntegral.integral_neg]
    exact hcoefReal
  have hN : 0 ≤ D.N V := D.N_nonneg haV hVb
  have hfactor : 0 ≤ F * D.N V := mul_nonneg hF hN
  have hpoint : ∀ᵐ s ∂volume.restrict (Ico D.a v),
      ENNReal.ofReal
        (IsBVSolution.mu D.S₂ s v *
          |D.S₁.r s v - D.S₂.r s v| /
            (D.S₁.r s v * (v - s))) ≤
        ENNReal.ofReal (F * D.N V) *
          ENNReal.ofReal (-IsBVSolution.incomingCoeff D.S₂ s v) := by
    apply ae_restrict_of_forall_mem measurableSet_Ico
    intro s hs
    have hsT : (s, v) ∈ triangle D.a V :=
      (mem_triangle).2 ⟨hs.1, hs.2, hv.2⟩
    have hreal := D.radius_mass_term_le_incomingCoeff hVb hsT
      hc₁ hlam₁ hc₂ hlam₂ hrhi
    change _ ≤ (F * D.N V) *
      (-IsBVSolution.incomingCoeff D.S₂ s v) at hreal
    rw [← ENNReal.ofReal_mul hfactor]
    exact ENNReal.ofReal_le_ofReal hreal
  calc
    (∫⁻ s in Ico D.a v,
      ENNReal.ofReal
        (IsBVSolution.mu D.S₂ s v *
          |D.S₁.r s v - D.S₂.r s v| /
            (D.S₁.r s v * (v - s)))) ≤
        ∫⁻ s in Ico D.a v,
          ENNReal.ofReal (F * D.N V) *
            ENNReal.ofReal (-IsBVSolution.incomingCoeff D.S₂ s v) :=
      lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (F * D.N V) *
          (∫⁻ s in Ico D.a v,
            ENNReal.ofReal (-IsBVSolution.incomingCoeff D.S₂ s v)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (F * D.N V) * ENNReal.ofReal J := by
      gcongr
    _ = ENNReal.ofReal (C * D.N V) := by
      rw [← ENNReal.ofReal_mul hfactor]
      congr 1
      dsimp [C]
      ring

/-- The incoming weighted mass-ratio difference is bounded by the incoming
radius norm and finite terminal Hardy norm, uniformly in the compact top.
The full `Ico` characteristic reaches the excluded terminal axis. -/
theorem ComparisonData.mu_diff_weighted_incoming (D : ComparisonData)
    (ha : D.a = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ((∀ u v, (u, v) ∈ triangle D.a D.b →
        ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
          (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ 1 ∧
          (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ 1) →
      ∀ V, D.a < V → V < D.b →
        ∀ v ∈ Ioo D.a V,
          (∫⁻ s in Ico D.a v,
            ENNReal.ofReal
              (|IsBVSolution.mu D.S₁ s v -
                  IsBVSolution.mu D.S₂ s v| / (v - s))) ≤
            ENNReal.ofReal
              (C * (D.N V + (D.GammaStar V).toReal))) := by
  obtain ⟨c, hc, hlam⟩ := D.h₁.lam_bounded_below
  obtain ⟨R, hR, hrad⟩ := D.radius_mass_term_incoming_lintegral_uniform ha
  let C := max (2 / c) R + 1
  have hF : 0 ≤ 2 / c := div_nonneg (by norm_num) hc.le
  have hC : 0 ≤ C := by dsimp [C]; linarith [le_max_left (2 / c) R]
  have hFC : 2 / c ≤ C := by dsimp [C]; linarith [le_max_left (2 / c) R]
  have hRC : R ≤ C := by dsimp [C]; linarith [le_max_right (2 / c) R]
  refine ⟨C, hC, ?_⟩
  intro hsmall V haV hVb v hv
  let g : ℝ → ℝ := fun s =>
    |D.S₁.m s v - D.S₂.m s v| / (v - s) ^ 2
  let rerr : ℝ → ℝ := fun s =>
    IsBVSolution.mu D.S₂ s v *
      |D.S₁.r s v - D.S₂.r s v| /
        (D.S₁.r s v * (v - s))
  have hN : 0 ≤ D.N V := D.N_nonneg haV hVb
  have hΓ : 0 ≤ (D.GammaStar V).toReal := ENNReal.toReal_nonneg
  have hmassMeas : AEMeasurable (fun s => ENNReal.ofReal (g s))
      (volume.restrict (Ico D.a v)) := by
    have hInt := D.incoming_mass_diff_weight_integrable hv.1
      (hv.2.trans hVb)
    exact hInt.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hpoint : ∀ᵐ s ∂volume.restrict (Ico D.a v),
      ENNReal.ofReal
        (|IsBVSolution.mu D.S₁ s v - IsBVSolution.mu D.S₂ s v| /
          (v - s)) ≤
        ENNReal.ofReal (2 / c) * ENNReal.ofReal (g s) +
          ENNReal.ofReal (rerr s) := by
    apply ae_restrict_of_forall_mem measurableSet_Ico
    intro s hs
    have hsT : (s, v) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨hs.1, hs.2, hv.2.trans hVb⟩
    have hp := D.hT hsT
    have hmu : 0 ≤ IsBVSolution.mu D.S₂ s v :=
      (D.h₂.mass_ratio_bounds hp.2).1
    have hr := D.h₁.solution.radius_pos (s, v) hp.1
    have hd : 0 < v - s := sub_pos.mpr hs.2
    have hg : 0 ≤ g s := div_nonneg (abs_nonneg _) (sq_nonneg _)
    have he : 0 ≤ rerr s :=
      div_nonneg (mul_nonneg hmu (abs_nonneg _))
        (mul_nonneg hr.le hd.le)
    have hreal := D.mu_diff_weighted_pointwise hc hlam hsT
    change _ ≤ (2 / c) * g s + rerr s at hreal
    rw [← ENNReal.ofReal_mul hF, ← ENNReal.ofReal_add
      (mul_nonneg hF hg) he]
    exact ENNReal.ofReal_le_ofReal hreal
  have hΓfinite : D.GammaStar V ≠ ⊤ := by
    obtain ⟨M, _, hM⟩ := D.GammaStar_uniform_bound
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hM V haV hVb)
  have hmass : (∫⁻ s in Ico D.a v, ENNReal.ofReal (g s)) ≤
      ENNReal.ofReal (D.GammaStar V).toReal := by
    have hh : (∫⁻ s in Ico D.a v, ENNReal.ofReal (g s)) ≤
        D.GammaStar V := by
      unfold ComparisonData.GammaStar
      exact le_iSup_of_le v (le_iSup_of_le hv le_rfl)
    simpa only [ENNReal.ofReal_toReal hΓfinite] using hh
  have hrerr := hrad hsmall V haV hVb v hv
  have hfactor : 0 ≤ (2 / c) * (D.GammaStar V).toReal :=
    mul_nonneg hF hΓ
  have hradprod : 0 ≤ R * D.N V := mul_nonneg hR hN
  have hreal : (2 / c) * (D.GammaStar V).toReal + R * D.N V ≤
      C * (D.N V + (D.GammaStar V).toReal) := by
    have h₁ := mul_le_mul_of_nonneg_right hFC hΓ
    have h₂ := mul_le_mul_of_nonneg_right hRC hN
    nlinarith only [h₁, h₂]
  calc
    (∫⁻ s in Ico D.a v,
      ENNReal.ofReal
        (|IsBVSolution.mu D.S₁ s v -
            IsBVSolution.mu D.S₂ s v| / (v - s))) ≤
        ∫⁻ s in Ico D.a v,
          ENNReal.ofReal (2 / c) * ENNReal.ofReal (g s) +
            ENNReal.ofReal (rerr s) := lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (2 / c) *
          (∫⁻ s in Ico D.a v, ENNReal.ofReal (g s)) +
          (∫⁻ s in Ico D.a v, ENNReal.ofReal (rerr s)) := by
        rw [lintegral_add_left' (hmassMeas.const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (2 / c) *
          ENNReal.ofReal (D.GammaStar V).toReal +
          ENNReal.ofReal (R * D.N V) := by
        gcongr
    _ = ENNReal.ofReal
          ((2 / c) * (D.GammaStar V).toReal + R * D.N V) := by
        rw [ENNReal.ofReal_add hfactor hradprod,
          ENNReal.ofReal_mul hF]
    _ ≤ ENNReal.ofReal
          (C * (D.N V + (D.GammaStar V).toReal)) :=
      ENNReal.ofReal_le_ofReal hreal

end ChristodoulouBV.Uniqueness

end
