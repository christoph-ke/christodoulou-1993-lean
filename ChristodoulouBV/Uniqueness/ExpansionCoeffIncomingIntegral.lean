module

public import ChristodoulouBV.Uniqueness.ExpansionCoeffIntegrals

/-!
# Incoming coefficient-difference integral

The terminal-axis mass norm and the unsigned incoming coefficient estimate
give the incoming expansion transport error. Every incoming ray used here is
contained in the full comparison triangle.
-/

@[expose] public section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.Uniqueness

/-- The incoming weighted mass difference is integrable up to the excluded
terminal axis on a full comparison triangle. -/
theorem ComparisonData.incoming_mass_diff_weight_integrable
    (D : ComparisonData) {v : ℝ} (hav : D.a < v) (hvb : v < D.b) :
    IntegrableOn (fun s =>
      |D.S₁.m s v - D.S₂.m s v| / (v - s) ^ 2) (Ico D.a v) volume := by
  have hpoint : (D.a, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨le_rfl, hav, hvb⟩
  have hT₁ : triangle D.a D.b ⊆ D.U₁ := fun p hp => (D.hT hp).1
  have hT₂ : triangle D.a D.b ⊆ D.U₂ := fun p hp => (D.hT hp).2
  have h₁ := incoming_mass_div_sq_integrable D.h₁ hT₁ hpoint
  have h₂ := incoming_mass_div_sq_integrable D.h₂ hT₂ hpoint
  have heq : (fun s => |D.S₁.m s v / (v - s) ^ 2 -
      D.S₂.m s v / (v - s) ^ 2|) =
      (fun s => |D.S₁.m s v - D.S₂.m s v| / (v - s) ^ 2) := by
    funext s
    rw [← sub_div, abs_div]
    simp only [abs_of_nonneg (sq_nonneg (v - s))]
  rw [← heq]
  exact (h₁.sub h₂).abs

/-- The incoming weighted mass integral on one complete characteristic lies
below the finite extended norm `Γ*` at every later compact top. -/
theorem ComparisonData.incoming_mass_diff_integral_le_GammaStar
    (D : ComparisonData) {V v : ℝ}
    (hv : v ∈ Ioo D.a V) (hVb : V < D.b) :
    (∫ s in Ioc D.a v,
      |D.S₁.m s v - D.S₂.m s v| / (v - s) ^ 2) ≤
      (D.GammaStar V).toReal := by
  have hvb : v < D.b := hv.2.trans hVb
  have hint := D.incoming_mass_diff_weight_integrable hv.1 hvb
  let mass : ℝ → ℝ := fun s =>
    |D.S₁.m s v - D.S₂.m s v| / (v - s) ^ 2
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ico D.a v)] mass := by
    apply ae_restrict_of_forall_mem measurableSet_Ico
    intro s _
    exact div_nonneg (abs_nonneg _) (sq_nonneg _)
  have hreal : 0 ≤ ∫ s in Ico D.a v, mass s :=
    integral_nonneg_of_ae hnonneg
  have heq := ofReal_integral_eq_lintegral_ofReal hint hnonneg
  have hlin : (∫⁻ s in Ico D.a v,
      ENNReal.ofReal (mass s)) ≤ D.GammaStar V := by
    unfold ComparisonData.GammaStar
    exact le_iSup_of_le v (le_iSup_of_le hv le_rfl)
  obtain ⟨M, _, hM⟩ := D.GammaStar_uniform_bound
  have hfinite : D.GammaStar V ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hM V (hv.1.trans hv.2) hVb)
  have hle := ENNReal.toReal_mono hfinite (heq.trans_le hlin)
  rw [ENNReal.toReal_ofReal hreal] at hle
  simpa only [restrict_Ico_eq_restrict_Ioc] using hle

/-- A fixed quotient bound makes both incoming logarithmic coefficients
integrable on the complete incoming ray. The bound needs no local smallness. -/
theorem ComparisonData.incomingCoeff_integrable_pair (D : ComparisonData)
    (ha : D.a = 0) :
    ∀ v ∈ Ioo D.a D.b,
      IntegrableOn (IsBVSolution.incomingCoeff D.S₁ · v) (Ioc D.a v) volume ∧
      IntegrableOn (IsBVSolution.incomingCoeff D.S₂ · v) (Ioc D.a v) volume := by
  let w := (D.a + D.b) / 2
  have hw : w ∈ Ioo D.a D.b := by dsimp [w]; constructor <;> linarith [D.hab]
  have hpoint : (D.a, w) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨le_rfl, hw.1, hw.2⟩
  have href : (0, w) ∈ D.U₁ ∩ D.U₂ := by
    simpa only [ha] using D.hT hpoint
  have hdata : D.S₁.phi 0 w = D.S₂.phi 0 w := by
    simpa only [ha] using (D.hdata w hw).2
  obtain ⟨c, C₀, hc, hC₀, hfield⟩ :=
    D.h₁.preloc_coefficient_bounds D.h₂ href hdata
  let Q := C₀ / c
  have hQ : 0 ≤ Q := div_nonneg hC₀ hc.le
  intro v hv
  have hquot : ∀ s ∈ Ico D.a v, ∀ S : Fields,
      (S = D.S₁ ∨ S = D.S₂) → |S.zeta s v / S.nu s v| ≤ Q := by
    intro s hs S hS
    have hspt : (s, v) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨hs.1, hs.2, hv.2⟩
    obtain ⟨_, _, hnu, _, _, _, hzeta⟩ :=
      hfield D.a D.b s v D.hT hspt S hS
    have hnupos : 0 < |S.nu s v| := hc.trans_le hnu
    rw [abs_div]
    apply (div_le_iff₀ hnupos).2
    calc
      |S.zeta s v| ≤ C₀ := hzeta
      _ = Q * c := by dsimp [Q]; field_simp [hc.ne']
      _ ≤ Q * |S.nu s v| := mul_le_mul_of_nonneg_left hnu hQ
  have haccess : ∀ s ∈ Ico D.a v, (s, v) ∈ D.U₁ ∩ D.U₂ := by
    intro s hs
    exact D.hT ((mem_triangle).2 ⟨hs.1, hs.2, hv.2⟩)
  exact ⟨D.h₁.incomingCoeff_integrable_axis hv.1
      (fun s hs => (haccess s hs).1)
      (fun s hs => hquot s hs D.S₁ (Or.inl rfl)),
    D.h₂.incomingCoeff_integrable_axis hv.1
      (fun s hs => (haccess s hs).2)
      (fun s hs => hquot s hs D.S₂ (Or.inr rfl))⟩

/-- The absolute incoming coefficient
difference is controlled by `ε N + Γ*` on every good incoming ray. The
constant is fixed before the final variation size and compact cutoff. -/
theorem ComparisonData.incomingCoeff_difference_integral_uniform
    (D : ComparisonData) (ha : D.a = 0) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∃ C₁ : ℝ, 4 ≤ C₁ ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
          (∀ u v, (u, v) ∈ triangle D.a D.b →
            ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
              (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε ∧
              (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε) →
          ∀ V, D.a < V → V < D.b →
            ∀ v ∈ Ioo D.a V, v ∈ D.goodV →
              (∫ s in D.a..v,
                |IsBVSolution.incomingCoeff D.S₁ s v -
                  IsBVSolution.incomingCoeff D.S₂ s v|) ≤
                C * (ε * D.N V + (D.GammaStar V).toReal) := by
  let w := (D.a + D.b) / 2
  have hw : w ∈ Ioo D.a D.b := by dsimp [w]; constructor <;> linarith [D.hab]
  have hpoint₀ : (D.a, w) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨le_rfl, hw.1, hw.2⟩
  have href : (0, w) ∈ D.U₁ ∩ D.U₂ := by
    simpa only [ha] using D.hT hpoint₀
  have hdata : D.S₁.phi 0 w = D.S₂.phi 0 w := by
    simpa only [ha] using (D.hdata w hw).2
  obtain ⟨J, hJ, husable⟩ := D.h₁.eq3_12_usable D.h₂ href hdata
  obtain ⟨C₀, hC₀, ε₀, hε₀, C₁, hC₁, hpoint⟩ :=
    D.expansion_coefficient_pointwise_uniform ha
  let F := C₁ ^ 2 + (C₁ ^ 2) ^ 2 + (C₁ ^ 2) ^ 4
  let B := 2 * (C₁ ^ 2) ^ 5
  let C := max (F * J) B + 1
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 1 ≤ C := by
    dsimp [C]
    have : 0 ≤ F * J := mul_nonneg hF hJ
    linarith [le_max_left (F * J) B]
  refine ⟨C₀, hC₀, ε₀, hε₀, C₁, hC₁, C, hC, ?_⟩
  intro ε hε hε₀le hsmall V haV hVb v hv hvG
  have hvb : v < D.b := hv.2.trans hVb
  have hpre : ∀ u v, (u, v) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀ ∧
        (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε₀ := by
    intro u' v' hp S hS
    have hh := hsmall u' v' hp S hS
    exact ⟨hh.1.trans hε₀le, hh.2.trans hε₀le⟩
  have hN : 0 ≤ D.N V := D.N_nonneg haV hVb
  have hΓ : 0 ≤ (D.GammaStar V).toReal := ENNReal.toReal_nonneg
  have hK := D.incomingCoeff_integrable_pair ha v ⟨hv.1, hvb⟩
  have hK₁ := hK.1
  have hK₂ := hK.2
  have hdiff : IntegrableOn (fun s =>
      |IsBVSolution.incomingCoeff D.S₁ s v -
        IsBVSolution.incomingCoeff D.S₂ s v|) (Ioc D.a v) volume :=
    (hK₁.sub hK₂).abs
  have hmassIco := D.incoming_mass_diff_weight_integrable hv.1 hvb
  let mass : ℝ → ℝ := fun s =>
    |D.S₁.m s v - D.S₂.m s v| / (v - s) ^ 2
  have hmass : IntegrableOn mass (Ioc D.a v) volume := by
    change Integrable mass (volume.restrict (Ioc D.a v))
    rw [← restrict_Ico_eq_restrict_Ioc]
    exact hmassIco
  have hRhs : IntegrableOn (fun s =>
      F * D.N V * (-IsBVSolution.incomingCoeff D.S₂ s v) +
        B * mass s) (Ioc D.a v) volume :=
    (hK₂.neg.const_mul (F * D.N V)).add (hmass.const_mul B)
  have hneg : IntegrableOn (fun s =>
      -IsBVSolution.incomingCoeff D.S₂ s v) (Ioc D.a v) volume := hK₂.neg
  have hae : ∀ᵐ s ∂volume.restrict (Ioc D.a v),
      |IsBVSolution.incomingCoeff D.S₁ s v -
        IsBVSolution.incomingCoeff D.S₂ s v| ≤
      F * D.N V * (-IsBVSolution.incomingCoeff D.S₂ s v) +
        B * mass s := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    have hne : ∀ᵐ s : ℝ ∂volume, s ≠ v := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with s hsne hs
    have hst : (s, v) ∈ triangle D.a V :=
      (mem_triangle).2 ⟨hs.1.le, lt_of_le_of_ne hs.2 hsne, hv.2⟩
    exact (hpoint hpre V haV hVb s v hst hvG).2
  have hle := integral_mono_ae hdiff hRhs hae
  have hsum : (∫ s in Ioc D.a v,
      F * D.N V * (-IsBVSolution.incomingCoeff D.S₂ s v) +
        B * mass s) =
      F * D.N V * (∫ s in Ioc D.a v,
        -IsBVSolution.incomingCoeff D.S₂ s v) +
      B * (∫ s in Ioc D.a v, mass s) := by
    rw [integral_add (hneg.const_mul (F * D.N V))
      (hmass.const_mul B), integral_const_mul, integral_const_mul]
  have hpointv : (D.a, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨le_rfl, hv.1, hvb⟩
  have hY := (hsmall D.a v hpointv D.S₂ (Or.inr rfl)).2
  have hcoef : (∫ s in Ioc D.a v,
      -IsBVSolution.incomingCoeff D.S₂ s v) ≤ J * ε := by
    have hh := husable ε hε D.a D.b D.a v D.hT hpointv
      D.S₂ (Or.inr rfl) hY
    change -(∫ s in D.a..v,
      IsBVSolution.incomingCoeff D.S₂ s v) ≤ J * ε at hh
    rw [intervalIntegral.integral_of_le hv.1.le] at hh
    rw [integral_neg]
    exact hh
  have hmassbound : (∫ s in Ioc D.a v, mass s) ≤
      (D.GammaStar V).toReal :=
    D.incoming_mass_diff_integral_le_GammaStar hv hVb
  have hFJ : F * J ≤ C := by
    dsimp [C]
    linarith [le_max_left (F * J) B]
  have hBC : B ≤ C := by dsimp [C]; linarith [le_max_right (F * J) B]
  have hstep₁ := mul_le_mul_of_nonneg_left hcoef (mul_nonneg hF hN)
  have hstep₂ := mul_le_mul_of_nonneg_left hmassbound hB
  have hεN : 0 ≤ ε * D.N V := mul_nonneg hε hN
  have hstep₃ := mul_le_mul_of_nonneg_right hFJ hεN
  have hstep₄ := mul_le_mul_of_nonneg_right hBC hΓ
  rw [intervalIntegral.integral_of_le hv.1.le]
  calc
    (∫ s in Ioc D.a v,
      |IsBVSolution.incomingCoeff D.S₁ s v -
        IsBVSolution.incomingCoeff D.S₂ s v|) ≤
      F * D.N V * (∫ s in Ioc D.a v,
        -IsBVSolution.incomingCoeff D.S₂ s v) +
      B * (∫ s in Ioc D.a v, mass s) := by rw [← hsum]; exact hle
    _ ≤ F * D.N V * (J * ε) +
        B * (D.GammaStar V).toReal := by linarith
    _ ≤ C * (ε * D.N V + (D.GammaStar V).toReal) := by nlinarith

end ChristodoulouBV.Uniqueness

end
