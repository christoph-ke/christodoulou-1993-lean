module

public import ChristodoulouBV.Uniqueness.IncomingMassFormula
public import ChristodoulouBV.Uniqueness.IncomingHardyEndpoint
public import ChristodoulouBV.Uniqueness.IncomingIStarBound
public import ChristodoulouBV.Uniqueness.ExpansionFirstAbsorption
import ChristodoulouBV.Uniqueness.ZetaGood

/-!
# Incoming mass difference and terminal Hardy estimate

This module collects the corrected terminal-value equation, its decaying
integrating factor, and the representative-stable incoming mass estimate.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- Outgoing continuity transfers the good-ray `ν` norm to every incoming
coordinate, including exceptional values of the frozen representatives. -/
theorem ComparisonData.nu_diff_le_N (D : ComparisonData)
    {V u v : ℝ} (hV : V < D.b)
    (huv : (u, v) ∈ triangle D.a V) :
    |D.S₁.nu u v - D.S₂.nu u v| ≤ D.N V := by
  have hcont₁ := (D.outgoing_continuous_primitives huv.1 hV.le
    D.S₁ (Or.inl rfl)).2.2.2.1
  have hcont₂ := (D.outgoing_continuous_primitives huv.1 hV.le
    D.S₂ (Or.inr rfl)).2.2.2.1
  have hf : ContinuousOn
      (fun t => D.S₁.nu u t - D.S₂.nu u t) (Ioo u V) :=
    hcont₁.sub hcont₂
  apply goodV_continuous_extension (D.goodV_properties).2.1 hf
  · intro t ht htG
    exact D.nu_diff_le_N_good hV.le
      ((mem_triangle).2 ⟨huv.1, ht.1, ht.2⟩) htG
  · exact ⟨huv.2.1, huv.2.2⟩

/-- The incoming scalar quotient norm is nonnegative on each compact top.
The baseline BV field bounds suffice to make its supremum finite. -/
theorem ComparisonData.B_nonneg (D : ComparisonData)
    (ha : D.a = 0) {V : ℝ} (hVb : V ≤ D.b) :
    0 ≤ D.B V := by
  let w := (D.a + D.b) / 2
  have hw : w ∈ Ioo D.a D.b := by
    dsimp [w]
    constructor <;> linarith [D.hab]
  have href : (0, w) ∈ D.U₁ ∩ D.U₂ := by
    simpa only [ha] using D.hT
      ((mem_triangle).2 ⟨le_rfl, hw.1, hw.2⟩)
  have hdata : D.S₁.phi 0 w = D.S₂.phi 0 w := by
    simpa only [ha] using (D.hdata w hw).2
  obtain ⟨c, C₀, hc, hC₀, hfield⟩ :=
    D.h₁.preloc_coefficient_bounds D.h₂ href hdata
  let M := 2 * (C₀ + C₀ / c)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hquot (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂)
      {x y : ℝ} (hxy : (x, y) ∈ triangle D.a V) :
      |S.beta x y / S.nu x y| ≤ C₀ + C₀ / c := by
    have hfull : (x, y) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨hxy.1, hxy.2.1, hxy.2.2.trans_le hVb⟩
    obtain ⟨_, _, hnu, _, hφ, _, hζ⟩ :=
      hfield D.a D.b x y D.hT hfull S hS
    have hnuPos : 0 < |S.nu x y| := hc.trans_le hnu
    have hnuNe : S.nu x y ≠ 0 := abs_pos.mp hnuPos
    have hζdiv : |S.zeta x y / S.nu x y| ≤ C₀ / c := by
      rw [abs_div]
      apply (div_le_div_iff₀ hnuPos hc).2
      have hleft := mul_le_mul_of_nonneg_right hζ hc.le
      have hright := mul_le_mul_of_nonneg_left hnu hC₀
      nlinarith only [hleft, hright]
    have heq : S.beta x y / S.nu x y =
        S.phi x y + S.zeta x y / S.nu x y := by
      unfold Fields.zeta
      field_simp [hnuNe]
      ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add hφ hζdiv)
  have hbound : ∀ x y, (x, y) ∈ triangle D.a V →
      y ∈ D.goodV →
      |D.S₁.beta x y / D.S₁.nu x y -
        D.S₂.beta x y / D.S₂.nu x y| ≤ M := by
    intro x y hxy _
    calc
      _ ≤ |D.S₁.beta x y / D.S₁.nu x y| +
          |D.S₂.beta x y / D.S₂.nu x y| := abs_sub _ _
      _ ≤ (C₀ + C₀ / c) + (C₀ + C₀ / c) :=
        add_le_add (hquot D.S₁ (Or.inl rfl) hxy)
          (hquot D.S₂ (Or.inr rfl) hxy)
      _ = M := by dsimp [M]; ring
  exact D.goodVNorm_nonneg hM hbound

private theorem incoming_mass_forcing_algebra
    {z₁ z₂ nu₂ q mu₂ dr r₁ dnu dz B N C : ℝ}
    (hC : 1 ≤ C) (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hz₂ : |z₂ / nu₂| ≤ C) (hq : |q| ≤ C)
    (hmu₂ : 0 ≤ mu₂ ∧ mu₂ ≤ 1)
    (hdr : |dr / r₁| ≤ C * N)
    (hdnu : |dnu| ≤ N)
    (hdz : |dz| ≤ C * (B + N)) :
    |(z₂ ^ 2 / nu₂) * (mu₂ * (dr / r₁) - q * dnu) +
      q * (z₁ + z₂) * dz| ≤
      3 * C ^ 2 * (B + N) * (|z₁| + |z₂|) := by
  have hC₀ : 0 ≤ C := by linarith
  have hBN : 0 ≤ B + N := add_nonneg hB hN
  have hlead : |z₂ ^ 2 / nu₂| ≤ C * |z₂| := by
    have heq : z₂ ^ 2 / nu₂ = z₂ * (z₂ / nu₂) := by ring
    rw [heq, abs_mul]
    exact (mul_le_mul_of_nonneg_left hz₂ (abs_nonneg _)).trans_eq
      (mul_comm _ _)
  have hqN : |q * dnu| ≤ C * N := by
    rw [abs_mul]
    exact mul_le_mul hq hdnu (abs_nonneg _) hC₀
  have hmuN : |mu₂ * (dr / r₁)| ≤ C * N := by
    rw [abs_mul, abs_of_nonneg hmu₂.1]
    exact (mul_le_mul_of_nonneg_right hmu₂.2 (abs_nonneg _)).trans
      (by simpa only [one_mul] using hdr)
  have hbracket : |mu₂ * (dr / r₁) - q * dnu| ≤ 2 * C * N := by
    calc
      _ ≤ |mu₂ * (dr / r₁)| + |q * dnu| := abs_sub _ _
      _ ≤ C * N + C * N := add_le_add hmuN hqN
      _ = 2 * C * N := by ring
  have hsum : |z₁ + z₂| ≤ |z₁| + |z₂| := abs_add_le _ _
  have hterm₁ :
      |(z₂ ^ 2 / nu₂) * (mu₂ * (dr / r₁) - q * dnu)| ≤
      2 * C ^ 2 * (B + N) * (|z₁| + |z₂|) := by
    rw [abs_mul]
    calc
      |z₂ ^ 2 / nu₂| * |mu₂ * (dr / r₁) - q * dnu| ≤
          (C * |z₂|) * (2 * C * N) :=
        mul_le_mul hlead hbracket (abs_nonneg _) (by positivity)
      _ ≤ (C * (|z₁| + |z₂|)) * (2 * C * (B + N)) := by
        gcongr
        · exact le_add_of_nonneg_left (abs_nonneg _)
        · exact le_add_of_nonneg_left hB
      _ = 2 * C ^ 2 * (B + N) * (|z₁| + |z₂|) := by ring
  have hterm₂ : |q * (z₁ + z₂) * dz| ≤
      C ^ 2 * (B + N) * (|z₁| + |z₂|) := by
    rw [abs_mul, abs_mul]
    calc
      |q| * |z₁ + z₂| * |dz| ≤
          C * (|z₁| + |z₂|) * (C * (B + N)) := by
        gcongr
      _ = C ^ 2 * (B + N) * (|z₁| + |z₂|) := by ring
  calc
    _ ≤ |(z₂ ^ 2 / nu₂) * (mu₂ * (dr / r₁) - q * dnu)| +
        |q * (z₁ + z₂) * dz| := abs_add_le _ _
    _ ≤ 2 * C ^ 2 * (B + N) * (|z₁| + |z₂|) +
        C ^ 2 * (B + N) * (|z₁| + |z₂|) := add_le_add hterm₁ hterm₂
    _ = 3 * C ^ 2 * (B + N) * (|z₁| + |z₂|) := by ring

/-- The corrected incoming forcing is bounded by the stable `B,N` norms
times the paper's `I*` density. The constant and preliminary threshold are
fixed before the compact cutoff. -/
theorem ComparisonData.incoming_mass_forcing_le (D : ComparisonData)
    (ha : D.a = 0) (hb : D.b = 1) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∃ C : ℝ, 1 ≤ C ∧
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀ ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε₀) →
        ∀ V u v, D.a < V → V < D.b →
          (u, v) ∈ triangle D.a V →
          |incomingMassForcing D u v| ≤
            3 * C ^ 2 * (D.B V + D.N V) *
              (|D.S₁.zeta u v| + |D.S₂.zeta u v|)) := by
  obtain ⟨C₀, hC₀, ε₀, hε₀, Cζ, hCζ, hζdiff⟩ := D.zeta_diff_le ha hb
  obtain ⟨d, _, hd, hrad⟩ := D.h₁.exists_uniform_radius_bounds
  obtain ⟨c₁, hc₁, hlam₁⟩ := D.h₁.lam_bounded_below
  obtain ⟨c₂, hc₂, hlam₂⟩ := D.h₂.lam_bounded_below
  let T := max D.h₂.item5.choose 0
  let C := max Cζ (max (1 / d) (max (1 / c₁) (max (T / c₂) 1)))
  have hC : 1 ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _) |>.trans
      (le_max_right _ _) |>.trans (le_max_right _ _)
  have hCpos : 0 ≤ C := by linarith
  have hCζle : Cζ ≤ C := le_max_left _ _
  have hdInv : 1 / d ≤ C :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hc₁Inv : 1 / c₁ ≤ C :=
    (le_max_left _ _).trans (le_max_right _ _) |>.trans
      (le_max_right _ _)
  have hc₂T : T / c₂ ≤ C :=
    (le_max_left _ _).trans (le_max_right _ _) |>.trans
      (le_max_right _ _) |>.trans (le_max_right _ _)
  refine ⟨C₀, hC₀, ε₀, hε₀, C, hC, ?_⟩
  intro hsmall V u v haV hVb huv
  have hfull : (u, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨huv.1, huv.2.1, huv.2.2.trans hVb⟩
  have hp := D.hT hfull
  have hB : 0 ≤ D.B V := D.B_nonneg ha hVb.le
  have hN : 0 ≤ D.N V := D.N_nonneg haV hVb
  have hBN : 0 ≤ D.B V + D.N V := add_nonneg hB hN
  have hmu₁ := D.h₁.mass_ratio_bounds hp.1
  have hmu₂ := D.h₂.mass_ratio_bounds hp.2
  have hnu₁ : D.S₁.nu u v < 0 :=
    lt_of_le_of_lt (D.h₁.nu_le_neg_lower hc₁ hlam₁ hp.1)
      (neg_lt_zero.mpr hc₁)
  have hnu₂ : D.S₂.nu u v < 0 :=
    lt_of_le_of_lt (D.h₂.nu_le_neg_lower hc₂ hlam₂ hp.2)
      (neg_lt_zero.mpr hc₂)
  have hnu₁lo : c₁ ≤ |D.S₁.nu u v| := by
    rw [abs_of_neg hnu₁]
    linarith [D.h₁.nu_le_neg_lower hc₁ hlam₁ hp.1]
  have hnu₂lo : c₂ ≤ |D.S₂.nu u v| := by
    rw [abs_of_neg hnu₂]
    linarith [D.h₂.nu_le_neg_lower hc₂ hlam₂ hp.2]
  have hζ₂ : |D.S₂.zeta u v| ≤ T :=
    D.h₂.zeta_abs_le_global_variation_of_triangle
      (fun p hp => (D.hT hp).2) hfull
  have hζratio : |D.S₂.zeta u v / D.S₂.nu u v| ≤ C := by
    rw [abs_div]
    have hbase : |D.S₂.zeta u v| / |D.S₂.nu u v| ≤ T / c₂ := by
      apply (div_le_div_iff₀ (hc₂.trans_le hnu₂lo) hc₂).2
      have h₁ := mul_le_mul_of_nonneg_right hζ₂ hc₂.le
      have h₂ := mul_le_mul_of_nonneg_left hnu₂lo
        (le_max_right D.h₂.item5.choose 0)
      nlinarith only [h₁, h₂]
    exact hbase.trans hc₂T
  change 0 ≤ IsBVSolution.mu D.S₁ u v ∧
    IsBVSolution.mu D.S₁ u v < 1 at hmu₁
  change 0 ≤ IsBVSolution.mu D.S₂ u v ∧
    IsBVSolution.mu D.S₂ u v < 1 at hmu₂
  have hgap : 0 ≤ 1 - IsBVSolution.mu D.S₁ u v ∧
      1 - IsBVSolution.mu D.S₁ u v ≤ 1 := by
    constructor <;> linarith only [hmu₁.1, hmu₁.2]
  have hq : |(1 - IsBVSolution.mu D.S₁ u v) / D.S₁.nu u v| ≤ C := by
    rw [abs_div, abs_of_nonneg hgap.1]
    have hbase : (1 - IsBVSolution.mu D.S₁ u v) / |D.S₁.nu u v| ≤
        1 / c₁ := by
      apply (div_le_div_iff₀ (hc₁.trans_le hnu₁lo) hc₁).2
      have h₁ := mul_le_mul_of_nonneg_right hgap.2 hc₁.le
      have h₂ := hnu₁lo
      nlinarith only [h₁, h₂]
    exact hbase.trans hc₁Inv
  have hrpos := D.h₁.solution.radius_pos (u, v) hp.1
  have hdist : 0 < v - u := sub_pos.mpr huv.2.1
  have hdr : |(D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v| ≤
      C * D.N V := by
    rw [abs_div, abs_of_pos hrpos]
    have hrlo := (hrad u v hp.1).1
    have hdiff := D.radius_diff_le_N hVb huv
    have hbase : |D.S₁.r u v - D.S₂.r u v| / D.S₁.r u v ≤
        (1 / d) * D.N V := by
      apply (div_le_iff₀ hrpos).2
      have hprod := mul_le_mul_of_nonneg_right hrlo hN
      have hdiff' := mul_le_mul_of_nonneg_left hdiff hd.le
      have hdne : d ≠ 0 := hd.ne'
      field_simp [hdne]
      nlinarith only [hprod, hdiff']
    exact hbase.trans (mul_le_mul_of_nonneg_right hdInv hN)
  have hdnu : |D.S₁.nu u v - D.S₂.nu u v| ≤ D.N V :=
    D.nu_diff_le_N hVb huv
  have hdz : |D.S₁.zeta u v - D.S₂.zeta u v| ≤
      C * (D.B V + D.N V) :=
    (hζdiff hsmall V u v hVb huv).trans
      (mul_le_mul_of_nonneg_right hCζle hBN)
  have hmu₂' : 0 ≤ IsBVSolution.mu D.S₂ u v ∧
      IsBVSolution.mu D.S₂ u v ≤ 1 := ⟨hmu₂.1, hmu₂.2.le⟩
  have halg := incoming_mass_forcing_algebra
    (z₁ := D.S₁.zeta u v) hC hB hN
    hζratio hq hmu₂' hdr hdnu hdz
  simpa only [incomingMassForcing] using halg

/-- The decaying terminal factor turns the corrected mass equation into the
source estimate `|Δm| ≤ C(B+N) I*`, uniformly in the compact top. -/
theorem ComparisonData.mass_in_difference_le_IStar (D : ComparisonData)
    (ha : D.a = 0) (hb : D.b = 1) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∃ C : ℝ, 1 ≤ C ∧
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀ ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε₀) →
        ∀ V u v, D.a < V → V < D.b →
          (u, v) ∈ triangle D.a V →
          |D.S₁.m u v - D.S₂.m u v| ≤
            C * (D.B V + D.N V) * IStar D u v) := by
  obtain ⟨C₀, hC₀, ε₀, hε₀, Cforce, hCforce, hforce⟩ :=
    D.incoming_mass_forcing_le ha hb
  let C := 3 * Cforce ^ 2
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [sq_nonneg Cforce]
  refine ⟨C₀, hC₀, ε₀, hε₀, C, hC, ?_⟩
  intro hsmall V u v haV hVb huv
  have hfull : (u, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨huv.1, huv.2.1, huv.2.2.trans hVb⟩
  have hT₁ : triangle D.a D.b ⊆ D.U₁ := fun p hp => (D.hT hp).1
  have hT₂ : triangle D.a D.b ⊆ D.U₂ := fun p hp => (D.hT hp).2
  have hf₁ := zeta_abs_integrable D.h₁ hT₁ hfull
  have hf₂ := zeta_abs_integrable D.h₂ hT₂ hfull
  have hf : IntervalIntegrable
      (fun s => |D.S₁.zeta s v| + |D.S₂.zeta s v|) volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huv.2.1.le).2
      (hf₁.add hf₂)
  have hFhalf := D.incomingMassForcing_integrable hfull
  have hF : IntervalIntegrable (fun s => incomingMassForcing D s v)
      volume u v := by
    have hh := hFhalf.const_mul 2
    convert hh using 1
    funext s
    ring
  let k : ℝ → ℝ := fun s => D.S₂.zeta s v ^ 2 /
    (D.S₂.nu s v * D.S₁.r s v)
  have hk : IntervalIntegrable k volume u v := by
    have hh := (D.incomingMassCoefficient_integrable hfull).neg
    convert hh using 1
    funext s
    unfold k incomingMassCoefficient
    simp
  let E : ℝ → ℝ := fun s => Real.exp (∫ t in u..s, k t)
  have hE : AbsolutelyContinuousOnInterval E u v :=
    (hk.absolutelyContinuousOnInterval_intervalIntegral (by simp)).exp
  have hEF : IntervalIntegrable (fun s => E s * incomingMassForcing D s v)
      volume u v := hF.continuousOn_mul hE.continuousOn
  have hBN : 0 ≤ D.B V + D.N V :=
    add_nonneg (D.B_nonneg ha hVb.le) (D.N_nonneg haV hVb)
  have hconst : 0 ≤ C * (D.B V + D.N V) :=
    mul_nonneg (by linarith) hBN
  have hbound : ∀ s ∈ Ioo u v,
      |E s * incomingMassForcing D s v| ≤
        C * (D.B V + D.N V) *
          (|D.S₁.zeta s v| + |D.S₂.zeta s v|) := by
    intro s hs
    have hst : (s, v) ∈ triangle D.a V :=
      (mem_triangle).2 ⟨huv.1.trans hs.1.le, hs.2, huv.2.2⟩
    have hfactor := D.incoming_mass_factor_le_one hfull
      (show s ∈ Icc u v from ⟨hs.1.le, hs.2.le⟩)
    have hforce' := hforce hsmall V s v haV hVb hst
    calc
      |E s * incomingMassForcing D s v| =
          E s * |incomingMassForcing D s v| := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ |incomingMassForcing D s v| := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hfactor (abs_nonneg _)
      _ ≤ C * (D.B V + D.N V) *
          (|D.S₁.zeta s v| + |D.S₂.zeta s v|) := hforce'
  have hI : (∫ s in u..v, |E s * incomingMassForcing D s v|) ≤
      C * (D.B V + D.N V) * IStar D u v := by
    have hright : IntervalIntegrable
        (fun s => C * (D.B V + D.N V) *
          (|D.S₁.zeta s v| + |D.S₂.zeta s v|)) volume u v :=
      hf.const_mul _
    have hh := intervalIntegral.integral_mono_on_of_le_Ioo
      huv.2.1.le hEF.abs hright hbound
    rw [intervalIntegral.integral_const_mul] at hh
    exact hh
  have hmass := D.mass_in_terminal_formula hfull
  rw [hmass, abs_mul, abs_neg, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  have hInt := intervalIntegral.abs_integral_le_integral_abs (μ := volume) huv.2.1.le
    (f := fun s => E s * incomingMassForcing D s v)
  have hIstar : 0 ≤ IStar D u v := by
    unfold IStar
    apply intervalIntegral.integral_nonneg huv.2.1.le
    intro s _
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hright : 0 ≤ C * (D.B V + D.N V) * IStar D u v :=
    mul_nonneg hconst hIstar
  change (1 / 2 : ℝ) *
    |∫ s in u..v, E s * incomingMassForcing D s v| ≤
      C * (D.B V + D.N V) * IStar D u v
  calc
    (1 / 2 : ℝ) * |∫ s in u..v, E s * incomingMassForcing D s v| ≤
        (1 / 2 : ℝ) * (∫ s in u..v,
          |E s * incomingMassForcing D s v|) :=
      mul_le_mul_of_nonneg_left hInt (by norm_num)
    _ ≤ (1 / 2 : ℝ) *
        (C * (D.B V + D.N V) * IStar D u v) :=
      mul_le_mul_of_nonneg_left hI (by norm_num)
    _ ≤ C * (D.B V + D.N V) * IStar D u v := by
      linarith only [hright]

/-- The stable incoming mass Hardy estimate on the full comparison triangle.
The incoming axis is available to both developments and both terminal mass
traces vanish. The coefficient is fixed before the variation and cutoff. -/
theorem ComparisonData.GammaStar_le_epsilon_B_N (D : ComparisonData)
    (ha : D.a = 0) (hb : D.b = 1) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
        (∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε) →
        ∀ V, D.a < V → V < D.b →
          D.GammaStar V ≤ ENNReal.ofReal (C * ε * (D.B V + D.N V)) ∧
          (∀ v ∈ Ioo D.a V,
            (∀ u ∈ Ico D.a v, (u, v) ∈ D.U₁ ∧ (u, v) ∈ D.U₂) ∧
            Tendsto (fun u => D.S₁.m u v) (𝓝[<] v) (𝓝 (0 : ℝ)) ∧
            Tendsto (fun u => D.S₂.m u v) (𝓝[<] v) (𝓝 (0 : ℝ))) := by
  obtain ⟨C₀, hC₀, ε₀, hε₀, Cm, hCm, hmass⟩ :=
    D.mass_in_difference_le_IStar ha hb
  obtain ⟨K, hK, hHardy⟩ := D.IStar_hardy_le_local_variation
  let C := max (Cm * K) 1
  have hC : 1 ≤ C := le_max_right _ _
  refine ⟨C₀, hC₀, ε₀, hε₀, C, hC, ?_⟩
  intro ε hε hε₀ hsmall V haV hVb
  have hsmall₀ : ∀ u v, (u, v) ∈ triangle D.a D.b →
      ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
        (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀ ∧
        (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε₀ := by
    intro u v huv S hS
    obtain ⟨hout, hin⟩ := hsmall u v huv S hS
    exact ⟨hout.trans hε₀, hin.trans hε₀⟩
  have hBN : 0 ≤ D.B V + D.N V :=
    add_nonneg (D.B_nonneg ha hVb.le) (D.N_nonneg haV hVb)
  let T := Cm * (D.B V + D.N V)
  have hT : 0 ≤ T := mul_nonneg (by linarith) hBN
  constructor
  · unfold ComparisonData.GammaStar
    apply iSup_le
    intro v
    apply iSup_le
    intro hv
    have hav : (D.a, v) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨le_rfl, hv.1, hv.2.trans hVb⟩
    have hvar₁ := (hsmall D.a v hav D.S₁ (Or.inl rfl)).2
    have hvar₂ := (hsmall D.a v hav D.S₂ (Or.inr rfl)).2
    have hHardy' := hHardy D.a v ε hav hvar₁ hvar₂
    rw [← restrict_Ico_eq_restrict_Ioc] at hHardy'
    have hpoint : ∀ u ∈ Ico D.a v,
        ENNReal.ofReal
          (|D.S₁.m u v - D.S₂.m u v| / (v - u) ^ 2) ≤
          ENNReal.ofReal T *
            ENNReal.ofReal (IStar D u v / (v - u) ^ 2) := by
      intro u hu
      have huv : (u, v) ∈ triangle D.a V :=
        (mem_triangle).2 ⟨hu.1, hu.2, hv.2⟩
      have hmass' := hmass hsmall₀ V u v haV hVb huv
      have hden : 0 ≤ (v - u) ^ 2 := sq_nonneg _
      have hreal : |D.S₁.m u v - D.S₂.m u v| / (v - u) ^ 2 ≤
          T * (IStar D u v / (v - u) ^ 2) := by
        calc
          _ ≤ (T * IStar D u v) / (v - u) ^ 2 :=
            div_le_div_of_nonneg_right hmass' hden
          _ = T * (IStar D u v / (v - u) ^ 2) := by ring
      rw [← ENNReal.ofReal_mul hT]
      exact ENNReal.ofReal_le_ofReal hreal
    have hCmk : Cm * K ≤ C := le_max_left _ _
    have hrealFinal : T * (K * ε) ≤ C * ε * (D.B V + D.N V) := by
      calc
        T * (K * ε) = (Cm * K * ε) * (D.B V + D.N V) := by
          dsimp [T]
          ring
        _ ≤ (C * ε) * (D.B V + D.N V) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCmk hε) hBN
        _ = C * ε * (D.B V + D.N V) := rfl
    calc
      (∫⁻ u in Ico D.a v, ENNReal.ofReal
        (|D.S₁.m u v - D.S₂.m u v| / (v - u) ^ 2)) ≤
          ∫⁻ u in Ico D.a v, ENNReal.ofReal T *
            ENNReal.ofReal (IStar D u v / (v - u) ^ 2) := by
        apply lintegral_mono_ae
        exact ae_restrict_of_forall_mem measurableSet_Ico hpoint
      _ = ENNReal.ofReal T *
          (∫⁻ u in Ico D.a v, ENNReal.ofReal
            (IStar D u v / (v - u) ^ 2)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal T * ENNReal.ofReal (K * ε) := by
        gcongr
      _ = ENNReal.ofReal (T * (K * ε)) := by
        rw [ENNReal.ofReal_mul hT]
      _ ≤ ENNReal.ofReal (C * ε * (D.B V + D.N V)) :=
        ENNReal.ofReal_le_ofReal hrealFinal
  · intro v hv
    have hav : (D.a, v) ∈ triangle D.a D.b :=
      (mem_triangle).2 ⟨le_rfl, hv.1, hv.2.trans hVb⟩
    have hT₁ : triangle D.a D.b ⊆ D.U₁ :=
      fun p hp => (D.hT hp).1
    have hT₂ : triangle D.a D.b ⊆ D.U₂ :=
      fun p hp => (D.hT hp).2
    exact ⟨fun u hu => ⟨
        IsBVSolution.incoming_axis_access_of_triangle hT₁ hav u hu,
        IsBVSolution.incoming_axis_access_of_triangle hT₂ hav u hu⟩,
      IsBVSolution.incoming_mass_axis_trace_of_triangle D.h₁ hT₁ hav,
      IsBVSolution.incoming_mass_axis_trace_of_triangle D.h₂ hT₂ hav⟩

end ChristodoulouBV.Uniqueness

end
