module

public import ChristodoulouBV.Uniqueness.UniformThresholdZetaGood
public import ChristodoulouBV.Uniqueness.IncomingMassHardy

/-!
# Package-uniform incoming mass forcing

The incoming forcing coefficient is selected from the package field and
radius bounds before normalized comparison data are selected.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace ChristodoulouBV.Uniqueness

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
theorem UniformThresholdBounds.incoming_mass_forcing_le
    (P : UniformThresholdBounds) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ P.gapThreshold) →
        ∀ V u v, D.a < V → V < D.b →
          (u, v) ∈ triangle D.a V →
          |incomingMassForcing D u v| ≤
            3 * C ^ 2 * (D.B V + D.N V) *
              (|D.S₁.zeta u v| + |D.S₂.zeta u v|)) := by
  obtain ⟨Cζ, hCζ, hζdiff⟩ := P.zeta_diff_le
  let d := P.radiusLower
  let c₁ := P.c
  let c₂ := P.c
  let T := P.C
  have hd : 0 < d := P.radiusLower_pos
  have hc₁ : 0 < c₁ := P.c_pos
  have hc₂ : 0 < c₂ := P.c_pos
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
  refine ⟨C, hC, ?_⟩
  intro D ha hb hP hsmall V u v haV hVb huv
  have hfull : (u, v) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨huv.1, huv.2.1, huv.2.2.trans hVb⟩
  have hp := D.hT hfull
  have hfull' : (u, v) ∈ triangle 0 1 := by
    simpa only [ha, hb] using hfull
  obtain ⟨_, _, hnu₁lo, _, _, _, _, hradloP, _⟩ :=
    hP u v hfull' D.S₁ (Or.inl rfl)
  obtain ⟨_, _, hnu₂lo, _, _, _, hζ₂, _, _⟩ :=
    hP u v hfull' D.S₂ (Or.inr rfl)
  have hB : 0 ≤ D.B V := D.B_nonneg ha hVb.le
  have hN : 0 ≤ D.N V := D.N_nonneg haV hVb
  have hBN : 0 ≤ D.B V + D.N V := add_nonneg hB hN
  have hmu₁ := D.h₁.mass_ratio_bounds hp.1
  have hmu₂ := D.h₂.mass_ratio_bounds hp.2
  have hζratio : |D.S₂.zeta u v / D.S₂.nu u v| ≤ C := by
    rw [abs_div]
    have hbase : |D.S₂.zeta u v| / |D.S₂.nu u v| ≤ T / c₂ := by
      apply (div_le_div_iff₀ (hc₂.trans_le hnu₂lo) hc₂).2
      have h₁ := mul_le_mul_of_nonneg_right hζ₂ hc₂.le
      have h₂ := mul_le_mul_of_nonneg_left hnu₂lo P.C_nonneg
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
    have hrlo := hradloP
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
    (hζdiff D ha hb hP hsmall V u v hVb huv).trans
      (mul_le_mul_of_nonneg_right hCζle hBN)
  have hmu₂' : 0 ≤ IsBVSolution.mu D.S₂ u v ∧
      IsBVSolution.mu D.S₂ u v ≤ 1 := ⟨hmu₂.1, hmu₂.2.le⟩
  have halg := incoming_mass_forcing_algebra
    (z₁ := D.S₁.zeta u v) hC hB hN
    hζratio hq hmu₂' hdr hdnu hdz
  simpa only [incomingMassForcing] using halg


end ChristodoulouBV.Uniqueness

end
