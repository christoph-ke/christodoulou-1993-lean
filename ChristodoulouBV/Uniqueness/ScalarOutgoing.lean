module

public import ChristodoulouBV.Uniqueness.RadiusScalarBase

/-!
# Outgoing scalar comparison estimate

The quotient and expansion norms are evaluated only on the fixed good-v set.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- Under the preliminary coefficient choice, the scalar difference is
controlled on every compact top by the outgoing good-ray quotient and
expansion norms. The same choice works uniformly as the top rises. -/
theorem ComparisonData.phi_diff_outgoing_le (D : ComparisonData)
    (ha : D.a = 0) (hb : D.b = 1) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∃ C₁ : ℝ, 4 ≤ C₁ ∧
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀ ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε₀) →
          ∀ V u v, V < D.b → (u, v) ∈ triangle D.a V →
            |D.S₁.phi u v - D.S₂.phi u v| ≤
              2 * C₁ ^ 2 * (D.A V + D.L V)) := by
  have hw : (D.a, (1 / 2 : ℝ)) ∈ triangle D.a D.b := by
    rw [ha, hb]
    exact initial_edge_of_triangle (by norm_num) (by norm_num)
  have href : (0, (1 / 2 : ℝ)) ∈ D.U₁ ∩ D.U₂ := by
    simpa only [ha] using D.hT hw
  have hdatum : D.S₁.phi 0 (1 / 2 : ℝ) = D.S₂.phi 0 (1 / 2 : ℝ) := by
    have hh := (D.hdata (1 / 2 : ℝ) (by rw [ha, hb]; constructor <;> norm_num)).2
    simpa only [ha] using hh
  obtain ⟨C₀, hC₀, ε₀, hε₀, C₁, hC₁, hcoeff⟩ :=
    D.h₁.coefficient_bounds D.h₂ href hdatum
  refine ⟨C₀, hC₀, ε₀, hε₀, C₁, hC₁, ?_⟩
  intro hsmall V u v hVb huv
  have hCpos : 0 < C₁ := by linarith
  have htwo : 0 ≤ 2 * C₁ := by linarith
  have hfield (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V)
      (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :=
    hcoeff D.a D.b D.hT hsmall x y
      ((mem_triangle).2 ⟨hxy.1, hxy.2.1, hxy.2.2.trans hVb⟩) S hS
  have hbg (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V) :
      |D.S₁.lam x y| ≤ C₁ ∧ |D.S₂.lam x y| ≤ C₁ ∧
      |D.S₁.alpha x y / D.S₁.lam x y| ≤ C₁ ∧
      |D.S₂.alpha x y / D.S₂.lam x y| ≤ C₁ ∧
      |D.S₂.phi x y| ≤ C₁ ∧
      1 / C₁ ≤ D.S₁.r x y / (y - x) := by
    have hp := D.hT ((mem_triangle).2
      ⟨hxy.1, hxy.2.1, hxy.2.2.trans hVb⟩)
    rcases hfield x y hxy D.S₁ (Or.inl rfl) with
      ⟨_, hlam₁, _, _, _, _, _, hrlo, _, _, _, _, _, hq₁, _, _, _, _, _, _⟩
    rcases hfield x y hxy D.S₂ (Or.inr rfl) with
      ⟨_, hlam₂, _, _, hphi₂, _, _, _, _, _, _, _, _, hq₂, _, _, _, _, _, _⟩
    have hp₁ := D.h₁.solution.lam_pos (x, y) hp.1
    have hp₂ := D.h₂.solution.lam_pos (x, y) hp.2
    exact ⟨by simpa only [abs_of_pos hp₁] using hlam₁,
      by simpa only [abs_of_pos hp₂] using hlam₂,
      hq₁, hq₂, hphi₂, hrlo⟩
  have hLbound (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V)
      (_hyG : y ∈ D.goodV) :
      |D.S₁.lam x y - D.S₂.lam x y| ≤ 2 * C₁ := by
    have h := hbg x y hxy
    calc
      |D.S₁.lam x y - D.S₂.lam x y| ≤
          |D.S₁.lam x y| + |D.S₂.lam x y| := abs_sub _ _
      _ ≤ C₁ + C₁ := add_le_add h.1 h.2.1
      _ = 2 * C₁ := by ring
  have hAbound (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V)
      (_hyG : y ∈ D.goodV) :
      |D.S₁.alpha x y / D.S₁.lam x y -
        D.S₂.alpha x y / D.S₂.lam x y| ≤ 2 * C₁ := by
    have h := hbg x y hxy
    calc
      |D.S₁.alpha x y / D.S₁.lam x y -
        D.S₂.alpha x y / D.S₂.lam x y| ≤
          |D.S₁.alpha x y / D.S₁.lam x y| +
          |D.S₂.alpha x y / D.S₂.lam x y| := abs_sub _ _
      _ ≤ C₁ + C₁ := add_le_add h.2.2.1 h.2.2.2.1
      _ = 2 * C₁ := by ring
  have hLpoint (x y : ℝ) (hxy : (x,y) ∈ triangle D.a V)
      (hyG : y ∈ D.goodV) :
      |D.S₁.lam x y - D.S₂.lam x y| ≤ D.L V :=
    D.le_goodVNorm (V := V)
      (f := fun s t => D.S₁.lam s t - D.S₂.lam s t)
      htwo hLbound hxy hyG
  have hApoint (x y : ℝ) (hxy : (x,y) ∈ triangle D.a V)
      (hyG : y ∈ D.goodV) :
      |D.S₁.alpha x y / D.S₁.lam x y -
        D.S₂.alpha x y / D.S₂.lam x y| ≤ D.A V :=
    D.le_goodVNorm (V := V)
      (f := fun s t => D.S₁.alpha s t / D.S₁.lam s t -
        D.S₂.alpha s t / D.S₂.lam s t)
      htwo hAbound hxy hyG
  have hL0 : 0 ≤ D.L V :=
    D.goodVNorm_nonneg (V := V)
      (f := fun s t => D.S₁.lam s t - D.S₂.lam s t)
      htwo hLbound
  have hA0 : 0 ≤ D.A V :=
    D.goodVNorm_nonneg (V := V)
      (f := fun s t => D.S₁.alpha s t / D.S₁.lam s t -
        D.S₂.alpha s t / D.S₂.lam s t)
      htwo hAbound
  have hαpoint (t : ℝ) (ht : t ∈ Ioc u v) (htG : t ∈ D.goodV) :
      |D.S₁.alpha u t - D.S₂.alpha u t| ≤
        C₁ * (D.A V + D.L V) := by
    have htT : (u,t) ∈ triangle D.a V :=
      (mem_triangle).2 ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩
    have heq := D.alpha_diff_quotient_identity
      ((mem_triangle).2 ⟨huv.1, ht.1, ht.2.trans_lt (huv.2.2.trans hVb)⟩)
    have hlam := (hbg u t htT).1
    have hq := (hbg u t htT).2.2.2.1
    have hA := hApoint u t htT htG
    have hL := hLpoint u t htT htG
    rw [heq]
    calc
      |D.S₁.lam u t * (D.S₁.alpha u t / D.S₁.lam u t -
          D.S₂.alpha u t / D.S₂.lam u t) +
          (D.S₂.alpha u t / D.S₂.lam u t) *
          (D.S₁.lam u t - D.S₂.lam u t)| ≤
          |D.S₁.lam u t| *
            |D.S₁.alpha u t / D.S₁.lam u t -
              D.S₂.alpha u t / D.S₂.lam u t| +
          |D.S₂.alpha u t / D.S₂.lam u t| *
            |D.S₁.lam u t - D.S₂.lam u t| := by
        simpa only [abs_mul] using
          (abs_add_le
            (D.S₁.lam u t * (D.S₁.alpha u t / D.S₁.lam u t -
              D.S₂.alpha u t / D.S₂.lam u t))
            ((D.S₂.alpha u t / D.S₂.lam u t) *
              (D.S₁.lam u t - D.S₂.lam u t)))
      _ ≤ C₁ * D.A V + C₁ * D.L V := by
        apply add_le_add
        · exact (mul_le_mul_of_nonneg_right hlam (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hA hCpos.le)
        · exact (mul_le_mul_of_nonneg_right hq (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hL hCpos.le)
      _ = C₁ * (D.A V + D.L V) := by ring
  have hAE : ∀ᵐ t ∂volume, t ∈ Ι u v →
      |D.S₁.alpha u t - D.S₂.alpha u t| ≤
        C₁ * (D.A V + D.L V) := by
    filter_upwards [(D.goodV_properties).1] with t htG htI
    have ht : t ∈ Ioc u v := by simpa [uIoc_of_le huv.2.1.le] using htI
    exact hαpoint t ht htG
  have hInt := intervalIntegral.norm_integral_le_of_norm_le_const_ae
    (f := fun t => D.S₁.alpha u t - D.S₂.alpha u t)
    (C := C₁ * (D.A V + D.L V))
    (by simpa only [Real.norm_eq_abs] using hAE)
  have hInt' : |∫ t in u..v, D.S₁.alpha u t - D.S₂.alpha u t| ≤
      C₁ * (D.A V + D.L V) * (v-u) := by
    simpa only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr huv.2.1)] using hInt
  have hrad := D.radius_diff_le_L hVb.le huv
  have hp := D.hT ((mem_triangle).2
    ⟨huv.1, huv.2.1, huv.2.2.trans hVb⟩)
  have hrpos := D.h₁.solution.radius_pos (u,v) hp.1
  have hdist : 0 < v-u := sub_pos.mpr huv.2.1
  have hrlo := (hbg u v huv).2.2.2.2.2
  have hrcompare : v-u ≤ C₁ * D.S₁.r u v := by
    have hh := (div_le_div_iff₀ hCpos hdist).mp hrlo
    nlinarith
  have hphi := (hbg u v huv).2.2.2.2.1
  have hidentity := D.phi_diff_outgoing_density_identity
    ((mem_triangle).2 ⟨huv.1, huv.2.1, huv.2.2.trans hVb⟩)
  rw [hidentity]
  have hmain : |(∫ t in u..v, D.S₁.alpha u t - D.S₂.alpha u t) /
      D.S₁.r u v| ≤ C₁ ^ 2 * (D.A V + D.L V) := by
    rw [abs_div, abs_of_pos hrpos]
    apply (div_le_iff₀ hrpos).2
    calc
      |∫ t in u..v, D.S₁.alpha u t - D.S₂.alpha u t| ≤
          C₁ * (D.A V + D.L V) * (v-u) := hInt'
      _ ≤ C₁ * (D.A V + D.L V) * (C₁ * D.S₁.r u v) :=
        mul_le_mul_of_nonneg_left hrcompare
          (mul_nonneg hCpos.le (add_nonneg hA0 hL0))
      _ = (C₁ ^ 2 * (D.A V + D.L V)) * D.S₁.r u v := by ring
  have hcorrection : |((D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v) *
      D.S₂.phi u v| ≤ C₁ ^ 2 * D.L V := by
    rw [abs_mul, abs_div, abs_of_pos hrpos]
    -- Rewrite the first factor using the radius estimate and the lower radius bound.
    have hdiv : |D.S₁.r u v - D.S₂.r u v| / D.S₁.r u v ≤ C₁ * D.L V := by
      apply (div_le_iff₀ hrpos).2
      calc
        |D.S₁.r u v - D.S₂.r u v| ≤ (v-u) * D.L V := hrad
        _ ≤ (C₁ * D.S₁.r u v) * D.L V :=
          mul_le_mul_of_nonneg_right hrcompare hL0
        _ = (C₁ * D.L V) * D.S₁.r u v := by ring
    calc
      (|D.S₁.r u v - D.S₂.r u v| / D.S₁.r u v) *
          |D.S₂.phi u v| ≤ (C₁ * D.L V) * |D.S₂.phi u v| :=
        mul_le_mul_of_nonneg_right hdiv (abs_nonneg _)
      _ ≤ (C₁ * D.L V) * C₁ :=
        mul_le_mul_of_nonneg_left hphi (mul_nonneg hCpos.le hL0)
      _ = C₁ ^ 2 * D.L V := by ring
  have hsum := (abs_sub _ _).trans (add_le_add hmain hcorrection)
  nlinarith [mul_nonneg (sq_nonneg C₁) hA0]

end ChristodoulouBV.Uniqueness

end
