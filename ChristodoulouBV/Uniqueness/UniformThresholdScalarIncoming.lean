module

public import ChristodoulouBV.Uniqueness.UniformThresholdIStarHardy
public import ChristodoulouBV.Uniqueness.ScalarIncoming

/-!
# Package-uniform incoming scalar difference

The scalar comparison constant is selected before normalized comparison data.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The incoming scalar difference satisfies the stable B+N estimate at
every point, including exceptional incoming coordinates. The estimate uses
the corrected absolute incoming identity and the same preliminary
coefficient choice on every compact top. -/
theorem UniformThresholdBounds.phi_diff_incoming_le
    (P : UniformThresholdBounds) :
    ∃ C₁ : ℝ, 4 ≤ C₁ ∧
      ∀ D : ComparisonData, D.a = 0 → D.b = 1 →
        P.Holds D.S₁ D.S₂ →
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ P.gapThreshold) →
          ∀ V u v, V < D.b → (u, v) ∈ triangle D.a V →
            |D.S₁.phi u v - D.S₂.phi u v| ≤
              2 * C₁ ^ 2 * (D.B V + D.N V)) := by
  obtain ⟨C₁, hC₁, hcoeff⟩ := P.coefficient_bounds_normalized
  refine ⟨C₁, hC₁, ?_⟩
  intro D ha hb hP hsmall V u v hVb huv
  have hCpos : 0 < C₁ := by linarith
  have htwo : 0 ≤ 2 * C₁ := by linarith
  have hfield (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V)
      (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :=
    hcoeff D ha hb hP hsmall x y
      ((mem_triangle).2 ⟨hxy.1, hxy.2.1, hxy.2.2.trans hVb⟩) S hS
  have hbg (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V) :
      |D.S₁.nu x y| ≤ C₁ ∧ |D.S₂.nu x y| ≤ C₁ ∧
      |D.S₁.beta x y / D.S₁.nu x y| ≤ C₁ ∧
      |D.S₂.beta x y / D.S₂.nu x y| ≤ C₁ ∧
      |D.S₂.phi x y| ≤ C₁ ∧
      1 / C₁ ≤ D.S₁.r x y / (y - x) := by
    rcases hfield x y hxy D.S₁ (Or.inl rfl) with
      ⟨_, _, _, hnu₁, _, _, _, hrlo, _, _, _, _, _, _, hp₁, _, _, _, _, _⟩
    rcases hfield x y hxy D.S₂ (Or.inr rfl) with
      ⟨_, _, _, hnu₂, hphi₂, _, _, _, _, _, _, _, _, _, hp₂, _, _, _, _, _⟩
    exact ⟨hnu₁, hnu₂, hp₁, hp₂, hphi₂, hrlo⟩
  have hNbound (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V)
      (_hyG : y ∈ D.goodV) :
      |D.S₁.nu x y - D.S₂.nu x y| ≤ 2 * C₁ := by
    have h := hbg x y hxy
    calc
      |D.S₁.nu x y - D.S₂.nu x y| ≤
          |D.S₁.nu x y| + |D.S₂.nu x y| := abs_sub _ _
      _ ≤ C₁ + C₁ := add_le_add h.1 h.2.1
      _ = 2 * C₁ := by ring
  have hBbound (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V)
      (_hyG : y ∈ D.goodV) :
      |D.S₁.beta x y / D.S₁.nu x y -
        D.S₂.beta x y / D.S₂.nu x y| ≤ 2 * C₁ := by
    have h := hbg x y hxy
    calc
      |D.S₁.beta x y / D.S₁.nu x y -
        D.S₂.beta x y / D.S₂.nu x y| ≤
          |D.S₁.beta x y / D.S₁.nu x y| +
          |D.S₂.beta x y / D.S₂.nu x y| := abs_sub _ _
      _ ≤ C₁ + C₁ := add_le_add h.2.2.1 h.2.2.2.1
      _ = 2 * C₁ := by ring
  have hNpoint (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V)
      (hyG : y ∈ D.goodV) :
      |D.S₁.nu x y - D.S₂.nu x y| ≤ D.N V :=
    D.le_goodVNorm (V := V)
      (f := fun s t => D.S₁.nu s t - D.S₂.nu s t)
      htwo hNbound hxy hyG
  have hBpoint (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V)
      (hyG : y ∈ D.goodV) :
      |D.S₁.beta x y / D.S₁.nu x y -
        D.S₂.beta x y / D.S₂.nu x y| ≤ D.B V :=
    D.le_goodVNorm (V := V)
      (f := fun s t => D.S₁.beta s t / D.S₁.nu s t -
        D.S₂.beta s t / D.S₂.nu s t)
      htwo hBbound hxy hyG
  have hN0 : 0 ≤ D.N V :=
    D.goodVNorm_nonneg (V := V)
      (f := fun s t => D.S₁.nu s t - D.S₂.nu s t)
      htwo hNbound
  have hB0 : 0 ≤ D.B V :=
    D.goodVNorm_nonneg (V := V)
      (f := fun s t => D.S₁.beta s t / D.S₁.nu s t -
        D.S₂.beta s t / D.S₂.nu s t)
      htwo hBbound
  have hgood (x y : ℝ) (hxy : (x, y) ∈ triangle D.a V)
      (hyG : y ∈ D.goodV) :
      |D.S₁.phi x y - D.S₂.phi x y| ≤
        2 * C₁ ^ 2 * (D.B V + D.N V) := by
    have hβpoint (s : ℝ) (hs : s ∈ Ico x y) :
        |D.S₁.beta s y - D.S₂.beta s y| ≤
          C₁ * (D.B V + D.N V) := by
      have hsT : (s, y) ∈ triangle D.a V :=
        (mem_triangle).2 ⟨hxy.1.trans hs.1, hs.2, hxy.2.2⟩
      have heq := D.beta_diff_quotient_identity
        ((mem_triangle).2 ⟨hxy.1.trans hs.1, hs.2,
          hxy.2.2.trans hVb⟩)
      have hnu := (hbg s y hsT).1
      have hq := (hbg s y hsT).2.2.2.1
      have hB := hBpoint s y hsT hyG
      have hN := hNpoint s y hsT hyG
      rw [heq]
      calc
        |D.S₁.nu s y * (D.S₁.beta s y / D.S₁.nu s y -
            D.S₂.beta s y / D.S₂.nu s y) +
            (D.S₂.beta s y / D.S₂.nu s y) *
            (D.S₁.nu s y - D.S₂.nu s y)| ≤
            |D.S₁.nu s y| *
              |D.S₁.beta s y / D.S₁.nu s y -
                D.S₂.beta s y / D.S₂.nu s y| +
            |D.S₂.beta s y / D.S₂.nu s y| *
              |D.S₁.nu s y - D.S₂.nu s y| := by
          simpa only [abs_mul] using
            (abs_add_le
              (D.S₁.nu s y * (D.S₁.beta s y / D.S₁.nu s y -
                D.S₂.beta s y / D.S₂.nu s y))
              ((D.S₂.beta s y / D.S₂.nu s y) *
                (D.S₁.nu s y - D.S₂.nu s y)))
        _ ≤ C₁ * D.B V + C₁ * D.N V := by
          apply add_le_add
          · exact (mul_le_mul_of_nonneg_right hnu (abs_nonneg _)).trans
              (mul_le_mul_of_nonneg_left hB hCpos.le)
          · exact (mul_le_mul_of_nonneg_right hq (abs_nonneg _)).trans
              (mul_le_mul_of_nonneg_left hN hCpos.le)
        _ = C₁ * (D.B V + D.N V) := by ring
    have hAE : ∀ᵐ s ∂volume, s ∈ Ι x y →
        |D.S₁.beta s y - D.S₂.beta s y| ≤
          C₁ * (D.B V + D.N V) := by
      have hae : ∀ᵐ s : ℝ ∂volume, s ≠ y := by
        simp [ae_iff, measure_singleton]
      filter_upwards [hae] with s hsne hsI
      have hs : s ∈ Ico x y := by
        have hh : s ∈ Ioc x y := by
          simpa [uIoc_of_le hxy.2.1.le] using hsI
        exact ⟨hh.1.le, lt_of_le_of_ne hh.2 hsne⟩
      exact hβpoint s hs
    have hInt := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (f := fun s => D.S₁.beta s y - D.S₂.beta s y)
      (C := C₁ * (D.B V + D.N V))
      (by simpa only [Real.norm_eq_abs] using hAE)
    have hInt' : |∫ s in x..y, D.S₁.beta s y - D.S₂.beta s y| ≤
        C₁ * (D.B V + D.N V) * (y-x) := by
      simpa only [Real.norm_eq_abs,
        abs_of_pos (sub_pos.mpr hxy.2.1)] using hInt
    have hrad := D.radius_diff_le_N hVb hxy
    have hp := D.hT ((mem_triangle).2
      ⟨hxy.1, hxy.2.1, hxy.2.2.trans hVb⟩)
    have hrpos := D.h₁.solution.radius_pos (x,y) hp.1
    have hphi := (hbg x y hxy).2.2.2.2.1
    have hrlo := (hbg x y hxy).2.2.2.2.2
    have hidentity := D.phi_diff_incoming_density_identity
      ((mem_triangle).2 ⟨hxy.1, hxy.2.1,
        hxy.2.2.trans hVb⟩)
    exact scalar_endpoint_bound hCpos hB0 hN0
      (sub_pos.mpr hxy.2.1) hrpos hrlo hInt' hrad hphi hidentity
  have hcont₁ := D.phi_continuousOn_outgoing huv.1 hVb.le
    D.S₁ (Or.inl rfl)
  have hcont₂ := D.phi_continuousOn_outgoing huv.1 hVb.le
    D.S₂ (Or.inr rfl)
  have hf : ContinuousOn
      (fun t => |D.S₁.phi u t - D.S₂.phi u t|)
      (Ioo u V) := (hcont₁.sub hcont₂).abs
  have hbound : ∀ t ∈ Ioo u V, t ∈ D.goodV →
      |D.S₁.phi u t - D.S₂.phi u t| ≤
        2 * C₁ ^ 2 * (D.B V + D.N V) := by
    intro t ht htG
    exact hgood u t ((mem_triangle).2
      ⟨huv.1, ht.1, ht.2⟩) htG
  exact goodV_continuous_le (D.goodV_properties).2.1 hf hbound v
    ⟨huv.2.1, huv.2.2⟩


end ChristodoulouBV.Uniqueness

end
