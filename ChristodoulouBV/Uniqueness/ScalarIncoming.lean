module

public import ChristodoulouBV.Uniqueness.RadiusScalarBase

/-!
# Incoming scalar comparison estimate

The corrected incoming identity is estimated on good incoming rays and then
extended through continuity of the scalar primitives.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The BV scalar field is continuous in the outgoing coordinate on every
open characteristic interval inside a common comparison triangle. -/
theorem ComparisonData.phi_continuousOn_outgoing (D : ComparisonData)
    {u V : ℝ} (hau : D.a ≤ u) (hVb : V ≤ D.b)
    (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :
    ContinuousOn (S.phi u) (Ioo u V) := by
  apply continuousOn_Ioo_of_ac_subintervals
  intro x y hux hxy hyV
  have hpoint : (u, y) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨hau, hux.trans_le hxy, hyV.trans_le hVb⟩
  rcases hS with rfl | rfl
  · exact D.h₁.item3_ac_out u x y hxy
      (D.h₁.solution.development.out_seg_subset
        (D.hT hpoint).1 hux hxy le_rfl)
  · exact D.h₂.item3_ac_out u x y hxy
      (D.h₂.solution.development.out_seg_subset
        (D.hT hpoint).2 hux hxy le_rfl)

/-- Algebraic endpoint estimate used by both scalar orientations. The input
`I` is the density-difference integral, with either sign. -/
theorem scalar_endpoint_bound
    {deltaPhi I deltaR phi r d C P Q : ℝ}
    (hC : 0 < C) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hd : 0 < d) (hr : 0 < r)
    (hrlo : 1 / C ≤ r / d)
    (hI : |I| ≤ C * (P + Q) * d)
    (hR : |deltaR| ≤ d * Q)
    (hphi : |phi| ≤ C)
    (hidentity : deltaPhi = -I / r - deltaR / r * phi) :
    |deltaPhi| ≤ 2 * C ^ 2 * (P + Q) := by
  have hrcompare : d ≤ C * r := by
    have hh := (div_le_div_iff₀ hC hd).mp hrlo
    nlinarith
  have hmain : |-I / r| ≤ C ^ 2 * (P + Q) := by
    rw [abs_div, abs_neg, abs_of_pos hr]
    apply (div_le_iff₀ hr).2
    calc
      |I| ≤ C * (P + Q) * d := hI
      _ ≤ C * (P + Q) * (C * r) :=
        mul_le_mul_of_nonneg_left hrcompare
          (mul_nonneg hC.le (add_nonneg hP hQ))
      _ = (C ^ 2 * (P + Q)) * r := by ring
  have hcorrection : |deltaR / r * phi| ≤ C ^ 2 * Q := by
    rw [abs_mul, abs_div, abs_of_pos hr]
    have hdiv : |deltaR| / r ≤ C * Q := by
      apply (div_le_iff₀ hr).2
      calc
        |deltaR| ≤ d * Q := hR
        _ ≤ (C * r) * Q := mul_le_mul_of_nonneg_right hrcompare hQ
        _ = (C * Q) * r := by ring
    calc
      (|deltaR| / r) * |phi| ≤ (C * Q) * |phi| :=
        mul_le_mul_of_nonneg_right hdiv (abs_nonneg _)
      _ ≤ (C * Q) * C :=
        mul_le_mul_of_nonneg_left hphi (mul_nonneg hC.le hQ)
      _ = C ^ 2 * Q := by ring
  rw [hidentity]
  have hsum := (abs_sub _ _).trans (add_le_add hmain hcorrection)
  nlinarith [mul_nonneg (sq_nonneg C) hP]

/-- The incoming scalar difference satisfies the stable B+N estimate at
every point, including exceptional incoming coordinates. The estimate uses
the corrected absolute incoming identity and the same preliminary
coefficient choice on every compact top. -/
theorem ComparisonData.phi_diff_incoming_le (D : ComparisonData)
    (ha : D.a = 0) (hb : D.b = 1) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∃ C₁ : ℝ, 4 ≤ C₁ ∧
        ((∀ u v, (u, v) ∈ triangle D.a D.b →
          ∀ S : Fields, (S = D.S₁ ∨ S = D.S₂) →
            (eVariationOn (S.phi u) (Ioc u v)).toReal ≤ ε₀ ∧
            (eVariationOn (fun s => S.phi s v) (Ico u v)).toReal ≤ ε₀) →
          ∀ V u v, V < D.b → (u, v) ∈ triangle D.a V →
            |D.S₁.phi u v - D.S₂.phi u v| ≤
              2 * C₁ ^ 2 * (D.B V + D.N V)) := by
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
