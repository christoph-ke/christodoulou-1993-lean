module

public import ChristodoulouBV.Uniqueness.Comparison

/-!
# Radius and scalar comparison estimates

The integration estimates use only the fixed good-v set for auxiliary
densities. Primary fields are recovered at all points from their continuous
characteristic primitives.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace ChristodoulouBV.Uniqueness

/-- The outgoing scalar-radius density is integrable up to the open axis.
This is the integrability proved in the axis formula, exported
here for subtraction of the two solutions. -/
theorem alpha_integrable_outgoing_axis
    {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsBVSolution U S) {u v : ℝ} (huv : (u, v) ∈ U) :
    IntervalIntegrable (S.alpha u) volume u v := by
  have hlt := (h.solution.development.wedge huv).2
  obtain ⟨K, hK, _⟩ := h.exists_uniform_radius_upper
  have hKnonneg : 0 ≤ K := by
    have hl := h.solution.lam_pos (u, v) huv
    linarith [hK (u, v) huv]
  have hBVφ : BoundedVariationOn (S.phi u) {t | (u, t) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (h.item3_variation.choose_spec.1 u)
  have hBVθ : BoundedVariationOn (S.theta u) {t | (u, t) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (h.item5.choose_spec.1 u)
  obtain ⟨Bφ, hBφ, hφ⟩ := hBVφ.exists_bound_on
  obtain ⟨Bθ, hBθ, hθ⟩ := hBVθ.exists_bound_on
  have hlocal : ∀ t ∈ Ioc u v,
      IntervalIntegrable (S.alpha u) volume t v := by
    intro t ht
    exact (h.solution.scalar_radius_out u t v ht.2
      (h.solution.development.out_seg_subset huv ht.1 ht.2 le_rfl)).1
  have hbound : ∀ t ∈ Ioc u v, |S.alpha u t| ≤ Bθ + K * Bφ := by
    intro t ht
    have htU := h.solution.development.outgoing_mem huv ht.1 ht.2
    have hprod : |S.lam u t * S.phi u t| ≤ K * Bφ := by
      rw [abs_mul, abs_of_pos (h.solution.lam_pos (u, t) htU)]
      exact (mul_le_mul_of_nonneg_right (hK (u, t) htU) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hφ t htU) hKnonneg)
    have heq : S.alpha u t = S.theta u t + S.lam u t * S.phi u t := by
      dsimp [Fields.theta]; ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add (hθ t htU) hprod)
  exact IsBVSolution.interval_integrable_of_bounded_left hlt
    (by positivity : 0 ≤ Bθ + K * Bφ) hlocal hbound

/-- The incoming scalar-radius density is integrable to the terminal axis
on a full augmented comparison triangle. -/
theorem beta_integrable_incoming_axis_of_triangle
    {U : Set (ℝ × ℝ)} {S : Fields}
    (h : IsBVSolution U S) {a b u v : ℝ}
    (hT : triangle a b ⊆ U) (huv : (u, v) ∈ triangle a b) :
    IntervalIntegrable (fun s => S.beta s v) volume u v := by
  obtain ⟨N, hN⟩ := h.nu_bounded_below
  obtain ⟨c, hc, hlam⟩ := h.lam_bounded_below
  have haccess := IsBVSolution.incoming_axis_access_of_triangle hT huv
  have hNnonneg : 0 ≤ N := by
    have hn := h.nu_le_neg_lower hc hlam (hT huv)
    linarith [hN (u, v) (hT huv)]
  have hBVφ : BoundedVariationOn (fun s => S.phi s v)
      {s | (s, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (h.item3_variation.choose_spec.2 v)
  have hBVζ : BoundedVariationOn (fun s => S.zeta s v)
      {s | (s, v) ∈ U} :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (h.item5.choose_spec.2 v)
  obtain ⟨Bφ, hBφ, hφ⟩ := hBVφ.exists_bound_on
  obtain ⟨Bζ, hBζ, hζ⟩ := hBVζ.exists_bound_on
  have hbound : ∀ s ∈ Ico u v, |S.beta s v| ≤ Bζ + N * Bφ := by
    intro s hs
    have hsU := haccess s hs
    have hnneg : S.nu s v < 0 :=
      (h.nu_le_neg_lower hc hlam hsU).trans_lt (neg_lt_zero.mpr hc)
    have hprod : |S.nu s v * S.phi s v| ≤ N * Bφ := by
      rw [abs_mul, abs_of_neg hnneg]
      calc
        -S.nu s v * |S.phi s v| ≤ N * |S.phi s v| :=
          mul_le_mul_of_nonneg_right (hN (s, v) hsU) (abs_nonneg _)
        _ ≤ N * Bφ := mul_le_mul_of_nonneg_left (hφ s hsU) hNnonneg
    have heq : S.beta s v = S.zeta s v + S.nu s v * S.phi s v := by
      dsimp [Fields.zeta]; ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add (hζ s hsU) hprod)
  have hlocal : ∀ s ∈ Ico u v,
      IntervalIntegrable (fun t => S.beta t v) volume u s := by
    intro s hs
    exact (h.solution.scalar_radius_in v u s hs.1
      (IsBVSolution.incoming_seg_subset_of_half_open_access hs.2 haccess)).1
  exact IsBVSolution.interval_integrable_of_bounded_right huv.2.1
    (by positivity : 0 ≤ Bζ + N * Bφ) hlocal hbound

/-- Local absolute continuity on compact subintervals gives continuity on
an open outgoing characteristic. -/
theorem continuousOn_Ioo_of_ac_subintervals
    {f : ℝ → ℝ} {u V : ℝ}
    (h : ∀ x y, u < x → x ≤ y → y < V →
      AbsolutelyContinuousOnInterval f x y) :
    ContinuousOn f (Ioo u V) := by
  intro v hv
  have huv : u < v := hv.1
  have hvV : v < V := hv.2
  let x := (u + v) / 2
  let y := (v + V) / 2
  have hux : u < x := by dsimp [x]; linarith
  have hxv : x < v := by dsimp [x]; linarith
  have hvy : v < y := by dsimp [y]; linarith
  have hyV : y < V := by dsimp [y]; linarith
  have hxy : x ≤ y := by linarith
  have hmem : Set.uIcc x y ∈ 𝓝 v := by
    rw [uIcc_of_le hxy]
    exact Icc_mem_nhds hxv hvy
  have hcont : ContinuousAt f v :=
    (h x y hux hxy hyV).continuousOn.continuousAt
      hmem
  exact hcont.continuousWithinAt

/-- The radius of either BV solution is continuous in the outgoing
coordinate on every open subinterval of a comparison triangle. -/
theorem ComparisonData.radius_continuousOn_outgoing (D : ComparisonData)
    {u V : ℝ} (hau : D.a ≤ u) (hVb : V ≤ D.b)
    (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :
    ContinuousOn (S.r u) (Ioo u V) := by
  apply continuousOn_Ioo_of_ac_subintervals
  intro x y hux hxy hyV
  have hpoint : (u, y) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨hau, hux.trans_le hxy, hyV.trans_le hVb⟩
  rcases hS with rfl | rfl
  · exact IsBVSolution.radius_ac_on_outgoing D.h₁.solution.development D.h₁.solution
      (D.hT hpoint).1 hux hxy le_rfl
  · exact IsBVSolution.radius_ac_on_outgoing D.h₂.solution.development D.h₂.solution
      (D.hT hpoint).2 hux hxy le_rfl

/-- Every field represented by an outgoing characteristic primitive is
continuous in its outgoing coordinate. This includes r, rφ, m, ν, and β,
but makes no continuity claim for the BV representatives λ or α. -/
theorem ComparisonData.outgoing_continuous_primitives (D : ComparisonData)
    {u V : ℝ} (hau : D.a ≤ u) (hVb : V ≤ D.b)
    (S : Fields) (hS : S = D.S₁ ∨ S = D.S₂) :
    ContinuousOn (S.r u) (Ioo u V) ∧
    ContinuousOn (fun v => S.r u v * S.phi u v) (Ioo u V) ∧
    ContinuousOn (S.m u) (Ioo u V) ∧
    ContinuousOn (S.nu u) (Ioo u V) ∧
    ContinuousOn (S.beta u) (Ioo u V) := by
  have hslice (x y : ℝ) (hux : u < x) (hxy : x ≤ y) (hyV : y < V) :
      (u, y) ∈ triangle D.a D.b :=
    (mem_triangle).2 ⟨hau, hux.trans_le hxy, hyV.trans_le hVb⟩
  have hac (x y : ℝ) (hux : u < x) (hxy : x ≤ y) (hyV : y < V)
      {U : Set (ℝ × ℝ)} (hS' : IsBVSolution U S)
      (hT' : triangle D.a D.b ⊆ U) : outSeg u x y ⊆ U :=
    hS'.solution.development.out_seg_subset
      (hT' (hslice x y hux hxy hyV)) hux hxy le_rfl
  rcases hS with rfl | rfl
  · have hT₁ : triangle D.a D.b ⊆ D.U₁ := fun p hp => (D.hT hp).1
    refine ⟨D.radius_continuousOn_outgoing hau hVb D.S₁ (Or.inl rfl), ?_, ?_, ?_, ?_⟩
    · apply continuousOn_Ioo_of_ac_subintervals
      intro x y hux hxy hyV
      exact (D.h₁.solution.scalar_radius_out_ac_ae hxy
        (hac x y hux hxy hyV D.h₁ hT₁)).1
    · apply continuousOn_Ioo_of_ac_subintervals
      intro x y hux hxy hyV
      exact IsBVSolution.mass_ac_on_outgoing D.h₁.solution.development
        D.h₁.solution (hT₁ (hslice x y hux hxy hyV)) hux hxy le_rfl
    · apply continuousOn_Ioo_of_ac_subintervals
      intro x y hux hxy hyV
      exact (D.h₁.solution.nu_out_ac_ae hxy
        (hac x y hux hxy hyV D.h₁ hT₁)).1
    · apply continuousOn_Ioo_of_ac_subintervals
      intro x y hux hxy hyV
      exact (D.h₁.solution.beta_out_ac_ae hxy
        (hac x y hux hxy hyV D.h₁ hT₁)).1
  · have hT₂ : triangle D.a D.b ⊆ D.U₂ := fun p hp => (D.hT hp).2
    refine ⟨D.radius_continuousOn_outgoing hau hVb D.S₂ (Or.inr rfl), ?_, ?_, ?_, ?_⟩
    · apply continuousOn_Ioo_of_ac_subintervals
      intro x y hux hxy hyV
      exact (D.h₂.solution.scalar_radius_out_ac_ae hxy
        (hac x y hux hxy hyV D.h₂ hT₂)).1
    · apply continuousOn_Ioo_of_ac_subintervals
      intro x y hux hxy hyV
      exact IsBVSolution.mass_ac_on_outgoing D.h₂.solution.development
        D.h₂.solution (hT₂ (hslice x y hux hxy hyV)) hux hxy le_rfl
    · apply continuousOn_Ioo_of_ac_subintervals
      intro x y hux hxy hyV
      exact (D.h₂.solution.nu_out_ac_ae hxy
        (hac x y hux hxy hyV D.h₂ hT₂)).1
    · apply continuousOn_Ioo_of_ac_subintervals
      intro x y hux hxy hyV
      exact (D.h₂.solution.beta_out_ac_ae hxy
        (hac x y hux hxy hyV D.h₂ hT₂)).1

/-- An upper bound for the outgoing density difference is available from the
global BV coefficient bounds, before any local variation smallness is chosen. -/
private theorem ComparisonData.outgoing_expansion_bound (D : ComparisonData) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ u v, (u, v) ∈ triangle D.a D.b →
        |D.S₁.lam u v - D.S₂.lam u v| ≤ M := by
  obtain ⟨K₁, hK₁, _⟩ := D.h₁.exists_uniform_radius_upper
  obtain ⟨K₂, hK₂, _⟩ := D.h₂.exists_uniform_radius_upper
  have hpoint (u v : ℝ) (huv : (u, v) ∈ triangle D.a D.b) :
      |D.S₁.lam u v - D.S₂.lam u v| ≤ K₁ + K₂ := by
    have hp := D.hT huv
    have hpos₁ := D.h₁.solution.lam_pos (u, v) hp.1
    have hpos₂ := D.h₂.solution.lam_pos (u, v) hp.2
    rw [abs_sub_le_iff]
    constructor <;> linarith [hK₁ (u, v) hp.1, hK₂ (u, v) hp.2]
  have hnonneg : 0 ≤ K₁ + K₂ := by
    obtain ⟨v, hv⟩ := exists_between D.hab
    have hp : (D.a, v) ∈ triangle D.a D.b :=
      initial_edge_of_triangle hv.1 hv.2
    have := hpoint D.a v hp
    linarith [abs_nonneg (D.S₁.lam D.a v - D.S₂.lam D.a v)]
  exact ⟨K₁ + K₂, hnonneg, hpoint⟩

/-- An upper bound for the incoming density difference follows from the BV
bound on negative ν and its strict negative sign. -/
private theorem ComparisonData.incoming_expansion_bound (D : ComparisonData) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ u v, (u, v) ∈ triangle D.a D.b →
        |D.S₁.nu u v - D.S₂.nu u v| ≤ M := by
  obtain ⟨K₁, hK₁⟩ := D.h₁.nu_bounded_below
  obtain ⟨K₂, hK₂⟩ := D.h₂.nu_bounded_below
  obtain ⟨c₁, hc₁, hlam₁⟩ := D.h₁.lam_bounded_below
  obtain ⟨c₂, hc₂, hlam₂⟩ := D.h₂.lam_bounded_below
  have hpoint (u v : ℝ) (huv : (u, v) ∈ triangle D.a D.b) :
      |D.S₁.nu u v - D.S₂.nu u v| ≤ K₁ + K₂ := by
    have hp := D.hT huv
    have hn₁ := D.h₁.nu_le_neg_lower hc₁ hlam₁ hp.1
    have hn₂ := D.h₂.nu_le_neg_lower hc₂ hlam₂ hp.2
    rw [abs_sub_le_iff]
    constructor <;> linarith [hK₁ (u, v) hp.1, hK₂ (u, v) hp.2]
  have hnonneg : 0 ≤ K₁ + K₂ := by
    obtain ⟨v, hv⟩ := exists_between D.hab
    have hp : (D.a, v) ∈ triangle D.a D.b :=
      initial_edge_of_triangle hv.1 hv.2
    have := hpoint D.a v hp
    linarith [abs_nonneg (D.S₁.nu D.a v - D.S₂.nu D.a v)]
  exact ⟨K₁ + K₂, hnonneg, hpoint⟩

/-- The outgoing axis integral bounds the radius difference by the stable
good-v outgoing norm on every compact comparison top. -/
theorem ComparisonData.radius_diff_le_L (D : ComparisonData)
    {V u v : ℝ} (hV : V ≤ D.b)
    (huv : (u, v) ∈ triangle D.a V) :
    |D.S₁.r u v - D.S₂.r u v| ≤ (v - u) * D.L V := by
  obtain ⟨M, hM, hbound⟩ := D.outgoing_expansion_bound
  have hpoint (s t : ℝ) (hst : (s, t) ∈ triangle D.a V)
      (htG : t ∈ D.goodV) :
      |D.S₁.lam s t - D.S₂.lam s t| ≤ D.L V := by
    change |D.S₁.lam s t - D.S₂.lam s t| ≤
      D.goodVNorm V (fun x y => D.S₁.lam x y - D.S₂.lam x y)
    apply D.le_goodVNorm (V := V)
      (f := fun x y => D.S₁.lam x y - D.S₂.lam x y) hM
    · intro x y hxy hyG
      exact hbound x y ((mem_triangle).2
        ⟨hxy.1, hxy.2.1, hxy.2.2.trans_le hV⟩)
    · exact hst
    · exact htG
  have hp : (u, v) ∈ D.U₁ ∩ D.U₂ :=
    D.hT ((mem_triangle).2 ⟨huv.1, huv.2.1, huv.2.2.trans_le hV⟩)
  have hAE : ∀ᵐ t ∂volume, t ∈ Ι u v →
      |D.S₁.lam u t - D.S₂.lam u t| ≤ D.L V := by
    filter_upwards [(D.goodV_properties).1] with t htG htI
    have ht : t ∈ Ioc u v := by simpa [uIoc_of_le huv.2.1.le] using htI
    exact hpoint u t ((mem_triangle).2
      ⟨huv.1, ht.1, ht.2.trans_lt huv.2.2⟩) htG
  have hInt := intervalIntegral.norm_integral_le_of_norm_le_const_ae
    (f := fun t => D.S₁.lam u t - D.S₂.lam u t) (C := D.L V)
    (by simpa only [Real.norm_eq_abs] using hAE)
  have heq := D.h₁.radius_difference_eq_outgoing_axis_integral D.h₂ hp
  rw [heq]
  simpa only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr huv.2.1), mul_comm]
    using hInt

/-- The incoming terminal axis integral bounds the radius difference by the
stable incoming norm at good incoming rays. -/
theorem ComparisonData.radius_diff_le_N_good (D : ComparisonData)
    {V u v : ℝ} (hV : V ≤ D.b)
    (huv : (u, v) ∈ triangle D.a V) (hvG : v ∈ D.goodV) :
    |D.S₁.r u v - D.S₂.r u v| ≤ (v - u) * D.N V := by
  obtain ⟨M, hM, hbound⟩ := D.incoming_expansion_bound
  have hpoint (s : ℝ) (hs : s ∈ Ico u v) :
      |D.S₁.nu s v - D.S₂.nu s v| ≤ D.N V := by
    change |D.S₁.nu s v - D.S₂.nu s v| ≤
      D.goodVNorm V (fun x y => D.S₁.nu x y - D.S₂.nu x y)
    apply D.le_goodVNorm (V := V)
      (f := fun x y => D.S₁.nu x y - D.S₂.nu x y) hM
    · intro x y hxy hyG
      exact hbound x y ((mem_triangle).2
        ⟨hxy.1, hxy.2.1, hxy.2.2.trans_le hV⟩)
    · exact (mem_triangle).2 ⟨huv.1.trans hs.1, hs.2, huv.2.2⟩
    · exact hvG
  have hAE : ∀ᵐ s ∂volume, s ∈ Ι u v →
      |D.S₁.nu s v - D.S₂.nu s v| ≤ D.N V := by
    have hae : ∀ᵐ s : ℝ ∂volume, s ≠ v := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hae] with s hsne hsI
    have hs : s ∈ Ico u v := by
      have hh : s ∈ Ioc u v := by simpa [uIoc_of_le huv.2.1.le] using hsI
      exact ⟨hh.1.le, lt_of_le_of_ne hh.2 hsne⟩
    exact hpoint s hs
  have hInt := intervalIntegral.norm_integral_le_of_norm_le_const_ae
    (f := fun s => D.S₁.nu s v - D.S₂.nu s v) (C := D.N V)
    (by simpa only [Real.norm_eq_abs] using hAE)
  have heq := D.h₁.radius_difference_eq_incoming_axis_integral_of_triangle
    D.h₂ D.hT ((mem_triangle).2
      ⟨huv.1, huv.2.1, huv.2.2.trans_le hV⟩)
  rw [heq]
  simpa only [abs_neg, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr huv.2.1),
    mul_comm] using hInt

/-- Continuity of the radius primitives extends the incoming comparison
estimate to exceptional incoming coordinates without evaluating ν there. -/
theorem ComparisonData.radius_diff_le_N (D : ComparisonData)
    {V u v : ℝ} (hV : V < D.b)
    (huv : (u, v) ∈ triangle D.a V) :
    |D.S₁.r u v - D.S₂.r u v| ≤ (v - u) * D.N V := by
  have hcont₁ := D.radius_continuousOn_outgoing huv.1
    hV.le D.S₁ (Or.inl rfl)
  have hcont₂ := D.radius_continuousOn_outgoing huv.1
    hV.le D.S₂ (Or.inr rfl)
  have hf : ContinuousOn
      (fun t => |D.S₁.r u t - D.S₂.r u t| - (t - u) * D.N V)
      (Ioo u V) := by
    have hlin : ContinuousOn (fun t => (t - u) * D.N V) (Ioo u V) := by
      fun_prop
    exact (hcont₁.sub hcont₂).abs.sub hlin
  have hG : Dense D.goodV := (D.goodV_properties).2.1
  have hbound : ∀ t ∈ Ioo u V, t ∈ D.goodV →
      |D.S₁.r u t - D.S₂.r u t| - (t - u) * D.N V ≤ 0 := by
    intro t ht htG
    have htT : (u, t) ∈ triangle D.a V :=
      (mem_triangle).2 ⟨huv.1, ht.1, ht.2⟩
    have hh := D.radius_diff_le_N_good hV.le htT htG
    linarith
  have hh := goodV_continuous_le hG hf hbound v ⟨huv.2.1, huv.2.2⟩
  linarith

/-- Subtraction of the two outgoing scalar-radius axis primitives. This is
the endpoint algebra underlying (3.6a), before splitting the integrand into
quotient and expansion differences. -/
theorem ComparisonData.phi_diff_outgoing_integral_identity
    (D : ComparisonData) {u v : ℝ}
    (huv : (u, v) ∈ triangle D.a D.b) :
    D.S₁.phi u v - D.S₂.phi u v =
      ((∫ t in u..v, D.S₁.alpha u t) -
        (∫ t in u..v, D.S₂.alpha u t)) / D.S₁.r u v -
      ((D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v) *
        D.S₂.phi u v := by
  have hp := D.hT huv
  have hr₁ := D.h₁.solution.radius_pos (u, v) hp.1
  have hr₂ := D.h₂.solution.radius_pos (u, v) hp.2
  have hφ₁ := D.h₁.phi_eq_outgoing_alpha_integral hp.1
  have hφ₂ := D.h₂.phi_eq_outgoing_alpha_integral hp.2
  rw [hφ₁, hφ₂]
  field_simp [ne_of_gt hr₁, ne_of_gt hr₂]
  ring

/-- The outgoing scalar difference is an integral of the difference of the
two scalar-radius densities, with the exact radius correction. -/
theorem ComparisonData.phi_diff_outgoing_density_identity
    (D : ComparisonData) {u v : ℝ}
    (huv : (u, v) ∈ triangle D.a D.b) :
    D.S₁.phi u v - D.S₂.phi u v =
      (∫ t in u..v, D.S₁.alpha u t - D.S₂.alpha u t) /
        D.S₁.r u v -
      ((D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v) *
        D.S₂.phi u v := by
  have hp := D.hT huv
  have h₁int := alpha_integrable_outgoing_axis D.h₁ hp.1
  have h₂int := alpha_integrable_outgoing_axis D.h₂ hp.2
  rw [D.phi_diff_outgoing_integral_identity huv,
    intervalIntegral.integral_sub h₁int h₂int]

/-- Subtraction of the two incoming scalar-radius axis primitives. The
radius correction has the same negative sign as in the outgoing formula;
absolute values are taken only after this identity. -/
theorem ComparisonData.phi_diff_incoming_integral_identity
    (D : ComparisonData) {u v : ℝ}
    (huv : (u, v) ∈ triangle D.a D.b) :
    D.S₁.phi u v - D.S₂.phi u v =
      -((∫ s in u..v, D.S₁.beta s v) -
        (∫ s in u..v, D.S₂.beta s v)) / D.S₁.r u v -
      ((D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v) *
        D.S₂.phi u v := by
  have hT₁ : triangle D.a D.b ⊆ D.U₁ := fun p hp => (D.hT hp).1
  have hT₂ : triangle D.a D.b ⊆ D.U₂ := fun p hp => (D.hT hp).2
  have hp := D.hT huv
  have hr₁ := D.h₁.solution.radius_pos (u, v) hp.1
  have hr₂ := D.h₂.solution.radius_pos (u, v) hp.2
  have hφ₁ := D.h₁.phi_eq_incoming_beta_integral_of_triangle hT₁ huv
  have hφ₂ := D.h₂.phi_eq_incoming_beta_integral_of_triangle hT₂ huv
  rw [hφ₁, hφ₂]
  field_simp [ne_of_gt hr₁, ne_of_gt hr₂]
  ring

/-- The corrected incoming scalar difference is an integral of the incoming
density difference. The radius correction retains its negative sign. -/
theorem ComparisonData.phi_diff_incoming_density_identity
    (D : ComparisonData) {u v : ℝ}
    (huv : (u, v) ∈ triangle D.a D.b) :
    D.S₁.phi u v - D.S₂.phi u v =
      -(∫ s in u..v, D.S₁.beta s v - D.S₂.beta s v) /
        D.S₁.r u v -
      ((D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v) *
        D.S₂.phi u v := by
  have hT₁ : triangle D.a D.b ⊆ D.U₁ := fun p hp => (D.hT hp).1
  have hT₂ : triangle D.a D.b ⊆ D.U₂ := fun p hp => (D.hT hp).2
  have h₁int := beta_integrable_incoming_axis_of_triangle D.h₁ hT₁ huv
  have h₂int := beta_integrable_incoming_axis_of_triangle D.h₂ hT₂ huv
  rw [D.phi_diff_incoming_integral_identity huv,
    intervalIntegral.integral_sub h₁int h₂int]

/-- Pointwise mass-ratio difference identity (3.9). -/
theorem ComparisonData.mu_diff_identity (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    IsBVSolution.mu D.S₁ u v - IsBVSolution.mu D.S₂ u v =
      2 * (D.S₁.m u v - D.S₂.m u v) / D.S₁.r u v -
      IsBVSolution.mu D.S₂ u v *
        (D.S₁.r u v - D.S₂.r u v) / D.S₁.r u v := by
  have hp := D.hT huv
  have hr₁ := D.h₁.solution.radius_pos (u, v) hp.1
  have hr₂ := D.h₂.solution.radius_pos (u, v) hp.2
  unfold IsBVSolution.mu
  field_simp [ne_of_gt hr₁, ne_of_gt hr₂]
  ring

/-- Pointwise outgoing quotient expansion of the scalar-radius density.
This algebra is used a.e. under outgoing integrals, where exceptional values
of the primitive density do not contribute. -/
theorem ComparisonData.alpha_diff_quotient_identity (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    D.S₁.alpha u v - D.S₂.alpha u v =
      D.S₁.lam u v *
        (D.S₁.alpha u v / D.S₁.lam u v -
          D.S₂.alpha u v / D.S₂.lam u v) +
      (D.S₂.alpha u v / D.S₂.lam u v) *
        (D.S₁.lam u v - D.S₂.lam u v) := by
  have hp := D.hT huv
  have hlam₁ := D.h₁.solution.lam_pos (u, v) hp.1
  have hlam₂ := D.h₂.solution.lam_pos (u, v) hp.2
  field_simp [ne_of_gt hlam₁, ne_of_gt hlam₂]
  ring

/-- Pointwise incoming quotient expansion of the scalar-radius density.
The ν denominator is nonzero by the BV sign bridge. -/
theorem ComparisonData.beta_diff_quotient_identity (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    D.S₁.beta u v - D.S₂.beta u v =
      D.S₁.nu u v *
        (D.S₁.beta u v / D.S₁.nu u v -
          D.S₂.beta u v / D.S₂.nu u v) +
      (D.S₂.beta u v / D.S₂.nu u v) *
        (D.S₁.nu u v - D.S₂.nu u v) := by
  have hp := D.hT huv
  obtain ⟨c₁, hc₁, hlam₁⟩ := D.h₁.lam_bounded_below
  obtain ⟨c₂, hc₂, hlam₂⟩ := D.h₂.lam_bounded_below
  have hnu₁ : D.S₁.nu u v ≠ 0 :=
    ne_of_lt ((D.h₁.nu_le_neg_lower hc₁ hlam₁ hp.1).trans_lt
      (neg_lt_zero.mpr hc₁))
  have hnu₂ : D.S₂.nu u v ≠ 0 :=
    ne_of_lt ((D.h₂.nu_le_neg_lower hc₂ hlam₂ hp.2).trans_lt
      (neg_lt_zero.mpr hc₂))
  field_simp [hnu₁, hnu₂]
  ring

/-- Algebraic θ difference identity behind (3.8a). -/
theorem ComparisonData.theta_diff_identity (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    D.S₁.theta u v - D.S₂.theta u v =
      D.S₁.lam u v *
        (D.S₁.alpha u v / D.S₁.lam u v -
          D.S₂.alpha u v / D.S₂.lam u v) +
      (D.S₂.theta u v / D.S₂.lam u v) *
        (D.S₁.lam u v - D.S₂.lam u v) -
      D.S₁.lam u v * (D.S₁.phi u v - D.S₂.phi u v) := by
  have hp := D.hT huv
  have hlam₁ := D.h₁.solution.lam_pos (u, v) hp.1
  have hlam₂ := D.h₂.solution.lam_pos (u, v) hp.2
  dsimp [Fields.theta]
  field_simp [ne_of_gt hlam₁, ne_of_gt hlam₂]
  ring

/-- Algebraic ζ difference identity behind (3.8b). -/
theorem ComparisonData.zeta_diff_identity (D : ComparisonData)
    {u v : ℝ} (huv : (u, v) ∈ triangle D.a D.b) :
    D.S₁.zeta u v - D.S₂.zeta u v =
      D.S₁.nu u v *
        (D.S₁.beta u v / D.S₁.nu u v -
          D.S₂.beta u v / D.S₂.nu u v) +
      (D.S₂.zeta u v / D.S₂.nu u v) *
        (D.S₁.nu u v - D.S₂.nu u v) -
      D.S₁.nu u v * (D.S₁.phi u v - D.S₂.phi u v) := by
  have hp := D.hT huv
  obtain ⟨c₁, hc₁, hlam₁⟩ := D.h₁.lam_bounded_below
  obtain ⟨c₂, hc₂, hlam₂⟩ := D.h₂.lam_bounded_below
  have hnu₁ : D.S₁.nu u v ≠ 0 :=
    ne_of_lt ((D.h₁.nu_le_neg_lower hc₁ hlam₁ hp.1).trans_lt
      (neg_lt_zero.mpr hc₁))
  have hnu₂ : D.S₂.nu u v ≠ 0 :=
    ne_of_lt ((D.h₂.nu_le_neg_lower hc₂ hlam₂ hp.2).trans_lt
      (neg_lt_zero.mpr hc₂))
  dsimp [Fields.zeta]
  field_simp [hnu₁, hnu₂]
  ring
end ChristodoulouBV.Uniqueness

end
