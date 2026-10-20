module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Smooth approximation of functions of bounded variation

A nonnegative probability kernel does not increase the total variation of a bounded
measurable real function. Applying this to smooth kernels supported to the left of zero
gives smooth approximations to right-continuous BV functions on a half-line.
-/

public section

open Set Filter Metric MeasureTheory
open scoped Topology Convolution ContDiff

namespace eVariationOn

/-- Averaging a bounded measurable real function against a nonnegative probability density
cannot increase its variation on the whole real line. -/
theorem integral_sub_le {f ρ : ℝ → ℝ} (hf : StronglyMeasurable f)
    (hbound : ∃ C : ℝ, ∀ x, |f x| ≤ C) (hρ : Integrable ρ volume)
    (hρnonneg : ∀ y, 0 ≤ ρ y) (hρone : ∫ y, ρ y = 1) :
    eVariationOn (fun x => ∫ y, ρ y * f (x - y)) univ ≤ eVariationOn f univ := by
  by_cases hV : eVariationOn f univ = ⊤
  · simp [hV]
  obtain ⟨C, hC⟩ := hbound
  have hint (x : ℝ) : Integrable (fun y => ρ y * f (x - y)) volume := by
    apply hρ.mul_bdd
    · exact (hf.comp_measurable (MeasurableSub.measurable_const_sub x)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using hC (x - y))
  apply iSup_le
  rintro ⟨n, ⟨u, hu, _⟩⟩
  have hpart (y : ℝ) :
      (∑ i ∈ Finset.range n, |f (u (i + 1) - y) - f (u i - y)|) ≤
        (eVariationOn f univ).toReal := by
    apply (ENNReal.ofReal_le_iff_le_toReal hV).mp
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
    simp_rw [← Real.dist_eq, ← edist_dist]
    exact eVariationOn.sum_le (fun i j hij => sub_le_sub_right (hu hij) y) (fun _ => mem_univ _)
  have hterm (i : ℕ) :
      |(∫ y, ρ y * f (u (i + 1) - y)) - (∫ y, ρ y * f (u i - y))| ≤
        ∫ y, ρ y * |f (u (i + 1) - y) - f (u i - y)| := by
    have hdiff : Integrable (fun y => ρ y * (f (u (i + 1) - y) - f (u i - y))) volume := by
      have heq : (fun y => ρ y * (f (u (i + 1) - y) - f (u i - y))) =
          (fun y => ρ y * f (u (i + 1) - y)) - (fun y => ρ y * f (u i - y)) := by
        funext y
        simp only [Pi.sub_apply]
        ring
      rw [heq]
      exact (hint (u (i + 1))).sub (hint (u i))
    calc
      _ = ‖∫ y, ρ y * (f (u (i + 1) - y) - f (u i - y))‖ := by
        simp_rw [mul_sub]
        rw [integral_sub (hint _) (hint _), Real.norm_eq_abs]
      _ ≤ ∫ y, ‖ρ y * (f (u (i + 1) - y) - f (u i - y))‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ y, ρ y * |f (u (i + 1) - y) - f (u i - y)| := by
        congr 1; ext y
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρnonneg y)]
  have htermInt (i : ℕ) :
      Integrable (fun y => ρ y * |f (u (i + 1) - y) - f (u i - y)|) volume := by
    have hdiff : Integrable (fun y => ρ y * (f (u (i + 1) - y) - f (u i - y))) volume := by
      have heq : (fun y => ρ y * (f (u (i + 1) - y) - f (u i - y))) =
          (fun y => ρ y * f (u (i + 1) - y)) - (fun y => ρ y * f (u i - y)) := by
        funext y
        simp only [Pi.sub_apply]
        ring
      rw [heq]
      exact (hint (u (i + 1))).sub (hint (u i))
    convert hdiff.norm using 1
    ext y
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρnonneg y)]
  have hreal :
      (∑ i ∈ Finset.range n,
        |(∫ y, ρ y * f (u (i + 1) - y)) - (∫ y, ρ y * f (u i - y))|) ≤
          (eVariationOn f univ).toReal := by
    calc
      _ ≤ ∑ i ∈ Finset.range n,
          ∫ y, ρ y * |f (u (i + 1) - y) - f (u i - y)| :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ = ∫ y, ∑ i ∈ Finset.range n,
          ρ y * |f (u (i + 1) - y) - f (u i - y)| := by
        rw [integral_finsetSum _ (fun i _ => htermInt i)]
      _ = ∫ y, ρ y * ∑ i ∈ Finset.range n,
          |f (u (i + 1) - y) - f (u i - y)| := by
        congr 1; ext y; rw [Finset.mul_sum]
      _ ≤ ∫ y, ρ y * (eVariationOn f univ).toReal := by
        apply integral_mono
        · simpa only [Finset.mul_sum] using
            (integrable_finsetSum (Finset.range n) (fun i _ => htermInt i))
        · exact hρ.mul_const _
        · intro y
          exact mul_le_mul_of_nonneg_left (hpart y) (hρnonneg y)
      _ = (eVariationOn f univ).toReal := by rw [integral_mul_const, hρone, one_mul]
  simp_rw [edist_dist, Real.dist_eq]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
  exact (ENNReal.ofReal_le_iff_le_toReal hV).mpr hreal

end eVariationOn

namespace BoundedVariationOn

/-- A real BV function on the nonnegative half-line which is right-continuous there
has smooth approximations with no larger half-line variation and pointwise convergence. -/
theorem exists_contDiff_sequence_of_continuousWithinAt_Ici
    {f : ℝ → ℝ} (hf : BoundedVariationOn f (Ici 0))
    (hrc : ∀ v ∈ Ici (0 : ℝ), ContinuousWithinAt f (Ici v) v) :
    ∃ g : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ ∞ (g n)) ∧
      (∀ n, eVariationOn (g n) (Ici 0) ≤ eVariationOn f (Ici 0)) ∧
      (∀ v ∈ Ici (0 : ℝ), Tendsto (fun n => g n v) atTop (𝓝 (f v))) := by
  let F : ℝ → ℝ := fun x => f (max 0 x)
  have hFvar : eVariationOn F univ ≤ eVariationOn f (Ici 0) := by
    exact eVariationOn.comp_le_of_monotoneOn f (fun x : ℝ => max 0 x)
      (fun _ _ _ _ hab => max_le_max_left 0 hab) (fun x _ => le_max_left 0 x)
  have hF : BoundedVariationOn F univ := ne_top_of_le_ne_top hf hFvar
  have hFmeas : StronglyMeasurable F := hF.stronglyMeasurable
  have hFbound : ∃ C : ℝ, ∀ x, |F x| ≤ C := by
    refine ⟨|F 0| + (eVariationOn F univ).toReal, ?_⟩
    intro x
    have hd : ‖F x - F 0‖ ≤ (eVariationOn F univ).toReal := by
      simpa only [dist_eq_norm_sub, norm_sub_rev] using
        (hF.dist_le (Set.mem_univ 0) (Set.mem_univ x))
    calc
      |F x| = ‖F x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖F 0‖ + ‖F x - F 0‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ |F 0| + (eVariationOn F univ).toReal := by
        simpa only [Real.norm_eq_abs] using add_le_add_right hd ‖F 0‖
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hrpos (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  let φ (n : ℕ) : ContDiffBump (0 : ℝ) :=
    ⟨r n / 2, r n, half_pos (hrpos n), half_lt_self (hrpos n)⟩
  let h (n : ℕ) : ℝ → ℝ := (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F
  let g (n : ℕ) : ℝ → ℝ := fun x => h n (x + r n)
  refine ⟨g, ?_, ?_, ?_⟩
  · intro n
    have hh : ContDiff ℝ ∞ (h n) := by
      change ContDiff ℝ ∞
        ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F)
      exact ((φ n).hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ) ((φ n).contDiff_normed (μ := volume) (n := ⊤))
        ((hF.memLp_top (μ := volume)).locallyIntegrable
          (by norm_num : (1 : ENNReal) ≤ ⊤))
    exact hh.comp (contDiff_id.add contDiff_const)
  · intro n
    have hρ : eVariationOn (h n) univ ≤ eVariationOn F univ := by
      have hmain := eVariationOn.integral_sub_le hFmeas hFbound
        (φ n).integrable_normed (φ n).nonneg_normed (φ n).integral_normed
      have heq : h n = (fun x => ∫ y, (φ n).normed volume y * F (x - y)) := by
        funext x
        simp only [h, convolution_lsmul, smul_eq_mul]
      rw [heq]
      exact hmain
    calc
      eVariationOn (g n) (Ici 0) ≤ eVariationOn (h n) univ := by
        exact eVariationOn.comp_le_of_monotoneOn (h n) (fun x : ℝ => x + r n)
          (fun _ _ _ _ hab => add_le_add_left hab _) (fun _ _ => Set.mem_univ _)
      _ ≤ eVariationOn F univ := hρ
      _ ≤ eVariationOn f (Ici 0) := hFvar
  · intro v hv
    have hFv : F v = f v := by simp only [F, max_eq_right hv]
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ :=
      (Metric.continuousWithinAt_iff.mp (hrc v hv)) (ε / 2) (half_pos hε)
    have hr0 : Tendsto r atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      (hr0.eventually (eventually_lt_nhds (half_pos hδpos)))
    refine ⟨N, fun n hn => ?_⟩
    have hrsmall : r n < δ / 2 := hN n hn
    have hball : ∀ z ∈ ball (v + r n) (r n), dist (F z) (F v) ≤ ε / 2 := by
      intro z hz
      have hz' : |z - (v + r n)| < r n := by simpa only [mem_ball, Real.dist_eq] using hz
      have hzlower : v ≤ z := by have := (abs_lt.mp hz').1; linarith
      have hzd : dist z v < δ := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hzlower)]
        have := (abs_lt.mp hz').2
        linarith
      have hzmem : z ∈ Ici v := hzlower
      have hFz : F z = f z := by
        simp only [F, max_eq_right (hv.trans hzlower)]
      rw [hFz, hFv]
      exact (hδ hzmem hzd).le
    have hsupp : Function.support ((φ n).normed volume) ⊆ ball (0 : ℝ) (r n) := by
      rw [(φ n).support_normed_eq]
    have hdist := dist_convolution_le (half_pos hε).le hsupp
      (φ n).nonneg_normed (φ n).integral_normed hFmeas.aestronglyMeasurable hball
    have hgn : dist (g n v) (F v) ≤ ε / 2 := by simpa only [g, h] using hdist
    rw [← hFv]
    exact hgn.trans_lt (half_lt_self hε)

end BoundedVariationOn
