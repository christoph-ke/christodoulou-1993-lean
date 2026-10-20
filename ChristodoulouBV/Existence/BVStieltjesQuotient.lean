module

public import ChristodoulouBV.Existence.BVStieltjesScalarTransport
public import ChristodoulouBV.Existence.BVStieltjesIntegralTransport
import Mathlib.Tactic

/-!
# Quotient variation from scalar residual variation

The proof bounds finite partition increments before taking their supremum.
The variation of the positive expansion is summed on closed subintervals,
so its jump contributions are retained without a differentiability assumption.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

/-- A BV quotient estimate with a positive expansion and an AC scalar
primitive. Its expansion term includes all jumps of that expansion. -/
theorem bv_quotient_variation_le_residual
    {L Θ φ p R : ℝ → ℝ} {a b P T : ℝ} (hP : 0 ≤ P) (hT : 0 ≤ T)
    (hL : ∀ t ∈ Ioo a b, (1 / 3 : ℝ) ≤ L t)
    (hΘ : ∀ t ∈ Ioo a b, |Θ t| ≤ T)
    (hLBV : BoundedVariationOn L (Ioo a b))
    (hp : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, x ≤ y →
      IntervalIntegrable p volume x y ∧ (∫ t in x..y, |p t|) ≤ P)
    (hφ : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, x ≤ y → φ y - φ x = ∫ t in x..y, p t)
    (hflux : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, x ≤ y →
      IntervalIntegrable (fun t => L t * p t) volume x y)
    (hR : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, x ≤ y →
      R y - R x = Θ y - Θ x + ∫ t in x..y, L t * p t) :
    eVariationOn (fun t => φ t + Θ t / L t) (Ioo a b) ≤
      3 * eVariationOn R (Ioo a b) +
        ENNReal.ofReal (3 * P + 9 * T) * eVariationOn L (Ioo a b) := by
  have hcoef : 0 ≤ 3 * P + 9 * T := by positivity
  have hterm (x : ℝ) (hx : x ∈ Ioo a b) (y : ℝ) (hy : y ∈ Ioo a b) (hxy : x ≤ y) :
      edist (φ y + Θ y / L y) (φ x + Θ x / L x) ≤
        3 * edist (R y) (R x) +
          ENNReal.ofReal (3 * P + 9 * T) * eVariationOn L (Icc x y) := by
    have hs : Icc x y ⊆ Ioo a b := fun _ ht => ⟨hx.1.trans_le ht.1, ht.2.trans_lt hy.2⟩
    have hb := hLBV.mono hs
    let V := (eVariationOn L (Icc x y)).toReal
    have hV : 0 ≤ V := ENNReal.toReal_nonneg
    have hLy : 0 < L y := lt_of_lt_of_le (by norm_num) (hL y hy)
    have hLx : 0 < L x := lt_of_lt_of_le (by norm_num) (hL x hx)
    have hdiff (t : ℝ) (ht : t ∈ Icc x y) : |L y - L t| ≤ V := by
      simpa only [Real.dist_eq] using hb.dist_le ⟨hxy, le_rfl⟩ ht
    have hpi := (hp x hx y hy hxy).1
    have hfi := hflux x hx y hy hxy
    let I := ∫ t in x..y, (L y - L t) * p t
    have hi : IntervalIntegrable (fun t => (L y - L t) * p t) volume x y := by
      convert (hpi.const_mul (L y)).sub hfi using 1
      funext t
      ring
    have hIb : |I| ≤ V * P := by
      calc
        |I| ≤ ∫ t in x..y, |(L y - L t) * p t| :=
          intervalIntegral.abs_integral_le_integral_abs hxy
        _ ≤ ∫ t in x..y, V * |p t| := by
          apply intervalIntegral.integral_mono_on hxy hi.abs (hpi.abs.const_mul V)
          intro t ht
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hdiff t ht) (abs_nonneg _)
        _ = V * ∫ t in x..y, |p t| := intervalIntegral.integral_const_mul _ _
        _ ≤ V * P := mul_le_mul_of_nonneg_left (hp x hx y hy hxy).2 hV
    have hIe : I = L y * (φ y - φ x) - ∫ t in x..y, L t * p t := by
      dsimp only [I]
      simp_rw [sub_mul]
      rw [intervalIntegral.integral_sub (hpi.const_mul (L y)) hfi,
        intervalIntegral.integral_const_mul, ← hφ x hx y hy hxy]
    have he : (φ y + Θ y / L y) - (φ x + Θ x / L x) =
        (R y - R x) / L y + I / L y + Θ x * (L x - L y) / (L x * L y) := by
      rw [hR x hx y hy hxy, hIe]
      field_simp [hLx.ne', hLy.ne']
      ring
    have hfirst : |(R y - R x) / L y| ≤ 3 * |R y - R x| := by
      rw [abs_div, abs_of_pos hLy, div_le_iff₀ hLy]
      have hh := mul_le_mul_of_nonneg_left (hL y hy) (abs_nonneg (R y - R x))
      nlinarith only [hh]
    have hsecond : |I / L y| ≤ 3 * V * P := by
      rw [abs_div, abs_of_pos hLy, div_le_iff₀ hLy]
      have hh := mul_le_mul_of_nonneg_left (hL y hy) (mul_nonneg hV hP)
      nlinarith only [hh, hIb]
    have hthird : |Θ x * (L x - L y) / (L x * L y)| ≤ 9 * T * V := by
      rw [abs_div, abs_mul, abs_of_pos (mul_pos hLx hLy), div_le_iff₀ (mul_pos hLx hLy)]
      have hden : (1 / 9 : ℝ) ≤ L x * L y := by
        have hh := mul_le_mul (hL x hx) (hL y hy) (by norm_num) hLx.le
        norm_num at hh
        exact hh
      have hnum : |Θ x| * |L x - L y| ≤ T * V := by
        rw [abs_sub_comm]
        exact mul_le_mul (hΘ x hx) (hdiff x ⟨le_rfl, hxy⟩) (abs_nonneg _) hT
      have hh := mul_le_mul_of_nonneg_left hden (mul_nonneg hT hV)
      nlinarith only [hnum, hh]
    have hr : |(φ y + Θ y / L y) - (φ x + Θ x / L x)| ≤
        3 * |R y - R x| + (3 * P + 9 * T) * V := by
      rw [he]
      exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
        (by linarith only [hfirst, hsecond, hthird])
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq]
    have hh := ENNReal.ofReal_le_ofReal hr
    rw [ENNReal.ofReal_add (by positivity) (mul_nonneg hcoef hV),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_mul hcoef, ENNReal.ofReal_toReal hb] at hh
    exact hh
  apply iSup_le
  rintro ⟨n, u, hu, hs⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n, (3 * edist (R (u (i + 1))) (R (u i)) +
        ENNReal.ofReal (3 * P + 9 * T) * eVariationOn L (Icc (u i) (u (i + 1)))) :=
      Finset.sum_le_sum fun i _ => hterm _ (hs _) _ (hs _) (hu (Nat.le_succ i))
    _ = 3 * (∑ i ∈ Finset.range n, edist (R (u (i + 1))) (R (u i))) +
        ENNReal.ofReal (3 * P + 9 * T) * eVariationOn L (Icc (u 0) (u n)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, eVariationOn.sum' L hu]
    _ ≤ _ := add_le_add
      (mul_le_mul le_rfl (eVariationOn.sum_le hu hs) bot_le bot_le)
      (mul_le_mul le_rfl (eVariationOn.mono L (show Icc (u 0) (u n) ⊆ Ioo a b from fun t ht =>
        ⟨(hs 0).1.trans_le ht.1, ht.2.trans_lt (hs n).2⟩)) bot_le bot_le)

/-- Removing an integrable correction from a residual costs at most its
absolute integral. This bound also retains jumps of both BV functions. -/
theorem bv_variation_le_residual_add_integral
    {f R g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hgi : IntervalIntegrable g volume a b)
    (hR : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, x ≤ y →
      R y - R x = f y - f x + ∫ t in x..y, g t) :
    eVariationOn f (Ioo a b) ≤ eVariationOn R (Ioo a b) +
      ENNReal.ofReal (∫ t in a..b, |g t|) := by
  have hq (x : ℝ) (hx : x ∈ Ioo a b) (y : ℝ) (hy : y ∈ Ioo a b) (_hxy : x ≤ y) :
      IntervalIntegrable (fun t => -g t) volume x y := by
    apply IntervalIntegrable.neg
    apply hgi.mono_set
    rw [uIcc_of_le hab]
    exact uIcc_subset_Icc ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩
  have hfg (x : ℝ) (hx : x ∈ Ioo a b) (y : ℝ) (hy : y ∈ Ioo a b) (hxy : x ≤ y) :
      (f y - f x) - (R y - R x) = ∫ t in x..y, -g t := by
    rw [intervalIntegral.integral_neg, hR x hx y hy hxy]
    ring
  have hh := stieltjes_variation_transport_integral hq hfg
    (K := fun t => ENNReal.ofReal |g t|)
    (Eventually.of_forall fun t _ => by rw [abs_neg])
  have hi := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hgi.abs).mono_set
    Ioo_subset_Ioc_self
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => abs_nonneg _)]
  exact hh

end ChristodoulouBV

end
