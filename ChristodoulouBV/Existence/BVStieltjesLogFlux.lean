module

public import ChristodoulouBV.Existence.BVStieltjesCalculus
import Mathlib.Tactic

/-!
# Square scalar fluxes for the logarithmic rectangles

The square fluxes are absolutely continuous in the complementary null
coordinate. Their derivatives combine with the scalar product rule to
produce the ordinary corrections in the two logarithmic area primitives.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace ChristodoulouBV

private theorem square_flux_calculus
    {r n z l w k : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hr : AbsolutelyContinuousOnInterval r a b)
    (hn : AbsolutelyContinuousOnInterval n a b)
    (hz : AbsolutelyContinuousOnInterval z a b)
    (hrd : ∀ᵐ t ∂volume, t ∈ Icc a b → deriv r t = l t)
    (hnd : ∀ᵐ t ∂volume, t ∈ Icc a b → deriv n t = k t)
    (hzd : ∀ᵐ t ∂volume, t ∈ Icc a b → deriv z t = -n t * (w t / r t))
    (hrc : ∀ t ∈ Icc a b, c ≤ r t)
    (hnc : ∀ t ∈ Icc a b, (1 / 3 : ℝ) ≤ |n t|) :
    AbsolutelyContinuousOnInterval (fun t => z t ^ 2 / (r t * n t)) a b ∧
      ∀ᵐ t ∂volume, t ∈ Icc a b →
        deriv (fun s => z s ^ 2 / (r s * n s)) t =
          -2 * z t * w t / r t ^ 2 - z t ^ 2 * k t / (r t * n t ^ 2) -
            l t * z t ^ 2 / (r t ^ 2 * n t) := by
  have hnum : AbsolutelyContinuousOnInterval (fun t => z t ^ 2) a b := by
    simpa only [pow_two] using hz.fun_mul hz
  have hden := hr.fun_mul hn
  have hq := hnum.div_and_ae_deriv hden (div_pos hc (by norm_num : (0 : ℝ) < 3)) (by
    intro t ht
    rw [uIcc_of_le hab] at ht
    rw [abs_mul]
    calc
      c / 3 = c * (1 / 3) := by ring
      _ ≤ |r t| * |n t| :=
        mul_le_mul ((hrc t ht).trans (le_abs_self _)) (hnc t ht)
          (by norm_num) (abs_nonneg _))
  refine ⟨hq.1, ?_⟩
  filter_upwards [hq.2, hrd, hnd, hzd, hz.ae_differentiableAt, hr.ae_deriv_mul hn]
    with t hqt hrt hnt hzt hzdiff hprod ht
  have htu : t ∈ uIcc a b := by simpa only [uIcc_of_le hab] using ht
  have hr0 : r t ≠ 0 := (hc.trans_le (hrc t ht)).ne'
  have hn0 : n t ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by norm_num) (hnc t ht))
  rw [hqt htu, deriv_fun_pow' (hzdiff htu) 2, hprod htu,
    hrt ht, hnt ht, hzt ht]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.pred_eq_sub_one, Nat.reduceSub,
    pow_zero, pow_one, add_zero, zero_add]
  field_simp [hr0, hn0]
  ring

/-- The outgoing derivative of the incoming square flux, derived from
canonical weak primitives. The right values of ζ are retained. -/
theorem bv_incoming_square_flux_calculus
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u a b : ℝ} (hab : a ≤ b)
    (hs : outSeg u a b ⊆ globalDomain) :
    let S := d.scalarRightFields
    AbsolutelyContinuousOnInterval (fun t => S.zeta u t ^ 2 / (S.r u t * S.nu u t)) a b ∧
      ∀ᵐ t ∂volume, t ∈ Icc a b →
        deriv (fun s => S.zeta u s ^ 2 / (S.r u s * S.nu u s)) t =
          -2 * S.zeta u t * S.theta u t / S.r u t ^ 2 -
            S.zeta u t ^ 2 * IsBVSolution.radiusCoeff S u t /
              (S.r u t * S.nu u t ^ 2) -
            S.lam u t * S.zeta u t ^ 2 / (S.r u t ^ 2 * S.nu u t) := by
  let S := d.scalarRightFields
  have H := transport_limit_is_solution h hD d
  have hr := H.radius_out_ac_ae hab hs
  have hn := H.nu_out_ac_ae hab hs
  have hz := IntervalPrimitive.ac_ae_of_subsegments hab
    (fun x y hax hxy hyb => bv_zeta_out_primitive h hD d hxy
      ((outSeg_subsegment hax hxy hyb).trans hs))
  have hp : (u, a) ∈ globalDomain := hs ⟨rfl, ⟨le_rfl, hab⟩⟩
  apply square_flux_calculus hab (c := (a - u) / 3)
    (div_pos (sub_pos.mpr hp.2) (by norm_num)) hr.1 hn.1 hz.1 hr.2 hn.2 hz.2
  · intro t ht
    exact (div_le_div_of_nonneg_right (sub_le_sub_right ht.1 u) (by norm_num)).trans
      (d.radius_lower h (p := (u, t)) (hs ⟨rfl, ht⟩))
  · intro t ht
    have hg := (scalar_right_fields_geometry h hD d (u, t) (hs ⟨rfl, ht⟩)).2.2.1
    exact hg.trans (neg_le_abs _)

/-- The incoming derivative of the outgoing square flux is the symmetric
weak identity. No longitudinal differentiability of α is assumed. -/
theorem bv_outgoing_square_flux_calculus
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {v a b : ℝ} (hab : a ≤ b)
    (hs : inSeg v a b ⊆ globalDomain) :
    let S := d.scalarRightFields
    AbsolutelyContinuousOnInterval (fun t => S.theta t v ^ 2 / (S.r t v * S.lam t v)) a b ∧
      ∀ᵐ t ∂volume, t ∈ Icc a b →
        deriv (fun s => S.theta s v ^ 2 / (S.r s v * S.lam s v)) t =
          -2 * S.theta t v * S.zeta t v / S.r t v ^ 2 -
            S.theta t v ^ 2 * IsBVSolution.radiusCoeff S t v /
              (S.r t v * S.lam t v ^ 2) -
            S.nu t v * S.theta t v ^ 2 / (S.r t v ^ 2 * S.lam t v) := by
  let S := d.scalarRightFields
  have H := transport_limit_is_solution h hD d
  have hr := H.radius_in_ac_ae hab hs
  have hl := H.lam_in_ac_ae hab hs
  have hz := IntervalPrimitive.ac_ae_of_subsegments hab
    (fun x y hax hxy hyb => bv_theta_in_primitive h hD d hxy
      ((inSeg_subsegment hax hxy hyb).trans hs))
  have hp : (b, v) ∈ globalDomain := hs ⟨⟨hab, le_rfl⟩, rfl⟩
  apply square_flux_calculus hab (c := (v - b) / 3)
    (div_pos (sub_pos.mpr hp.2) (by norm_num)) hr.1 hl.1 hz.1 hr.2 hl.2 hz.2
  · intro t ht
    exact (div_le_div_of_nonneg_right (sub_le_sub_left ht.2 v) (by norm_num)).trans
      (d.radius_lower h (p := (t, v)) (hs ⟨ht, rfl⟩))
  · intro t ht
    exact ((scalar_right_fields_geometry h hD d (t, v) (hs ⟨ht, rfl⟩)).1).trans
      (le_abs_self _)

/-- The square-flux derivative as a polynomial in the area coefficients.
The flag records the section variable of the associated logarithmic area pair. -/
@[expose] def bvLogSquareAlgebra (incoming : Bool) (c : Fin 9 → ℝ) : ℝ :=
  let θ := c 4 - c 1 * c 3
  let ζ := c 5 - c 2 * c 3
  if incoming then
    -2 * ζ * θ * c 0 ^ 2 - ζ ^ 2 * c 6 * c 0 * c 8 ^ 2 -
      c 1 * ζ ^ 2 * c 0 ^ 2 * c 8
  else
    -2 * θ * ζ * c 0 ^ 2 - θ ^ 2 * c 6 * c 0 * c 7 ^ 2 -
      c 2 * θ ^ 2 * c 0 ^ 2 * c 7

/-- The polynomial square-flux formulas are continuous. -/
theorem bv_log_square_algebra_continuous (incoming : Bool) :
    Continuous (bvLogSquareAlgebra incoming) := by
  change Continuous (fun c => bvLogSquareAlgebra incoming c)
  cases incoming <;>
    simp only [bvLogSquareAlgebra, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

/-- The incoming square flux has the exact outgoing polynomial primitive. -/
theorem bv_incoming_square_flux_primitive
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u a b : ℝ} (hab : a ≤ b)
    (hs : outSeg u a b ⊆ globalDomain) :
    let S := d.scalarRightFields
    IntervalPrimitive (fun t => S.zeta u t ^ 2 / (S.r u t * S.nu u t))
      (fun t => bvLogSquareAlgebra true (areaSectionCoefficients S (u, t))) a b := by
  have hc := bv_incoming_square_flux_calculus h hD d hab hs
  apply IntervalPrimitive.of_ac_ae hab hc.1
  filter_upwards [hc.2] with t ht htI
  rw [ht htI]
  change _ = -2 * d.scalarRightFields.zeta u t * d.scalarRightFields.theta u t *
      (d.scalarRightFields.r u t)⁻¹ ^ 2 - d.scalarRightFields.zeta u t ^ 2 *
      IsBVSolution.radiusCoeff d.scalarRightFields u t * (d.scalarRightFields.r u t)⁻¹ *
      (d.scalarRightFields.nu u t)⁻¹ ^ 2 - d.scalarRightFields.lam u t *
      d.scalarRightFields.zeta u t ^ 2 * (d.scalarRightFields.r u t)⁻¹ ^ 2 *
      (d.scalarRightFields.nu u t)⁻¹
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

/-- The outgoing square flux has the exact incoming polynomial primitive. -/
theorem bv_outgoing_square_flux_primitive
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {v a b : ℝ} (hab : a ≤ b)
    (hs : inSeg v a b ⊆ globalDomain) :
    let S := d.scalarRightFields
    IntervalPrimitive (fun t => S.theta t v ^ 2 / (S.r t v * S.lam t v))
      (fun t => bvLogSquareAlgebra false (areaSectionCoefficients S (t, v))) a b := by
  have hc := bv_outgoing_square_flux_calculus h hD d hab hs
  apply IntervalPrimitive.of_ac_ae hab hc.1
  filter_upwards [hc.2] with t ht htI
  rw [ht htI]
  change _ = -2 * d.scalarRightFields.theta t v * d.scalarRightFields.zeta t v *
      (d.scalarRightFields.r t v)⁻¹ ^ 2 - d.scalarRightFields.theta t v ^ 2 *
      IsBVSolution.radiusCoeff d.scalarRightFields t v * (d.scalarRightFields.r t v)⁻¹ *
      (d.scalarRightFields.lam t v)⁻¹ ^ 2 - d.scalarRightFields.nu t v *
      d.scalarRightFields.theta t v ^ 2 * (d.scalarRightFields.r t v)⁻¹ ^ 2 *
      (d.scalarRightFields.lam t v)⁻¹
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

/-- The ordinary correction in the outgoing logarithmic area is the
sum of the square-flux derivative and the complementary scalar product derivative. -/
theorem bv_log_scalar_product_in_primitive
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {v a b : ℝ} (hab : a ≤ b)
    (hs : inSeg v a b ⊆ globalDomain) :
    let S := d.scalarRightFields
    IntervalPrimitive (fun t => S.theta t v / S.r t v * S.phi t v)
      (fun t => areaSectionQ .phiBetaNu (areaSectionCoefficients S (t, v)) -
        bvLogSquareAlgebra true (areaSectionCoefficients S (t, v))) a b := by
  let S := d.scalarRightFields
  have hF := bv_incoming_mixed_scalar_density h hD d hab hs
  have hφ : AbsolutelyContinuousOnInterval (fun t => S.phi t v) a b :=
    (scalar_limit_absolute_continuity h hD d).2 v a b hab hs
  apply IntervalPrimitive.of_ac_ae hab (hF.1.fun_mul hφ)
  filter_upwards [hF.2, bv_ae_deriv_phi_in h hD d hab hs, hF.1.ae_deriv_mul hφ]
    with t hFt hφt hpt ht
  have htu : t ∈ uIcc a b := by simpa only [uIcc_of_le hab] using ht
  rw [hpt htu, hFt ht, hφt ht]
  have hn : S.nu t v ≠ 0 :=
    (limit_signs_conformal h hD d (t, v) (hs ⟨ht, rfl⟩)).2.2.1.ne
  change -(S.lam t v * S.zeta t v + S.nu t v * S.theta t v) *
      (S.r t v)⁻¹ ^ 2 * S.phi t v + S.theta t v / S.r t v *
      (S.zeta t v / S.r t v) =
    S.beta t v * (S.nu t v)⁻¹ *
      (-(S.lam t v * S.zeta t v + S.nu t v * S.theta t v) * (S.r t v)⁻¹ ^ 2) +
      (S.zeta t v * (S.r t v)⁻¹ *
        (IsBVSolution.radiusCoeff S t v * (S.phi t v * S.nu t v - S.beta t v) *
          (S.nu t v)⁻¹ ^ 2)) - bvLogSquareAlgebra true (areaSectionCoefficients S (t, v))
  change _ = _ + _ - (-2 * S.zeta t v * S.theta t v * (S.r t v)⁻¹ ^ 2 -
    S.zeta t v ^ 2 * IsBVSolution.radiusCoeff S t v * (S.r t v)⁻¹ *
    (S.nu t v)⁻¹ ^ 2 - S.lam t v * S.zeta t v ^ 2 * (S.r t v)⁻¹ ^ 2 * (S.nu t v)⁻¹)
  dsimp only [Fields.zeta]
  field_simp [hn]
  ring

/-- The symmetric scalar product identity for the incoming logarithmic area. -/
theorem bv_log_scalar_product_out_primitive
    {a₀ : ℕ → ℝ → ℝ} {D : ℝ≥0∞} {C : ℝ} {T : ℕ → Fields}
    (h : ∀ n, SmoothSolutionBounds (a₀ n) D C (T n)) (hD : D ≠ ∞)
    (d : RadiusLimitData T) {u a b : ℝ} (hab : a ≤ b)
    (hs : outSeg u a b ⊆ globalDomain) :
    let S := d.scalarRightFields
    IntervalPrimitive (fun t => S.zeta u t / S.r u t * S.phi u t)
      (fun t => areaSectionQ .phiAlphaLam (areaSectionCoefficients S (u, t)) -
        bvLogSquareAlgebra false (areaSectionCoefficients S (u, t))) a b := by
  let S := d.scalarRightFields
  have hF := bv_outgoing_mixed_scalar_density h hD d hab hs
  have hφ : AbsolutelyContinuousOnInterval (S.phi u) a b :=
    (scalar_limit_absolute_continuity h hD d).1 u a b hab hs
  apply IntervalPrimitive.of_ac_ae hab (hF.1.fun_mul hφ)
  filter_upwards [hF.2, bv_ae_deriv_phi_out h hD d hab hs, hF.1.ae_deriv_mul hφ]
    with t hFt hφt hpt ht
  have htu : t ∈ uIcc a b := by simpa only [uIcc_of_le hab] using ht
  rw [hpt htu, hFt ht, hφt ht]
  have hl : S.lam u t ≠ 0 :=
    (limit_signs_conformal h hD d (u, t) (hs ⟨rfl, ht⟩)).2.1.ne'
  change -(S.lam u t * S.zeta u t + S.nu u t * S.theta u t) *
      (S.r u t)⁻¹ ^ 2 * S.phi u t + S.zeta u t / S.r u t *
      (S.theta u t / S.r u t) =
    S.alpha u t * (S.lam u t)⁻¹ *
      (-(S.lam u t * S.zeta u t + S.nu u t * S.theta u t) * (S.r u t)⁻¹ ^ 2) +
      (S.theta u t * (S.r u t)⁻¹ *
        (IsBVSolution.radiusCoeff S u t * (S.phi u t * S.lam u t - S.alpha u t) *
          (S.lam u t)⁻¹ ^ 2)) - bvLogSquareAlgebra false (areaSectionCoefficients S (u, t))
  change _ = _ + _ - (-2 * S.theta u t * S.zeta u t * (S.r u t)⁻¹ ^ 2 -
    S.theta u t ^ 2 * IsBVSolution.radiusCoeff S u t * (S.r u t)⁻¹ *
    (S.lam u t)⁻¹ ^ 2 - S.nu u t * S.theta u t ^ 2 * (S.r u t)⁻¹ ^ 2 * (S.lam u t)⁻¹)
  dsimp only [Fields.theta]
  field_simp [hl]
  ring

end ChristodoulouBV

end
