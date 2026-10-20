module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraKernelJet
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraProductDifference
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Quotient estimates for diagonal Volterra kernels

These scalar estimates isolate the exact coefficients produced by the quotient
rule. They apply to arbitrary real numerators and positive denominators.
-/

public section

namespace intervalIntegral

/-- Off the diagonal, the extended quotient kernel obeys the usual quotient
rule for its relative first jet on the closed triangle. -/
theorem fderivWithin_weightedDiagonalQuotientKernel_apply_off_diag
    {a b c : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) {p e : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) (hpdiag : p.1 < p.2) :
    (fderivWithin ℝ (weightedDiagonalQuotientKernel w f)
      (closedCoordTriangle a b) p) e =
      (fderivWithin ℝ (weightedDiagonalQuadraticKernel w f)
        (closedCoordTriangle a b) p) e / weightedDiagonalRadius w p -
      weightedDiagonalQuadraticKernel w f p *
        (fderivWithin ℝ (weightedDiagonalRadius w)
          (closedCoordTriangle a b) p) e /
          (weightedDiagonalRadius w p) ^ 2 := by
  let d := p.2 - p.1
  have hd : 0 < d := sub_pos.mpr hpdiag
  have hρ : 0 < normalizedDiagonalRadius w p :=
    hc.trans_le (le_normalizedDiagonalRadius hw hweight hp)
  have hH : weightedDiagonalError w f p =
      d * verticalJetMean
        (fderivWithin ℝ (weightedDiagonalError w f)
          (closedCoordTriangle a b)) p :=
    weightedDiagonalError_eq_gap_mul_verticalJetMean hab hw hf hGw hGf
      hdw hdf hderivw hderivf hweight hc hp
  have hr : weightedDiagonalRadius w p =
      d * normalizedDiagonalRadius w p :=
    weightedDiagonalRadius_eq_gap_mul_normalized w p.1 p.2
  have hjetw : ∀ z ∈ closedCoordTriangle a b,
      HasFDerivWithinAt w (Gw z) (closedCoordTriangle a b) z := by
    intro z hz
    exact (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
      (isClosed_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      hw hGw hdw hderivw hz
  have hHC1 := contDiffOn_weightedDiagonalError hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc
  rw [fderivWithin_weightedDiagonalQuotientKernel_eq_jet hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc hp,
    fderivWithin_weightedDiagonalQuadraticKernel_apply hab hjetw hHC1 hp]
  dsimp [weightedDiagonalQuotientKernelJet, weightedDiagonalQuadraticKernel]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  rw [hH, hr]
  have halg (d ρ W P A X R : ℝ) (hd : d ≠ 0) (hρ : ρ ≠ 0) :
      d * P ^ 2 / ρ * A + 2 * W * P / ρ * X - W * P ^ 2 / ρ ^ 2 * R =
        (A * (d * P) ^ 2 + 2 * W * (d * P) * X) / (d * ρ) -
          W * (d * P) ^ 2 * R / (d * ρ) ^ 2 := by
    field_simp [hd, hρ]
  exact halg d (normalizedDiagonalRadius w p) (w p)
    (verticalJetMean (fderivWithin ℝ (weightedDiagonalError w f)
      (closedCoordTriangle a b)) p) (Gw p e)
    ((fderivWithin ℝ (weightedDiagonalError w f)
      (closedCoordTriangle a b) p) e)
    ((fderivWithin ℝ (weightedDiagonalRadius w)
      (closedCoordTriangle a b) p) e) hd.ne' hρ.ne'

/-- A quotient-rule derivative stays bounded when its numerator vanishes
quadratically and the denominator vanishes linearly. -/
theorem abs_quotientJet_le_of_bounds
    {c d j₀ j₁ R r j ji ri : ℝ}
    (hc : 0 < c) (hd : 0 < d)
    (hr : c * d ≤ r)
    (hj : |j| ≤ j₀ * d ^ 2)
    (hji : |ji| ≤ j₁ * d)
    (hri : |ri| ≤ R) :
    |ji / r - j * ri / r ^ 2| ≤ j₁ / c + j₀ * R / c ^ 2 := by
  have hrpos : 0 < r := (mul_pos hc hd).trans_le hr
  have hsq : (c * d) ^ 2 ≤ r ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hc.le hd.le) hrpos.le).2 hr
  have hjid : 0 ≤ j₁ * d := (abs_nonneg _).trans hji
  have hprod : |j * ri| ≤ (j₀ * d ^ 2) * R := by
    rw [abs_mul]
    have hj₀ : 0 ≤ j₀ * d ^ 2 := (abs_nonneg _).trans hj
    exact mul_le_mul hj hri (abs_nonneg _) hj₀
  have hprodnonneg : 0 ≤ (j₀ * d ^ 2) * R := (abs_nonneg _).trans hprod
  have hfirst : |ji / r| ≤ j₁ / c := by
    rw [abs_div, abs_of_nonneg hrpos.le]
    calc
      _ ≤ (j₁ * d) / (c * d) := by gcongr
      _ = j₁ / c := by field_simp [hc.ne', hd.ne']
  have hsecond : |j * ri / r ^ 2| ≤ j₀ * R / c ^ 2 := by
    rw [abs_div, abs_of_nonneg (sq_nonneg r)]
    calc
      _ ≤ ((j₀ * d ^ 2) * R) / (c * d) ^ 2 := by gcongr
      _ = j₀ * R / c ^ 2 := by field_simp [hc.ne', hd.ne']
  calc
    _ ≤ |ji / r| + |j * ri / r ^ 2| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (ji / r) (-(j * ri / r ^ 2))
    _ ≤ j₁ / c + j₀ * R / c ^ 2 := add_le_add hfirst hsecond

/-- A pointwise derivative bound for the extended quotient kernel follows
from the quadratic product and radius bounds. -/
theorem abs_fderivWithin_weightedDiagonalQuotientKernel_apply_le_of_bounds
    {a b c j₀ j₁ R : ℝ} (hab : a < b)
    {w f : ℝ × ℝ → ℝ}
    {Gw Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hGw : ContinuousOn Gw (closedCoordTriangle a b))
    (hGf : ContinuousOn Gf (closedCoordTriangle a b))
    (hdw : DifferentiableOn ℝ w (interior (closedCoordTriangle a b)))
    (hdf : DifferentiableOn ℝ f (interior (closedCoordTriangle a b)))
    (hderivw : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ w p = Gw p)
    (hderivf : ∀ p ∈ interior (closedCoordTriangle a b), fderiv ℝ f p = Gf p)
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p)
    (hc : 0 < c) {p e : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) (hpdiag : p.1 < p.2)
    (hj : |weightedDiagonalQuadraticKernel w f p| ≤
      j₀ * (p.2 - p.1) ^ 2)
    (hji : |(fderivWithin ℝ (weightedDiagonalQuadraticKernel w f)
      (closedCoordTriangle a b) p) e| ≤ j₁ * (p.2 - p.1))
    (hri : |(fderivWithin ℝ (weightedDiagonalRadius w)
      (closedCoordTriangle a b) p) e| ≤ R) :
    |(fderivWithin ℝ (weightedDiagonalQuotientKernel w f)
      (closedCoordTriangle a b) p) e| ≤ j₁ / c + j₀ * R / c ^ 2 := by
  have hd : 0 < p.2 - p.1 := sub_pos.mpr hpdiag
  have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := by
    simpa only [closedCoordTriangle, Set.mem_ofPred_eq] using hp
  have hr : c * (p.2 - p.1) ≤ weightedDiagonalRadius w p :=
    mul_sub_le_weightedDiagonalRadius hw hweight hcoord.1 hpdiag.le hcoord.2.2
  rw [fderivWithin_weightedDiagonalQuotientKernel_apply_off_diag hab hw hf
    hGw hGf hdw hdf hderivw hderivf hweight hc hp hpdiag]
  exact abs_quotientJet_le_of_bounds hc hd hr hj hji hri

/-- Reciprocal squares on a positive half-line have the sharp elementary
two-input bound used in quotient jet estimates. -/
theorem abs_inv_sq_sub_inv_sq_le {c x y D : ℝ}
    (hc : 0 < c) (hx : c ≤ x) (hy : c ≤ y)
    (hxy : |x - y| ≤ D) :
    |(x ^ 2)⁻¹ - (y ^ 2)⁻¹| ≤ 2 * D / c ^ 3 := by
  have hxpos : 0 < x := hc.trans_le hx
  have hypos : 0 < y := hc.trans_le hy
  have hD : 0 ≤ D := (abs_nonneg _).trans hxy
  have hrecip : |x⁻¹ - y⁻¹| ≤ D / c ^ 2 := by
    have h := abs_div_sub_div_le hc hx hy (x₁ := (1 : ℝ)) (x₂ := 1)
      (X := 0) (Y := D) (Z := 1) (by simp) hxy (by simp)
    simpa using h
  have hxi : x⁻¹ ≤ c⁻¹ := (inv_le_inv₀ hxpos hc).2 hx
  have hyi : y⁻¹ ≤ c⁻¹ := (inv_le_inv₀ hypos hc).2 hy
  have hsum : |x⁻¹ + y⁻¹| ≤ 2 / c := by
    rw [abs_of_nonneg (add_nonneg (inv_nonneg.mpr hxpos.le)
      (inv_nonneg.mpr hypos.le))]
    have hc_inv : 2 * c⁻¹ = 2 / c := by ring
    rw [← hc_inv]
    linarith
  have hprod := mul_le_mul hrecip hsum (abs_nonneg _) (div_nonneg hD (pow_nonneg hc.le 2))
  have hid : (x ^ 2)⁻¹ - (y ^ 2)⁻¹ =
      (x⁻¹ - y⁻¹) * (x⁻¹ + y⁻¹) := by ring
  rw [hid, abs_mul]
  calc
    _ ≤ (D / c ^ 2) * (2 / c) := hprod
    _ = 2 * D / c ^ 3 := by ring

/-- The two-input quotient-rule coefficient, stated for normalized
numerators and denominators. Its five summands correspond exactly to the
five terms obtained by subtracting two quotient derivatives. -/
theorem abs_quotientJet_sub_le
    {c j₀ j₁ jΔ₀ jΔ₁ R₁ RΔ D : ℝ}
    {ρ₁ ρ₂ J₁ J₂ P₁ P₂ S₁ S₂ : ℝ}
    (hc : 0 < c) (hj₀ : 0 ≤ j₀) (_hj₁ : 0 ≤ j₁)
    (hjΔ₀ : 0 ≤ jΔ₀) (_hjΔ₁ : 0 ≤ jΔ₁)
    (hR₁ : 0 ≤ R₁) (hRΔ : 0 ≤ RΔ) (hD : 0 ≤ D)
    (hρ₁ : c ≤ ρ₁) (hρ₂ : c ≤ ρ₂)
    (hρdiff : |ρ₁ - ρ₂| ≤ D)
    (hJ₂ : |J₂| ≤ j₀) (hJdiff : |J₁ - J₂| ≤ jΔ₀ * D)
    (hP₂ : |P₂| ≤ j₁) (hPdiff : |P₁ - P₂| ≤ jΔ₁ * D)
    (hS₁ : |S₁| ≤ R₁) (hS₂ : |S₂| ≤ R₁)
    (hSdiff : |S₁ - S₂| ≤ RΔ * D) :
    |(P₁ / ρ₁ - J₁ * S₁ / ρ₁ ^ 2) -
      (P₂ / ρ₂ - J₂ * S₂ / ρ₂ ^ 2)| ≤
      (jΔ₁ / c + j₁ / c ^ 2 + jΔ₀ * R₁ / c ^ 2 +
        j₀ * RΔ / c ^ 2 + 2 * j₀ * R₁ / c ^ 3) * D := by
  have hρ₁pos : 0 < ρ₁ := hc.trans_le hρ₁
  have hρ₂pos : 0 < ρ₂ := hc.trans_le hρ₂
  have hfirst := abs_div_sub_div_le hc hρ₁ hρ₂ hPdiff hρdiff hP₂
  have hJprod : |J₁ * S₁ - J₂ * S₂| ≤
      (jΔ₀ * R₁ + j₀ * RΔ) * D := by
    have hid : J₁ * S₁ - J₂ * S₂ =
        (J₁ - J₂) * S₁ + J₂ * (S₁ - S₂) := by ring
    rw [hid]
    have ha : |(J₁ - J₂) * S₁| ≤ jΔ₀ * D * R₁ := by
      rw [abs_mul]
      exact mul_le_mul hJdiff hS₁ (abs_nonneg _) (mul_nonneg hjΔ₀ hD)
    have hb : |J₂ * (S₁ - S₂)| ≤ j₀ * (RΔ * D) := by
      rw [abs_mul]
      exact mul_le_mul hJ₂ hSdiff (abs_nonneg _) hj₀
    have h := (abs_add_le _ _).trans (add_le_add ha hb)
    nlinarith only [h]
  have hJ₂prod : |J₂ * S₂| ≤ j₀ * R₁ := by
    rw [abs_mul]
    exact mul_le_mul hJ₂ hS₂ (abs_nonneg _) hj₀
  have hinvdiff := abs_inv_sq_sub_inv_sq_le hc hρ₁ hρ₂ hρdiff
  have hsecond : |J₁ * S₁ / ρ₁ ^ 2 - J₂ * S₂ / ρ₂ ^ 2| ≤
      ((jΔ₀ * R₁ + j₀ * RΔ) / c ^ 2 +
        2 * j₀ * R₁ / c ^ 3) * D := by
    have hρsq : c ^ 2 ≤ ρ₁ ^ 2 := by nlinarith
    have hA : |(J₁ * S₁ - J₂ * S₂) / ρ₁ ^ 2| ≤
        (jΔ₀ * R₁ + j₀ * RΔ) * D / c ^ 2 := by
      rw [abs_div, abs_of_nonneg (sq_nonneg ρ₁)]
      gcongr
    have hB : |J₂ * S₂ * ((ρ₁ ^ 2)⁻¹ - (ρ₂ ^ 2)⁻¹)| ≤
        j₀ * R₁ * (2 * D / c ^ 3) := by
      rw [abs_mul]
      have hcoef : 0 ≤ j₀ * R₁ := mul_nonneg hj₀ hR₁
      exact mul_le_mul hJ₂prod hinvdiff (abs_nonneg _) hcoef
    have hid : J₁ * S₁ / ρ₁ ^ 2 - J₂ * S₂ / ρ₂ ^ 2 =
        (J₁ * S₁ - J₂ * S₂) / ρ₁ ^ 2 +
          J₂ * S₂ * ((ρ₁ ^ 2)⁻¹ - (ρ₂ ^ 2)⁻¹) := by
      simp only [div_eq_mul_inv]
      ring
    rw [hid]
    have h := (abs_add_le _ _).trans (add_le_add hA hB)
    calc
      _ ≤ (jΔ₀ * R₁ + j₀ * RΔ) * D / c ^ 2 +
          j₀ * R₁ * (2 * D / c ^ 3) := h
      _ = _ := by ring
  have htri : |(P₁ / ρ₁ - P₂ / ρ₂) -
      (J₁ * S₁ / ρ₁ ^ 2 - J₂ * S₂ / ρ₂ ^ 2)| ≤
      |P₁ / ρ₁ - P₂ / ρ₂| +
        |J₁ * S₁ / ρ₁ ^ 2 - J₂ * S₂ / ρ₂ ^ 2| := by
    calc
      _ = |(P₁ / ρ₁ - P₂ / ρ₂) +
          -(J₁ * S₁ / ρ₁ ^ 2 - J₂ * S₂ / ρ₂ ^ 2)| := by ring_nf
      _ ≤ |P₁ / ρ₁ - P₂ / ρ₂| +
          |-(J₁ * S₁ / ρ₁ ^ 2 - J₂ * S₂ / ρ₂ ^ 2)| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have hid : (P₁ / ρ₁ - J₁ * S₁ / ρ₁ ^ 2) -
      (P₂ / ρ₂ - J₂ * S₂ / ρ₂ ^ 2) =
        (P₁ / ρ₁ - P₂ / ρ₂) -
          (J₁ * S₁ / ρ₁ ^ 2 - J₂ * S₂ / ρ₂ ^ 2) := by ring
  rw [hid]
  calc
    _ ≤ |P₁ / ρ₁ - P₂ / ρ₂| +
        |J₁ * S₁ / ρ₁ ^ 2 - J₂ * S₂ / ρ₂ ^ 2| := htri
    _ ≤ (jΔ₁ * D / c + j₁ * D / c ^ 2) +
        ((jΔ₀ * R₁ + j₀ * RΔ) / c ^ 2 + 2 * j₀ * R₁ / c ^ 3) * D :=
      add_le_add hfirst hsecond
    _ = _ := by ring

/-- The two-input value estimate for a quotient whose numerator vanishes
quadratically and denominator grows linearly from the diagonal. -/
theorem abs_weightedDiagonalQuotientKernel_sub_le_of_bounds
    {a b c j₀ jΔ₀ D : ℝ} {w₁ w₂ f₁ f₂ : ℝ × ℝ → ℝ}
    (hw₁ : ContinuousOn w₁ (closedCoordTriangle a b))
    (hw₂ : ContinuousOn w₂ (closedCoordTriangle a b))
    (hweight₁ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₁ p)
    (hweight₂ : ∀ p ∈ closedCoordTriangle a b, c ≤ w₂ p)
    (hc : 0 < c) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) (hpdiag : p.1 < p.2)
    (hj₂ : |weightedDiagonalQuadraticKernel w₂ f₂ p| ≤
      j₀ * (p.2 - p.1) ^ 2)
    (hjdiff : |weightedDiagonalQuadraticKernel w₁ f₁ p -
      weightedDiagonalQuadraticKernel w₂ f₂ p| ≤
        jΔ₀ * (p.2 - p.1) ^ 2 * D)
    (hrdiff : |weightedDiagonalRadius w₁ p -
      weightedDiagonalRadius w₂ p| ≤ (p.2 - p.1) * D) :
    |weightedDiagonalQuotientKernel w₁ f₁ p -
      weightedDiagonalQuotientKernel w₂ f₂ p| ≤
        (jΔ₀ / c + j₀ / c ^ 2) * (p.2 - p.1) * D := by
  let d := p.2 - p.1
  have hd : 0 < d := sub_pos.mpr hpdiag
  simp only [closedCoordTriangle, Set.mem_ofPred_eq] at hp
  have hr₁ : c * d ≤ weightedDiagonalRadius w₁ p :=
    mul_sub_le_weightedDiagonalRadius hw₁ hweight₁ hp.1 hpdiag.le hp.2.2
  have hr₂ : c * d ≤ weightedDiagonalRadius w₂ p :=
    mul_sub_le_weightedDiagonalRadius hw₂ hweight₂ hp.1 hpdiag.le hp.2.2
  have h := abs_div_sub_div_le (mul_pos hc hd) hr₁ hr₂ hjdiff hrdiff hj₂
  simp only [weightedDiagonalQuotientKernel, hpdiag, ↓reduceIte]
  calc
    _ ≤ (jΔ₀ * d ^ 2 * D) / (c * d) +
        (j₀ * d ^ 2) * (d * D) / (c * d) ^ 2 := h
    _ = (jΔ₀ / c + j₀ / c ^ 2) * d * D := by
      field_simp [hc.ne', hd.ne']

private theorem integral_sub_const (u w v : ℝ) :
    (∫ s in w..v, s - u) = ((v - u) ^ 2 - (w - u) ^ 2) / 2 := by
  rw [intervalIntegral.integral_sub]
  · simp [integral_id]
    ring
  · exact continuous_id.intervalIntegrable _ _
  · exact continuous_const.intervalIntegrable _ _

/-- Integrating a function bounded by a line from a fixed base point gives
the exact half-square bound, even when the lower endpoint is above the base. -/
theorem abs_integral_le_half_sq_of_abs_le_linear
    {u w v A : ℝ} {g : ℝ → ℝ}
    (hwv : w ≤ v) (hA : 0 ≤ A)
    (hgi : IntervalIntegrable g MeasureTheory.volume w v)
    (hbound : ∀ s ∈ Set.Icc w v, |g s| ≤ A * (s - u)) :
    |∫ s in w..v, g s| ≤ A * (v - u) ^ 2 / 2 := by
  have hmaj : IntervalIntegrable (fun s : ℝ => A * (s - u))
      MeasureTheory.volume w v :=
    (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have htarget : A * (((v - u) ^ 2 - (w - u) ^ 2) / 2) ≤
      A * (v - u) ^ 2 / 2 := by
    nlinarith [mul_nonneg hA (sq_nonneg (w - u))]
  have hupper : (∫ s in w..v, g s) ≤ A * (v - u) ^ 2 / 2 := by
    have h := intervalIntegral.integral_mono_on hwv hgi hmaj
      (fun s hs => (abs_le.mp (hbound s hs)).2)
    rw [intervalIntegral.integral_const_mul, integral_sub_const] at h
    exact h.trans htarget
  have hlower : -(∫ s in w..v, g s) ≤ A * (v - u) ^ 2 / 2 := by
    have h := intervalIntegral.integral_mono_on hwv hgi.neg hmaj
      (fun s hs => by
        dsimp
        linarith [(abs_le.mp (hbound s hs)).1])
    rw [intervalIntegral.integral_const_mul, integral_sub_const] at h
    simpa only [Pi.neg_apply, intervalIntegral.integral_neg] using h.trans htarget
  exact abs_le.mpr ⟨by linarith, hupper⟩

/-- The Volterra primitives of two kernels inherit a half-square difference
bound from a linear pointwise difference estimate. -/
theorem abs_weightedDiagonalVolterraPrimitive_sub_le_of_bounds
    {u w v A D : ℝ} {w₁ w₂ f₁ f₂ : ℝ × ℝ → ℝ}
    (hwv : w ≤ v) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hi₁ : IntervalIntegrable
      (fun s => weightedDiagonalQuotientKernel w₁ f₁ (u, s))
      MeasureTheory.volume w v)
    (hi₂ : IntervalIntegrable
      (fun s => weightedDiagonalQuotientKernel w₂ f₂ (u, s))
      MeasureTheory.volume w v)
    (hbound : ∀ s ∈ Set.Icc w v,
      |weightedDiagonalQuotientKernel w₁ f₁ (u, s) -
        weightedDiagonalQuotientKernel w₂ f₂ (u, s)| ≤ A * (s - u) * D) :
    |weightedDiagonalVolterraPrimitive w₁ f₁ u w v -
      weightedDiagonalVolterraPrimitive w₂ f₂ u w v| ≤
        A * (v - u) ^ 2 * D / 2 := by
  have h := abs_integral_le_half_sq_of_abs_le_linear hwv
    (mul_nonneg hA hD) (hi₁.sub hi₂) (fun s hs => by
      simpa only [Pi.sub_apply, mul_assoc, mul_comm, mul_left_comm] using hbound s hs)
  simp only [weightedDiagonalVolterraPrimitive,
    intervalIntegral.integral_sub hi₁ hi₂] at h ⊢
  calc
    _ ≤ A * D * (v - u) ^ 2 / 2 := h
    _ = _ := by ring

/-- A nonnegative linearly growing kernel has a nonnegative Volterra
primitive bounded by half the squared distance from its base point. -/
theorem weightedDiagonalVolterraPrimitive_nonneg_le_of_bounds
    {u w v A : ℝ} {weight f : ℝ × ℝ → ℝ}
    (hwv : w ≤ v) (hA : 0 ≤ A)
    (hi : IntervalIntegrable
      (fun s => weightedDiagonalQuotientKernel weight f (u, s))
      MeasureTheory.volume w v)
    (hbound : ∀ s ∈ Set.Icc w v,
      0 ≤ weightedDiagonalQuotientKernel weight f (u, s) ∧
      weightedDiagonalQuotientKernel weight f (u, s) ≤ A * (s - u)) :
    0 ≤ weightedDiagonalVolterraPrimitive weight f u w v ∧
      weightedDiagonalVolterraPrimitive weight f u w v ≤
        A * (v - u) ^ 2 / 2 := by
  have hmaj : IntervalIntegrable (fun s : ℝ => A * (s - u))
      MeasureTheory.volume w v :=
    (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have hupper := intervalIntegral.integral_mono_on hwv hi hmaj
    (fun s hs => (hbound s hs).2)
  rw [intervalIntegral.integral_const_mul, integral_sub_const] at hupper
  have htarget : A * (((v - u) ^ 2 - (w - u) ^ 2) / 2) ≤
      A * (v - u) ^ 2 / 2 := by
    nlinarith [mul_nonneg hA (sq_nonneg (w - u))]
  simp only [weightedDiagonalVolterraPrimitive]
  exact ⟨intervalIntegral.integral_nonneg hwv (fun s hs => (hbound s hs).1),
    hupper.trans htarget⟩

end intervalIntegral

end
