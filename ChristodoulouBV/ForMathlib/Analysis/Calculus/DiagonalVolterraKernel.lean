module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMeanJetBoxEstimates
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Quadratic kernels of positive weighted diagonal means

The product, quotient, and Volterra primitive are defined for arbitrary real
functions. Estimates impose positivity and continuous first-jet hypotheses.
-/

public section

open Set MeasureTheory
open scoped Interval Topology

namespace intervalIntegral

/-- The quadratic product of a weight and its weighted diagonal error. -/
@[expose] noncomputable def weightedDiagonalQuadraticKernel
    (w f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  w p * (weightedDiagonalError w f p) ^ 2

/-- The quotient of the quadratic product by the weighted vertical radius,
extended by zero on and below the diagonal. -/
@[expose] noncomputable def weightedDiagonalQuotientKernel
    (w f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1 < p.2 then
    weightedDiagonalQuadraticKernel w f p / weightedDiagonalRadius w p
  else 0

/-- The Volterra integral of the quotient kernel over a vertical interval. -/
@[expose] noncomputable def weightedDiagonalVolterraPrimitive
    (w f : ℝ × ℝ → ℝ) (u lower upper : ℝ) : ℝ :=
  ∫ s in lower..upper, weightedDiagonalQuotientKernel w f (u, s)

/-- The quadratic value coefficient for the product kernel. -/
@[expose] noncomputable def weightedDiagonalQuadraticValueCoefficient
    (C B : ℝ) : ℝ := C * B ^ 2

/-- The first-derivative coefficient for the product kernel. -/
@[expose] noncomputable def weightedDiagonalQuadraticDerivativeCoefficient
    (c C B L : ℝ) : ℝ :=
  L * B ^ 2 + 2 * C * B *
    weightedDiagonalErrorDerivativeCoefficient c C B L

/-- The two-input value coefficient for the quadratic product. -/
@[expose] noncomputable def weightedDiagonalQuadraticValueDifferenceCoefficient
    (c C B : ℝ) : ℝ :=
  B ^ 2 + 2 * C * B * weightedDiagonalErrorValueDifferenceCoefficient c C B

/-- The two-input first-derivative coefficient for the quadratic product. -/
@[expose] noncomputable def weightedDiagonalQuadraticDerivativeDifferenceCoefficient
    (c C B L : ℝ) : ℝ :=
  let M := weightedDiagonalErrorValueDifferenceCoefficient c C B
  let H₁ := weightedDiagonalErrorDerivativeCoefficient c C B L
  let N := weightedDiagonalErrorDerivativeDifferenceCoefficient c C B L
  B ^ 2 + 2 * L * B * M + 2 * (B * H₁ + C * M * H₁ + C * B * N)

/-- The linear value coefficient for the quotient kernel. -/
@[expose] noncomputable def weightedDiagonalQuotientValueCoefficient
    (c C B : ℝ) : ℝ := C * B ^ 2 / c

/-- The quadratic product has a continuous first jet on any closed coordinate
triangle on which the weight stays positive. -/
theorem contDiffOn_weightedDiagonalQuadraticKernel
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
    (hc : 0 < c) :
    ContDiffOn ℝ 1 (weightedDiagonalQuadraticKernel w f)
      (closedCoordTriangle a b) := by
  have hwC1 := (convex_closedCoordTriangle a b).contDiffOn_one_of_continuousOn_fderiv
    (isClosed_closedCoordTriangle a b)
    (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
    hw hGw hdw hderivw
  have hHC1 := contDiffOn_weightedDiagonalError hab hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hc
  exact hwC1.mul (hHC1.pow 2)

/-- The coordinate derivative of the quadratic kernel obeys the ordinary
product rule, including on the boundary when the first jets extend there. -/
theorem fderivWithin_weightedDiagonalQuadraticKernel_apply
    {a b : ℝ} (hab : a < b) {w f : ℝ × ℝ → ℝ}
    {Gw : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hjetw : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt w (Gw p) (closedCoordTriangle a b) p)
    (hC1 : ContDiffOn ℝ 1 (weightedDiagonalError w f)
      (closedCoordTriangle a b))
    {p e : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    (fderivWithin ℝ (weightedDiagonalQuadraticKernel w f)
      (closedCoordTriangle a b) p) e =
      Gw p e * (weightedDiagonalError w f p) ^ 2 +
      2 * w p * weightedDiagonalError w f p *
        (fderivWithin ℝ (weightedDiagonalError w f)
          (closedCoordTriangle a b) p) e := by
  let K := closedCoordTriangle a b
  let H := weightedDiagonalError w f
  have hunique : UniqueDiffWithinAt ℝ K p :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab) p hp
  have hdiffH : DifferentiableWithinAt ℝ H K p :=
    hC1.differentiableOn (by norm_num) p hp
  have hdiffw : DifferentiableWithinAt ℝ w K p := (hjetw p hp).differentiableWithinAt
  have hwd : fderivWithin ℝ w K p = Gw p :=
    (hjetw p hp).fderivWithin hunique
  change (fderivWithin ℝ (w * H ^ 2) K p) e = _
  rw [fderivWithin_mul hunique hdiffw (hdiffH.pow 2),
    fderivWithin_pow hunique 2 hdiffH, hwd]
  simp only [add_apply, smul_apply, smul_eq_mul, Pi.pow_apply]
  ring

/-- A pointwise product-rule estimate for the quadratic kernel. -/
theorem abs_fderivWithin_weightedDiagonalQuadraticKernel_apply_le
    {a b : ℝ} (hab : a < b) {w f : ℝ × ℝ → ℝ}
    {Gw : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hjetw : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt w (Gw p) (closedCoordTriangle a b) p)
    (hC1 : ContDiffOn ℝ 1 (weightedDiagonalError w f)
      (closedCoordTriangle a b))
    {C B L H₁ : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hL : 0 ≤ L)
    {p e : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hdle : p.2 - p.1 ≤ 1)
    (hw : |w p| ≤ C) (hGw : |Gw p e| ≤ L)
    (hH : |weightedDiagonalError w f p| ≤ B * (p.2 - p.1))
    (hGH : |(fderivWithin ℝ (weightedDiagonalError w f)
      (closedCoordTriangle a b) p) e| ≤ H₁) :
    |(fderivWithin ℝ (weightedDiagonalQuadraticKernel w f)
      (closedCoordTriangle a b) p) e| ≤
      (L * B ^ 2 + 2 * C * B * H₁) * (p.2 - p.1) := by
  let d := p.2 - p.1
  let H := weightedDiagonalError w f p
  let GH := (fderivWithin ℝ (weightedDiagonalError w f)
    (closedCoordTriangle a b) p) e
  have hd : 0 ≤ d := sub_nonneg.mpr hp.2.1
  have hsq : H ^ 2 ≤ B ^ 2 * d ^ 2 := by
    have hnonneg : 0 ≤ B * d := mul_nonneg hB hd
    have h := (sq_le_sq₀ (abs_nonneg H) hnonneg).2 hH
    nlinarith [sq_abs H]
  have hsq' : H ^ 2 ≤ B ^ 2 * d := by
    have hd2 : d ^ 2 ≤ d := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hd2 (sq_nonneg B)]
  have hfirst : |Gw p e * H ^ 2| ≤ L * B ^ 2 * d := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg H)]
    have h := mul_le_mul hGw hsq' (sq_nonneg H) hL
    nlinarith
  have hsecond : |2 * w p * H * GH| ≤ 2 * C * B * H₁ * d := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hwh : |w p| * |H| ≤ C * (B * d) :=
      mul_le_mul hw hH (abs_nonneg _) hC
    have hprod : |w p| * |H| * |GH| ≤ C * (B * d) * H₁ :=
      mul_le_mul hwh hGH (abs_nonneg GH)
        (mul_nonneg hC (mul_nonneg hB hd))
    nlinarith
  rw [fderivWithin_weightedDiagonalQuadraticKernel_apply hab hjetw hC1 hp]
  exact (abs_add_le _ _).trans (by nlinarith [add_le_add hfirst hsecond])

/-- The exact value difference estimate for two quadratic products follows
from value and difference bounds for their factors. -/
theorem abs_weightedDiagonalQuadraticKernel_sub_le_of_bounds
    {w₁ w₂ f₁ f₂ : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    {C B M D : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hd : 0 ≤ p.2 - p.1)
    (hw₂ : |w₂ p| ≤ C) (hwdiff : |w₁ p - w₂ p| ≤ D)
    (hH₁ : |weightedDiagonalError w₁ f₁ p| ≤ B * (p.2 - p.1))
    (hH₂ : |weightedDiagonalError w₂ f₂ p| ≤ B * (p.2 - p.1))
    (hHdiff : |weightedDiagonalError w₁ f₁ p -
      weightedDiagonalError w₂ f₂ p| ≤ M * (p.2 - p.1) * D) :
    |weightedDiagonalQuadraticKernel w₁ f₁ p -
      weightedDiagonalQuadraticKernel w₂ f₂ p| ≤
      (B ^ 2 + 2 * C * B * M) * (p.2 - p.1) ^ 2 * D := by
  let d := p.2 - p.1
  let H₁ := weightedDiagonalError w₁ f₁ p
  let H₂ := weightedDiagonalError w₂ f₂ p
  have hBd : 0 ≤ B * d := mul_nonneg hB hd
  have hMdD : 0 ≤ M * d * D := mul_nonneg (mul_nonneg hM hd) hD
  have hsq₁ : H₁ ^ 2 ≤ B ^ 2 * d ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg H₁) hBd).2 hH₁
    nlinarith [sq_abs H₁]
  have hsum : |H₁ + H₂| ≤ 2 * B * d := by
    have h := (abs_add_le H₁ H₂).trans (add_le_add hH₁ hH₂)
    nlinarith
  have hsqdiff : |H₁ ^ 2 - H₂ ^ 2| ≤ 2 * B * M * d ^ 2 * D := by
    rw [show H₁ ^ 2 - H₂ ^ 2 = (H₁ - H₂) * (H₁ + H₂) by ring, abs_mul]
    have h := mul_le_mul hHdiff hsum (abs_nonneg _ ) hMdD
    nlinarith
  have hfirst : |(w₁ p - w₂ p) * H₁ ^ 2| ≤ B ^ 2 * d ^ 2 * D := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg H₁)]
    have h := mul_le_mul hwdiff hsq₁ (sq_nonneg H₁) hD
    nlinarith
  have hsecond : |w₂ p * (H₁ ^ 2 - H₂ ^ 2)| ≤
      2 * C * B * M * d ^ 2 * D := by
    rw [abs_mul]
    have h := mul_le_mul hw₂ hsqdiff (abs_nonneg _) hC
    nlinarith
  change |w₁ p * H₁ ^ 2 - w₂ p * H₂ ^ 2| ≤ _
  have hid : w₁ p * H₁ ^ 2 - w₂ p * H₂ ^ 2 =
      (w₁ p - w₂ p) * H₁ ^ 2 + w₂ p * (H₁ ^ 2 - H₂ ^ 2) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (by nlinarith [add_le_add hfirst hsecond])

/-- The quadratic product vanishes on the diagonal. -/
theorem weightedDiagonalQuadraticKernel_diag
    {w f : ℝ × ℝ → ℝ} {u : ℝ} (hw : w (u, u) ≠ 0) :
    weightedDiagonalQuadraticKernel w f (u, u) = 0 := by
  simp [weightedDiagonalQuadraticKernel, weightedDiagonalError_diag hw]

/-- The extended quotient is zero on the diagonal, by definition. -/
theorem weightedDiagonalQuotientKernel_diag
    (w f : ℝ × ℝ → ℝ) (u : ℝ) :
    weightedDiagonalQuotientKernel w f (u, u) = 0 := by
  simp [weightedDiagonalQuotientKernel]

/-- The Volterra primitive vanishes when its integration endpoints agree. -/
theorem weightedDiagonalVolterraPrimitive_self
    (w f : ℝ × ℝ → ℝ) (u v : ℝ) :
    weightedDiagonalVolterraPrimitive w f u v v = 0 := by
  simp [weightedDiagonalVolterraPrimitive]

/-- The quadratic product is nonnegative under a nonnegative weight. -/
theorem weightedDiagonalQuadraticKernel_nonneg
    {w f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hw : 0 ≤ w p) :
    0 ≤ weightedDiagonalQuadraticKernel w f p := by
  exact mul_nonneg hw (sq_nonneg _)

/-- The quadratic product has the exact quadratic value coefficient on a
bounded positive-weight box. -/
theorem weightedDiagonalQuadraticKernel_le_mul_sq_gap
    {a b c C B : ℝ} {w f : ℝ × ℝ → ℝ}
    {Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p ∧ w p ≤ C)
    (hc : 0 < c) (hB : 0 ≤ B)
    (hjet : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt f (Gf p) (closedCoordTriangle a b) p)
    (hvertical : ∀ p ∈ closedCoordTriangle a b, |Gf p (0, 1)| ≤ B)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    weightedDiagonalQuadraticKernel w f p ≤ C * B ^ 2 * (p.2 - p.1) ^ 2 := by
  have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
  have hd : 0 ≤ p.2 - p.1 := sub_nonneg.mpr hcoord.2.1
  have hH := abs_weightedDiagonalError_le_of_jet hw hf
    (fun z hz => (hweight z hz).1) hc hB hjet
    (fun z hz => by simpa only [Real.norm_eq_abs] using hvertical z hz)
    hcoord.1 hcoord.2.1 hcoord.2.2
  have hsq : (weightedDiagonalError w f p) ^ 2 ≤
      (B * (p.2 - p.1)) ^ 2 := by
    have hprod := mul_nonneg
      (sub_nonneg.mpr hH)
      (add_nonneg (mul_nonneg hB hd)
        (abs_nonneg (weightedDiagonalError w f p)))
    nlinarith [sq_abs (weightedDiagonalError w f p)]
  have hC : 0 ≤ C := (hc.le.trans (hweight p hp).1).trans (hweight p hp).2
  have hw0 : 0 ≤ w p := hc.le.trans (hweight p hp).1
  change w p * (weightedDiagonalError w f p) ^ 2 ≤ _
  calc
    _ ≤ C * (B * (p.2 - p.1)) ^ 2 :=
      mul_le_mul (hweight p hp).2 hsq (sq_nonneg _) hC
    _ = C * B ^ 2 * (p.2 - p.1) ^ 2 := by ring

/-- The value and two coordinate first jets of the quadratic kernel obey the
exact product-rule box coefficients. -/
theorem weightedDiagonalQuadraticKernel_bounds_on_jetBox
    {a b c C B L : ℝ} (hab : a < b) (hsize : b - a ≤ 1)
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
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p ∧ w p ≤ C)
    (hGwU : ∀ p ∈ closedCoordTriangle a b, |Gw p (1, 0)| ≤ L)
    (hGwV : ∀ p ∈ closedCoordTriangle a b, |Gw p (0, 1)| ≤ L)
    (hGfU : ∀ p ∈ closedCoordTriangle a b, |Gf p (1, 0)| ≤ L)
    (hGfV : ∀ p ∈ closedCoordTriangle a b, |Gf p (0, 1)| ≤ B)
    (hc : 0 < c) (hB : 0 ≤ B) (hL : 0 ≤ L)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |weightedDiagonalQuadraticKernel w f p| ≤
      weightedDiagonalQuadraticValueCoefficient C B * (p.2 - p.1) ^ 2 ∧
    |(fderivWithin ℝ (weightedDiagonalQuadraticKernel w f)
      (closedCoordTriangle a b) p) (1, 0)| ≤
      weightedDiagonalQuadraticDerivativeCoefficient c C B L * (p.2 - p.1) ∧
    |(fderivWithin ℝ (weightedDiagonalQuadraticKernel w f)
      (closedCoordTriangle a b) p) (0, 1)| ≤
      weightedDiagonalQuadraticDerivativeCoefficient c C B L * (p.2 - p.1) := by
  let K := closedCoordTriangle a b
  have hjetw : ∀ z ∈ K, HasFDerivWithinAt w (Gw z) K z := by
    intro z hz
    exact (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
      (isClosed_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      hw hGw hdw hderivw hz
  have hjetf : ∀ z ∈ K, HasFDerivWithinAt f (Gf z) K z := by
    intro z hz
    exact (convex_closedCoordTriangle a b).hasFDerivWithinAt_of_continuousOn_fderiv
      (isClosed_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
      hf hGf hdf hderivf hz
  have hC1 := contDiffOn_weightedDiagonalError hab hw hf hGw hGf
    hdw hdf hderivw hderivf (fun z hz => (hweight z hz).1) hc
  have hH := weightedDiagonalError_bounds_on_jetBox hab hsize hw hf hGw hGf
    hdw hdf hderivw hderivf hweight hGwU hGfU hGfV hc hB hL hp
  have hC : 0 ≤ C := (hc.le.trans (hweight p hp).1).trans (hweight p hp).2
  have hwabs : |w p| ≤ C := by
    rw [abs_of_nonneg (hc.le.trans (hweight p hp).1)]
    exact (hweight p hp).2
  have hdle : p.2 - p.1 ≤ 1 := by
    have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
    linarith
  have hj0 := weightedDiagonalQuadraticKernel_le_mul_sq_gap hw hf hweight hc hB
    hjetf hGfV hp
  have hjnonneg : 0 ≤ weightedDiagonalQuadraticKernel w f p :=
    weightedDiagonalQuadraticKernel_nonneg (hc.le.trans (hweight p hp).1)
  have hjU := abs_fderivWithin_weightedDiagonalQuadraticKernel_apply_le hab
    hjetw hC1 hC hB hL hp hdle hwabs (hGwU p hp) hH.1 hH.2.1
  have hjV := abs_fderivWithin_weightedDiagonalQuadraticKernel_apply_le hab
    hjetw hC1 hC hB hL hp hdle hwabs (hGwV p hp) hH.1 hH.2.2
  refine ⟨?_, ?_, ?_⟩
  · simpa only [weightedDiagonalQuadraticValueCoefficient,
      abs_of_nonneg hjnonneg] using hj0
  · simpa only [weightedDiagonalQuadraticDerivativeCoefficient] using hjU
  · simpa only [weightedDiagonalQuadraticDerivativeCoefficient] using hjV

/-- The extended quotient kernel is nonnegative and grows at most linearly
from the diagonal. -/
theorem weightedDiagonalQuotientKernel_bounds_on_jetBox
    {a b c C B : ℝ} {w f : ℝ × ℝ → ℝ}
    {Gf : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hw : ContinuousOn w (closedCoordTriangle a b))
    (hf : ContinuousOn f (closedCoordTriangle a b))
    (hweight : ∀ p ∈ closedCoordTriangle a b, c ≤ w p ∧ w p ≤ C)
    (hc : 0 < c) (hB : 0 ≤ B)
    (hjet : ∀ p ∈ closedCoordTriangle a b,
      HasFDerivWithinAt f (Gf p) (closedCoordTriangle a b) p)
    (hvertical : ∀ p ∈ closedCoordTriangle a b, |Gf p (0, 1)| ≤ B)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    0 ≤ weightedDiagonalQuotientKernel w f p ∧
    weightedDiagonalQuotientKernel w f p ≤
      weightedDiagonalQuotientValueCoefficient c C B * (p.2 - p.1) := by
  let d := p.2 - p.1
  have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
  have hd : 0 ≤ d := sub_nonneg.mpr hcoord.2.1
  have hC : 0 ≤ C := (hc.le.trans (hweight p hp).1).trans (hweight p hp).2
  have hj0 : 0 ≤ C * B ^ 2 := mul_nonneg hC (sq_nonneg B)
  have hcoef : 0 ≤ weightedDiagonalQuotientValueCoefficient c C B :=
    div_nonneg hj0 hc.le
  by_cases hlt : p.1 < p.2
  · have hrpos := weightedDiagonalRadius_pos hw (fun z hz => (hweight z hz).1)
      hc hcoord.1 hlt hcoord.2.2
    have hr := mul_sub_le_weightedDiagonalRadius hw
      (fun z hz => (hweight z hz).1) hcoord.1 hlt.le hcoord.2.2
    have hj := weightedDiagonalQuadraticKernel_le_mul_sq_gap hw hf
      hweight hc hB hjet hvertical hp
    have hjnonneg : 0 ≤ weightedDiagonalQuadraticKernel w f p :=
      weightedDiagonalQuadraticKernel_nonneg (hc.le.trans (hweight p hp).1)
    have hcmp : weightedDiagonalQuadraticKernel w f p ≤
        weightedDiagonalQuotientValueCoefficient c C B * d *
          weightedDiagonalRadius w p := by
      calc
        _ ≤ C * B ^ 2 * d ^ 2 := hj
        _ = (weightedDiagonalQuotientValueCoefficient c C B * d) * (c * d) := by
          dsimp [weightedDiagonalQuotientValueCoefficient]
          field_simp
        _ ≤ (weightedDiagonalQuotientValueCoefficient c C B * d) *
              weightedDiagonalRadius w p :=
          mul_le_mul_of_nonneg_left hr (mul_nonneg hcoef hd)
    simp only [weightedDiagonalQuotientKernel, hlt, ↓reduceIte]
    exact ⟨div_nonneg hjnonneg hrpos.le, (div_le_iff₀ hrpos).2 hcmp⟩
  · simp only [weightedDiagonalQuotientKernel, hlt, ↓reduceIte]
    exact ⟨le_rfl, mul_nonneg hcoef hd⟩

end intervalIntegral

end
