module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBoxJets
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Product jets of removable rational coefficients

The derivative identities in this file are established at interior points,
where ordinary quotient differentiation is valid. The factors and their
first jets are already continuous on the closed triangle.
-/

public section

open Set

namespace intervalIntegral

/-- On the interior, the first jet of the rational cubic coefficient is the
three-factor product-rule jet for the squared quotient, the regular product,
and the reciprocal complementary coefficient. -/
theorem CubicRationalTriangleBox.coefficient_jet_interior
    {a b c ε : ℝ} (B : CubicRationalTriangleBox a b c)
    (hab : a < b) (hc : 0 < c) (hε : 0 < ε)
    (hoff : ∀ p ∈ closedCoordTriangle a b, p.1 < p.2 →
      cubicLinearQuotient B.J B.r p ≤ 1 - ε)
    {p : ℝ × ℝ} (hp : p ∈ interior (closedCoordTriangle a b))
    (e : ℝ × ℝ) :
    (fderivWithin ℝ (rationalCubicCoefficient B.J B.r B.w B.z)
      (closedCoordTriangle a b) p) e =
      (fderivWithin ℝ (cubicSquaredQuotient B.J B.r)
        (closedCoordTriangle a b) p) e *
        (B.w p * B.z p) * (1 - cubicLinearQuotient B.J B.r p)⁻¹ +
      cubicSquaredQuotient B.J B.r p *
        ((fderivWithin ℝ B.w (closedCoordTriangle a b) p) e * B.z p +
          B.w p * (fderivWithin ℝ B.z (closedCoordTriangle a b) p) e) *
        (1 - cubicLinearQuotient B.J B.r p)⁻¹ +
      cubicSquaredQuotient B.J B.r p * (B.w p * B.z p) *
        ((fderivWithin ℝ (cubicLinearQuotient B.J B.r)
          (closedCoordTriangle a b) p) e /
            (1 - cubicLinearQuotient B.J B.r p) ^ 2) := by
  let K := closedCoordTriangle a b
  let A := cubicSquaredQuotient B.J B.r
  let μ := cubicLinearQuotient B.J B.r
  let W : ℝ × ℝ → ℝ := fun q => B.w q * B.z q
  let G : ℝ × ℝ → ℝ := fun q => 1 - μ q
  let T : ℝ × ℝ → ℝ := fun q => W q / G q
  have hpK : p ∈ K := interior_subset hp
  have hnhds : K ∈ nhds p := mem_interior_iff_mem_nhds.mp hp
  have hA₁ := (B.squaredQuotient_hasJet hab hc).1
  have hμ₁ := contDiffOn_cubicLinearQuotient hA₁ B.r_c1 hc
    B.ρ_lower B.r_factor
  have hAa : DifferentiableAt ℝ A p :=
    ((hA₁.differentiableOn (by norm_num)) p hpK).differentiableAt hnhds
  have hμa : DifferentiableAt ℝ μ p :=
    ((hμ₁.differentiableOn (by norm_num)) p hpK).differentiableAt hnhds
  have hwa : DifferentiableAt ℝ B.w p :=
    ((B.w_c1.differentiableOn (by norm_num)) p hpK).differentiableAt hnhds
  have hza : DifferentiableAt ℝ B.z p :=
    ((B.z_c1.differentiableOn (by norm_num)) p hpK).differentiableAt hnhds
  have hWa : DifferentiableAt ℝ W p := hwa.mul hza
  have hGa : DifferentiableAt ℝ G p := by
    exact (differentiableAt_const (c := (1 : ℝ))).sub hμa
  have hGne : G p ≠ 0 := B.complement_ne_zero hε hoff p hpK
  have hTa : DifferentiableAt ℝ T p := by
    change DifferentiableAt ℝ (fun q => W q * (G q)⁻¹) p
    exact hWa.mul (hGa.inv hGne)
  have hKderiv : fderiv ℝ (rationalCubicCoefficient B.J B.r B.w B.z) p =
      A p • fderiv ℝ T p + T p • fderiv ℝ A p := by
    change fderiv ℝ (fun q => A q * T q) p = _
    exact fderiv_fun_mul hAa hTa
  have hTderiv : fderiv ℝ T p =
      (1 / G p) • fderiv ℝ W p -
        (W p / G p ^ 2) • fderiv ℝ G p :=
    fderiv_div_real hWa hGa hGne
  have hWderiv : fderiv ℝ W p =
      B.w p • fderiv ℝ B.z p +
        B.z p • fderiv ℝ B.w p :=
    fderiv_fun_mul hwa hza
  have hGderiv : fderiv ℝ G p = -fderiv ℝ μ p := by
    exact fderiv_const_sub (f := μ) (1 : ℝ)
  have hAderiv : fderivWithin ℝ A K p = fderiv ℝ A p :=
    fderivWithin_of_mem_nhds hnhds
  have hμderiv : fderivWithin ℝ μ K p = fderiv ℝ μ p :=
    fderivWithin_of_mem_nhds hnhds
  have hwderiv : fderivWithin ℝ B.w K p = fderiv ℝ B.w p :=
    fderivWithin_of_mem_nhds hnhds
  have hzderiv : fderivWithin ℝ B.z K p = fderiv ℝ B.z p :=
    fderivWithin_of_mem_nhds hnhds
  have hRderiv : fderivWithin ℝ
      (rationalCubicCoefficient B.J B.r B.w B.z) K p =
      fderiv ℝ (rationalCubicCoefficient B.J B.r B.w B.z) p :=
    fderivWithin_of_mem_nhds hnhds
  rw [hRderiv, hAderiv, hμderiv, hwderiv, hzderiv,
    hKderiv, hTderiv, hWderiv, hGderiv]
  simp only [add_apply, sub_apply, neg_apply, smul_apply, smul_eq_mul]
  dsimp only [T, W, G]
  simp only [div_eq_mul_inv]
  field_simp [hGne]
  ring

/-- On the interior, the source coefficient has the quotient-rule jet of
the product of the rational coefficient and the linearly vanishing source
factor. -/
theorem CubicRationalTriangleBox.source_jet_interior
    {a b c ε : ℝ} (B : CubicRationalTriangleBox a b c)
    (hab : a < b) (hc : 0 < c) (hε : 0 < ε)
    (hoff : ∀ p ∈ closedCoordTriangle a b, p.1 < p.2 →
      cubicLinearQuotient B.J B.r p ≤ 1 - ε)
    {p : ℝ × ℝ} (hp : p ∈ interior (closedCoordTriangle a b))
    (e : ℝ × ℝ) :
    (fderivWithin ℝ (rationalCubicSource B.J B.r B.w B.z B.H)
      (closedCoordTriangle a b) p) e =
      -(((fderivWithin ℝ
          (rationalCubicCoefficient B.J B.r B.w B.z)
          (closedCoordTriangle a b) p) e * B.H p +
        rationalCubicCoefficient B.J B.r B.w B.z p *
          (fderivWithin ℝ B.H (closedCoordTriangle a b) p) e) /
          B.w p) +
      rationalCubicCoefficient B.J B.r B.w B.z p * B.H p *
        (fderivWithin ℝ B.w (closedCoordTriangle a b) p) e /
          B.w p ^ 2 := by
  let K := closedCoordTriangle a b
  let C := rationalCubicCoefficient B.J B.r B.w B.z
  let T : ℝ × ℝ → ℝ := fun q => -B.H q / B.w q
  have hpK : p ∈ K := interior_subset hp
  have hnhds : K ∈ nhds p := mem_interior_iff_mem_nhds.mp hp
  have hC₁ := (B.contDiffOn_coefficients hab hc hε hoff).2.2.1
  have hCa : DifferentiableAt ℝ C p :=
    ((hC₁.differentiableOn (by norm_num)) p hpK).differentiableAt hnhds
  have hHa : DifferentiableAt ℝ B.H p :=
    ((B.H_c1.differentiableOn (by norm_num)) p hpK).differentiableAt hnhds
  have hwa : DifferentiableAt ℝ B.w p :=
    ((B.w_c1.differentiableOn (by norm_num)) p hpK).differentiableAt hnhds
  have hwne : B.w p ≠ 0 :=
    ne_of_gt (hc.trans_le (B.w_lower p hpK))
  have hTa : DifferentiableAt ℝ T p := by
    change DifferentiableAt ℝ
      (fun q => (-B.H q) * (B.w q)⁻¹) p
    exact hHa.neg.mul (hwa.inv hwne)
  have hQderiv : fderiv ℝ
      (rationalCubicSource B.J B.r B.w B.z B.H) p =
        C p • fderiv ℝ T p + T p • fderiv ℝ C p := by
    change fderiv ℝ (fun q => C q * T q) p = _
    exact fderiv_fun_mul hCa hTa
  have hTderiv : fderiv ℝ T p =
      (1 / B.w p) • fderiv ℝ (fun q => -B.H q) p -
        ((-B.H p) / B.w p ^ 2) • fderiv ℝ B.w p :=
    fderiv_div_real hHa.neg hwa hwne
  have hHneg : fderiv ℝ (fun q => -B.H q) p =
      -fderiv ℝ B.H p := fderiv_fun_neg
  have hCrw : fderivWithin ℝ C K p = fderiv ℝ C p :=
    fderivWithin_of_mem_nhds hnhds
  have hHrw : fderivWithin ℝ B.H K p = fderiv ℝ B.H p :=
    fderivWithin_of_mem_nhds hnhds
  have hwrw : fderivWithin ℝ B.w K p = fderiv ℝ B.w p :=
    fderivWithin_of_mem_nhds hnhds
  have hQrw : fderivWithin ℝ
      (rationalCubicSource B.J B.r B.w B.z B.H) K p =
        fderiv ℝ (rationalCubicSource B.J B.r B.w B.z B.H) p :=
    fderivWithin_of_mem_nhds hnhds
  rw [hQrw, hCrw, hHrw, hwrw, hQderiv, hTderiv, hHneg]
  simp only [add_apply, sub_apply, neg_apply, smul_apply, smul_eq_mul]
  dsimp only [T]
  field_simp [hwne]
  ring

end intervalIntegral

end
