module

public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBoxProductJet
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsReciprocal
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsLedger
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Regular factors in a common rational-coefficient box

The extra box fields bound the regular factors and the linearly vanishing
source. The product and reciprocal factors are then derived from them and
from the previously proved removable quotient bounds.
-/

public section

open Set

namespace intervalIntegral

/-- Two cubic rational inputs with a common complementary denominator,
regular-factor, and source-factor bounds. -/
structure CubicRationalFullPairBox (a b c : ℝ) where
  /-- Common cubic numerator and radius bounds. -/
  pair : CubicRationalPairBox a b c
  /-- Lower bound for the complementary denominator. -/
  ε : ℝ
  /-- Positivity of the complementary denominator bound. -/
  ε_pos : 0 < ε
  /-- The first complementary denominator is bounded below. -/
  complement_first : ∀ p ∈ closedCoordTriangle a b,
    ε ≤ 1 - cubicLinearQuotient pair.first.J pair.first.r p
  /-- The second complementary denominator is bounded below. -/
  complement_second : ∀ p ∈ closedCoordTriangle a b,
    ε ≤ 1 - cubicLinearQuotient pair.second.J pair.second.r p
  /-- Bound for the first regular factor. -/
  C : ℝ
  /-- Bound for the second regular factor. -/
  V : ℝ
  /-- Common coordinate-jet bound for both regular factors. -/
  L : ℝ
  /-- Linear bound for the source factor. -/
  H₀ : ℝ
  /-- Coordinate-jet bound for the source factor. -/
  H₁ : ℝ
  /-- Linear source-factor difference bound. -/
  HΔ₀ : ℝ
  /-- Source-factor jet difference bound. -/
  HΔ₁ : ℝ
  /-- Nonnegativity of the first regular-factor bound. -/
  C_nonneg : 0 ≤ C
  /-- Nonnegativity of the second regular-factor bound. -/
  V_nonneg : 0 ≤ V
  /-- Nonnegativity of the regular-factor jet bound. -/
  L_nonneg : 0 ≤ L
  /-- Nonnegativity of the source-factor bound. -/
  H₀_nonneg : 0 ≤ H₀
  /-- Nonnegativity of the source-factor jet bound. -/
  H₁_nonneg : 0 ≤ H₁
  /-- Nonnegativity of the source-factor difference bound. -/
  HΔ₀_nonneg : 0 ≤ HΔ₀
  /-- Nonnegativity of the source-factor jet difference bound. -/
  HΔ₁_nonneg : 0 ≤ HΔ₁
  /-- Common value bounds for the two regular factors. -/
  regular_bound : ∀ p ∈ closedCoordTriangle a b,
    (|pair.first.w p| ≤ C ∧ |pair.second.w p| ≤ C) ∧
    (|pair.first.z p| ≤ V ∧ |pair.second.z p| ≤ V)
  /-- Common coordinate-jet bounds for the regular factors. -/
  regular_jet_bound : ∀ p ∈ closedCoordTriangle a b,
    ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
      (|(fderivWithin ℝ pair.first.w (closedCoordTriangle a b) p) e| ≤ L ∧
       |(fderivWithin ℝ pair.second.w (closedCoordTriangle a b) p) e| ≤ L) ∧
      (|(fderivWithin ℝ pair.first.z (closedCoordTriangle a b) p) e| ≤ L ∧
       |(fderivWithin ℝ pair.second.z (closedCoordTriangle a b) p) e| ≤ L)
  /-- Both regular-factor value differences are bounded by the common
input distance. -/
  regular_sub_bound : ∀ p ∈ closedCoordTriangle a b,
    |pair.first.w p - pair.second.w p| ≤ pair.D ∧
    |pair.first.z p - pair.second.z p| ≤ pair.D
  /-- Both regular-factor jet differences are bounded by the common
input distance. -/
  regular_jet_sub_bound : ∀ p ∈ closedCoordTriangle a b,
    ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
      |(fderivWithin ℝ pair.first.w (closedCoordTriangle a b) p) e -
        (fderivWithin ℝ pair.second.w (closedCoordTriangle a b) p) e| ≤ pair.D ∧
      |(fderivWithin ℝ pair.first.z (closedCoordTriangle a b) p) e -
        (fderivWithin ℝ pair.second.z (closedCoordTriangle a b) p) e| ≤ pair.D
  /-- Both source factors have a common linear gap bound. -/
  source_bound : ∀ p ∈ closedCoordTriangle a b,
    |pair.first.H p| ≤ H₀ * (p.2 - p.1) ∧
    |pair.second.H p| ≤ H₀ * (p.2 - p.1)
  /-- Both source-factor coordinate jets have a common bound. -/
  source_jet_bound : ∀ p ∈ closedCoordTriangle a b,
    ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
      |(fderivWithin ℝ pair.first.H (closedCoordTriangle a b) p) e| ≤ H₁ ∧
      |(fderivWithin ℝ pair.second.H (closedCoordTriangle a b) p) e| ≤ H₁
  /-- The source-factor difference vanishes linearly. -/
  source_sub_bound : ∀ p ∈ closedCoordTriangle a b,
    |pair.first.H p - pair.second.H p| ≤
      HΔ₀ * (p.2 - p.1) * pair.D
  /-- The source-factor jet difference has a common bound. -/
  source_jet_sub_bound : ∀ p ∈ closedCoordTriangle a b,
    ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
      |(fderivWithin ℝ pair.first.H (closedCoordTriangle a b) p) e -
        (fderivWithin ℝ pair.second.H (closedCoordTriangle a b) p) e| ≤
          HΔ₁ * pair.D

/-- The ordinary regular product of the two nonsingular factors. -/
@[expose] noncomputable def CubicRationalTriangleBox.regularProduct
    {a b c : ℝ} (B : CubicRationalTriangleBox a b c)
    (p : ℝ × ℝ) : ℝ := B.w p * B.z p

/-- The coordinate product-rule expression for the regular product. -/
@[expose] noncomputable def CubicRationalTriangleBox.regularProductJet
    {a b c : ℝ} (B : CubicRationalTriangleBox a b c)
    (p e : ℝ × ℝ) : ℝ :=
  (fderivWithin ℝ B.w (closedCoordTriangle a b) p) e * B.z p +
    B.w p * (fderivWithin ℝ B.z (closedCoordTriangle a b) p) e

/-- The relative jet of the regular product is its product-rule
expression on the closed triangle. -/
theorem CubicRationalTriangleBox.regularProduct_jet
    {a b c : ℝ} (B : CubicRationalTriangleBox a b c)
    (hab : a < b) {p : ℝ × ℝ}
    (hp : p ∈ closedCoordTriangle a b) (e : ℝ × ℝ) :
    (fderivWithin ℝ B.regularProduct (closedCoordTriangle a b) p) e =
      B.regularProductJet p e := by
  let K := closedCoordTriangle a b
  have hunique : UniqueDiffWithinAt ℝ K p :=
    (uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact
        openCoordTriangle_nonempty hab)) p hp
  change (fderivWithin ℝ (fun q => B.w q * B.z q) K p) e =
    B.regularProductJet p e
  rw [fderivWithin_fun_mul hunique
    ((B.w_c1.differentiableOn (by norm_num)) p hp)
    ((B.z_c1.differentiableOn (by norm_num)) p hp)]
  simp only [regularProductJet, add_apply, smul_apply, smul_eq_mul]
  ring

/-- The regular product and its coordinate jets obey common value bounds. -/
theorem CubicRationalFullPairBox.regularProduct_bounds
    {a b c : ℝ} (B : CubicRationalFullPairBox a b c) :
    ∀ p ∈ closedCoordTriangle a b,
      ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        |B.pair.first.regularProduct p| ≤ B.C * B.V ∧
        |B.pair.second.regularProduct p| ≤ B.C * B.V ∧
        |B.pair.first.regularProductJet p e| ≤ B.L * (B.C + B.V) ∧
        |B.pair.second.regularProductJet p e| ≤ B.L * (B.C + B.V) := by
  intro p hp e he
  have hv := B.regular_bound p hp
  have hj := B.regular_jet_bound p hp e he
  have hvalue₁ : |B.pair.first.regularProduct p| ≤ B.C * B.V := by
    rw [CubicRationalTriangleBox.regularProduct, abs_mul]
    exact mul_le_mul hv.1.1 hv.2.1 (abs_nonneg _) B.C_nonneg
  have hvalue₂ : |B.pair.second.regularProduct p| ≤ B.C * B.V := by
    rw [CubicRationalTriangleBox.regularProduct, abs_mul]
    exact mul_le_mul hv.1.2 hv.2.2 (abs_nonneg _) B.C_nonneg
  have hjet (w z wi zi : ℝ)
      (hw : |w| ≤ B.C) (hz : |z| ≤ B.V)
      (hwi : |wi| ≤ B.L) (hzi : |zi| ≤ B.L) :
      |wi * z + w * zi| ≤ B.L * (B.C + B.V) := by
    calc
      _ ≤ |wi * z| + |w * zi| := abs_add_le _ _
      _ ≤ B.L * B.V + B.C * B.L := by
        rw [abs_mul, abs_mul]
        exact add_le_add
          (mul_le_mul hwi hz (abs_nonneg _) B.L_nonneg)
          (mul_le_mul hw hzi (abs_nonneg _) B.C_nonneg)
      _ = _ := by ring
  exact ⟨hvalue₁, hvalue₂,
    hjet _ _ _ _ hv.1.1 hv.2.1 hj.1.1 hj.2.1,
    hjet _ _ _ _ hv.1.2 hv.2.2 hj.1.2 hj.2.2⟩

/-- The two-factor difference estimate with independent value and
difference bounds. -/
theorem abs_mul_sub_mul_le_of_bounds
    {x₁ x₂ y₁ y₂ X Y ΔX ΔY : ℝ}
    (hX : 0 ≤ X) (hΔX : 0 ≤ ΔX)
    (hx₂ : |x₂| ≤ X) (hy₁ : |y₁| ≤ Y)
    (hxd : |x₁ - x₂| ≤ ΔX) (hyd : |y₁ - y₂| ≤ ΔY) :
    |x₁ * y₁ - x₂ * y₂| ≤ ΔX * Y + X * ΔY := by
  have hid : x₁ * y₁ - x₂ * y₂ =
      (x₁ - x₂) * y₁ + x₂ * (y₁ - y₂) := by ring
  rw [hid]
  have hfirst : |(x₁ - x₂) * y₁| ≤ ΔX * Y := by
    rw [abs_mul]
    exact mul_le_mul hxd hy₁ (abs_nonneg _) hΔX
  have hsecond : |x₂ * (y₁ - y₂)| ≤ X * ΔY := by
    rw [abs_mul]
    exact mul_le_mul hx₂ hyd (abs_nonneg _) hX
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

/-- The regular products and their coordinate jets satisfy the two-input
difference bounds from the product rule. -/
theorem CubicRationalFullPairBox.regularProduct_sub_bounds
    {a b c : ℝ} (B : CubicRationalFullPairBox a b c) :
    ∀ p ∈ closedCoordTriangle a b,
      ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        |B.pair.first.regularProduct p -
          B.pair.second.regularProduct p| ≤
            (B.C + B.V) * B.pair.D ∧
        |B.pair.first.regularProductJet p e -
          B.pair.second.regularProductJet p e| ≤
            (B.C + B.V + 2 * B.L) * B.pair.D := by
  intro p hp e he
  have hv := B.regular_bound p hp
  have hj := B.regular_jet_bound p hp e he
  have hsub := B.regular_sub_bound p hp
  have hjsub := B.regular_jet_sub_bound p hp e he
  have hW : |B.pair.first.regularProduct p -
      B.pair.second.regularProduct p| ≤ (B.C + B.V) * B.pair.D := by
    have h := abs_mul_sub_mul_le_of_bounds B.C_nonneg B.pair.D_nonneg
      hv.1.2 hv.2.1 hsub.1 hsub.2
    change |B.pair.first.w p * B.pair.first.z p -
      B.pair.second.w p * B.pair.second.z p| ≤ _ 
    convert h using 1
    ring
  have hfirst := abs_mul_sub_mul_le_of_bounds B.L_nonneg B.pair.D_nonneg
    hj.1.2 hv.2.1 hjsub.1 hsub.2
  have hsecond := abs_mul_sub_mul_le_of_bounds B.C_nonneg B.pair.D_nonneg
    hv.1.2 hj.2.1 hsub.1 hjsub.2
  have hWjet : |B.pair.first.regularProductJet p e -
      B.pair.second.regularProductJet p e| ≤
        (B.C + B.V + 2 * B.L) * B.pair.D := by
    change |((fderivWithin ℝ B.pair.first.w
        (closedCoordTriangle a b) p) e * B.pair.first.z p +
        B.pair.first.w p * (fderivWithin ℝ B.pair.first.z
          (closedCoordTriangle a b) p) e) -
      ((fderivWithin ℝ B.pair.second.w
        (closedCoordTriangle a b) p) e * B.pair.second.z p +
        B.pair.second.w p * (fderivWithin ℝ B.pair.second.z
          (closedCoordTriangle a b) p) e)| ≤ _
    have hid (x y x' y' : ℝ) :
        |(x + y) - (x' + y')| ≤ |x - x'| + |y - y'| := by
      have heq : (x + y) - (x' + y') = (x - x') + (y - y') := by ring
      rw [heq]
      exact abs_add_le _ _
    have h := hid
      ((fderivWithin ℝ B.pair.first.w (closedCoordTriangle a b) p) e *
        B.pair.first.z p)
      (B.pair.first.w p *
        (fderivWithin ℝ B.pair.first.z (closedCoordTriangle a b) p) e)
      ((fderivWithin ℝ B.pair.second.w (closedCoordTriangle a b) p) e *
        B.pair.second.z p)
      (B.pair.second.w p *
        (fderivWithin ℝ B.pair.second.z (closedCoordTriangle a b) p) e)
    calc
      _ ≤ _ + _ := h
      _ ≤ (B.pair.D * B.V + B.L * B.pair.D) +
          (B.pair.D * B.L + B.C * B.pair.D) :=
        add_le_add hfirst hsecond
      _ = _ := by ring
  exact ⟨hW, hWjet⟩

/-- The reciprocal of the complementary cubic-over-linear coefficient. -/
@[expose] noncomputable def CubicRationalTriangleBox.inverseComplement
    {a b c : ℝ} (B : CubicRationalTriangleBox a b c)
    (p : ℝ × ℝ) : ℝ :=
  (1 - cubicLinearQuotient B.J B.r p)⁻¹

/-- The ordinary reciprocal-rule coordinate-jet expression. -/
@[expose] noncomputable def CubicRationalTriangleBox.inverseComplementJet
    {a b c : ℝ} (B : CubicRationalTriangleBox a b c)
    (p e : ℝ × ℝ) : ℝ :=
  (fderivWithin ℝ (cubicLinearQuotient B.J B.r)
    (closedCoordTriangle a b) p) e /
      (1 - cubicLinearQuotient B.J B.r p) ^ 2

/-- The reciprocal complement and its coordinate-jet expression have the
common zero-order and first-order bounds on the closed triangle. -/
theorem CubicRationalFullPairBox.inverseComplement_bounds
    {a b c : ℝ} (B : CubicRationalFullPairBox a b c)
    (hab : a < b) (hc : 0 < c) :
    ∀ p ∈ closedCoordTriangle a b,
      ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        |B.pair.first.inverseComplement p| ≤ B.ε⁻¹ ∧
        |B.pair.second.inverseComplement p| ≤ B.ε⁻¹ ∧
        |B.pair.first.inverseComplementJet p e| ≤
          ((B.pair.J₁ / c + B.pair.J₀ * B.pair.R₁ / c ^ 2) /
            B.ε ^ 2) * (p.2 - p.1) ∧
        |B.pair.second.inverseComplementJet p e| ≤
          ((B.pair.J₁ / c + B.pair.J₀ * B.pair.R₁ / c ^ 2) /
            B.ε ^ 2) * (p.2 - p.1) := by
  intro p hp e he
  have hd : 0 ≤ p.2 - p.1 := sub_nonneg.mpr hp.2.1
  have hμi := B.pair.linearQuotient_jet_bounds hab hc p hp e he
  have hM₁ : 0 ≤ B.pair.J₁ / c + B.pair.J₀ * B.pair.R₁ / c ^ 2 := by
    exact add_nonneg (div_nonneg B.pair.J₁_nonneg hc.le)
      (div_nonneg (mul_nonneg B.pair.J₀_nonneg B.pair.R₁_nonneg) (sq_nonneg c))
  exact ⟨inv_one_sub_le B.ε_pos (B.complement_first p hp),
    inv_one_sub_le B.ε_pos (B.complement_second p hp),
    abs_inverseOneSubJet_le_of_gap_bounds B.ε_pos hd hM₁
      (B.complement_first p hp) hμi.1,
    abs_inverseOneSubJet_le_of_gap_bounds B.ε_pos hd hM₁
      (B.complement_second p hp) hμi.2⟩

/-- The reciprocal complementary coefficients retain the quadratic
two-input value difference and linear first-jet difference. -/
theorem CubicRationalFullPairBox.inverseComplement_sub_bounds
    {a b c : ℝ} (B : CubicRationalFullPairBox a b c)
    (hab : a < b) (hc : 0 < c) :
    ∀ p ∈ closedCoordTriangle a b,
      ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        |B.pair.first.inverseComplement p -
          B.pair.second.inverseComplement p| ≤
            ((B.pair.JΔ₀ / c + B.pair.J₀ / c ^ 2) /
              B.ε ^ 2) * (p.2 - p.1) ^ 2 * B.pair.D ∧
        |B.pair.first.inverseComplementJet p e -
          B.pair.second.inverseComplementJet p e| ≤
            ((B.pair.JΔ₁ / c + B.pair.J₁ / c ^ 2 +
                B.pair.JΔ₀ * B.pair.R₁ / c ^ 2 +
                B.pair.J₀ * B.pair.RΔ / c ^ 2 +
                2 * B.pair.J₀ * B.pair.R₁ / c ^ 3) / B.ε ^ 2 +
              2 * (B.pair.J₁ / c + B.pair.J₀ * B.pair.R₁ / c ^ 2) *
                (B.pair.JΔ₀ / c + B.pair.J₀ / c ^ 2) / B.ε ^ 3) *
              (p.2 - p.1) * B.pair.D := by
  intro p hp e he
  have hd : 0 ≤ p.2 - p.1 := sub_nonneg.mpr hp.2.1
  have hdle : p.2 - p.1 ≤ 1 := by
    have hcoord : a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b := hp
    linarith [B.pair.width_le_one]
  have hμd := B.pair.linearQuotient_sub_bound hc p hp
  have hμid := B.pair.linearQuotient_jet_sub_bound hab hc p hp e he
  have hμi := (B.pair.linearQuotient_jet_bounds hab hc p hp e he).2
  have hM₁ : 0 ≤ B.pair.J₁ / c + B.pair.J₀ * B.pair.R₁ / c ^ 2 := by
    exact add_nonneg (div_nonneg B.pair.J₁_nonneg hc.le)
      (div_nonneg (mul_nonneg B.pair.J₀_nonneg B.pair.R₁_nonneg) (sq_nonneg c))
  have hMΔ₀ : 0 ≤ B.pair.JΔ₀ / c + B.pair.J₀ / c ^ 2 := by
    exact add_nonneg (div_nonneg B.pair.JΔ₀_nonneg hc.le)
      (div_nonneg B.pair.J₀_nonneg (sq_nonneg c))
  exact ⟨abs_inv_one_sub_sub_le_of_quadratic_gap_bounds
      B.ε_pos (B.complement_first p hp) (B.complement_second p hp) hμd,
    abs_inverseOneSubJet_sub_le_of_gap_bounds B.ε_pos hd hdle
      B.pair.D_nonneg hM₁ hMΔ₀
      (B.complement_first p hp) (B.complement_second p hp)
      hμd hμi hμid⟩

end intervalIntegral

end
