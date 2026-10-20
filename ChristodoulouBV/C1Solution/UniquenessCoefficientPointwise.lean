module

public import ChristodoulouBV.C1Solution.UniquenessRegularProduct
public import ChristodoulouBV.C1Solution.UniquenessLedger
import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBoxFactors
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Pointwise incoming difference for the mixed coefficient

The estimate uses the already obtained differences of the squared-radius
mass quotient, regular product, and reciprocal mass gap. The incoming
factor is the value difference at the current point, which permits a
scalar Gronwall argument along one outgoing ray.
-/

public section

namespace ChristodoulouBV.C1Solution

/-- The mixed-coefficient value difference uses only the outgoing moving
seminorm and the incoming difference at the current point. -/
theorem canonical_mixed_coefficient_value_sub_le_pointwise
    {b₁ b₂ T c C Bv V ε : ℝ}
    (hT : 0 < T) (hTwidth : T ≤ 1)
    (hT₁ : T < b₁) (hT₂ : T < b₂)
    (hc : 0 < c) (hC : 0 ≤ C) (hBv : 0 ≤ Bv)
    (hV : 0 ≤ V) (hε : 0 < ε)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hweight₁ : ∀ p ∈ closedCoordTriangle 0 T,
      c ≤ S₁.lam p.1 p.2 ∧ S₁.lam p.1 p.2 ≤ C)
    (hweight₂ : ∀ p ∈ closedCoordTriangle 0 T,
      c ≤ S₂.lam p.1 p.2 ∧ S₂.lam p.1 p.2 ≤ C)
    (hhvertical₁ : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (outgoingQuotient S₁)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Bv)
    (hhvertical₂ : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (outgoingQuotient S₂)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Bv)
    (hnu₁ : ∀ p ∈ closedCoordTriangle 0 T,
      |S₁.nu p.1 p.2| ≤ V)
    (hnu₂ : ∀ p ∈ closedCoordTriangle 0 T,
      |S₂.nu p.1 p.2| ≤ V)
    (hgap₁ : ∀ p ∈ closedCoordTriangle 0 T,
      ε ≤ 1 - canonicalMassRatio b₁ S₁ p)
    (hgap₂ : ∀ p ∈ closedCoordTriangle 0 T,
      ε ≤ 1 - canonicalMassRatio b₂ S₂ p)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 T) :
    let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
      hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
    let A0 := B.J₀ / c ^ 2
    let Ad := B.JΔ / c ^ 2 + 2 * B.J₀ / c ^ 3
    let W0 := C * V
    let Wd := V + C
    let Z0 := ε⁻¹
    let Zd := (B.JΔ / c + B.J₀ / c ^ 2) / ε ^ 2
    |canonicalMixedCoefficient b₁ S₁ p -
      canonicalMixedCoefficient b₂ S₂ p| ≤
        (Ad * W0 * Z0 + A0 * Wd * Z0 + A0 * W0 * Zd) *
          (p.2 - p.1) *
            (outgoingDifference T hT.le S₁ S₂ p.1 +
              |S₁.nu p.1 p.2 - S₂.nu p.1 p.2|) := by
  dsimp only
  let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
    hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
  let d := p.2 - p.1
  let D := outgoingDifference T hT.le S₁ S₂ p.1
  let N := |S₁.nu p.1 p.2 - S₂.nu p.1 p.2|
  let E := D + N
  let A0 := B.J₀ / c ^ 2
  let Ad := B.JΔ / c ^ 2 + 2 * B.J₀ / c ^ 3
  let W0 := C * V
  let Wd := V + C
  let Z0 := ε⁻¹
  let Zd := (B.JΔ / c + B.J₀ / c ^ 2) / ε ^ 2
  have hcoord := closed_triangle_coordinates hp
  have hd : 0 ≤ d := sub_nonneg.mpr hcoord.2.1
  have hdle : d ≤ 1 := by dsimp [d]; linarith only [hcoord.1, hcoord.2.2, hTwidth]
  have hD : 0 ≤ D := outgoing_difference_nonneg hT hT₁ hT₂ H₁ H₂
    ⟨hcoord.1, hcoord.2.1.trans hcoord.2.2⟩
  have hN : 0 ≤ N := abs_nonneg _
  have hE : 0 ≤ E := add_nonneg hD hN
  have hDE : D ≤ E := le_add_of_nonneg_right hN
  rcases B.bounds_nonneg with ⟨hJ0, _, hJd, _, _, _⟩
  have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
  have hAd : 0 ≤ Ad := by dsimp [Ad]; positivity
  have hW0 : 0 ≤ W0 := mul_nonneg hC hV
  have hWd : 0 ≤ Wd := add_nonneg hV hC
  have hZd : 0 ≤ Zd := by dsimp [Zd]; positivity
  have hid := canonical_vertical_pair_box_mass_quotients
    hT hTwidth hT₁ hT₂ hc hC hBv H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hp
  have hAvals := B.squaredQuotient_value_bounds hc p hp
  rw [hid.1.2, hid.2.2] at hAvals
  have hAdiff := canonical_mass_over_radius_sq_sub_le_difference
    hT hTwidth hT₁ hT₂ hc hC hBv H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hp
  have hAdiffE : |canonicalMassOverRadiusSq b₁ S₁ p -
      canonicalMassOverRadiusSq b₂ S₂ p| ≤ Ad * d * E := by
    calc
      _ ≤ Ad * d * D := hAdiff
      _ ≤ Ad * d * E := mul_le_mul_of_nonneg_left hDE
        (mul_nonneg hAd hd)
  have hW := canonical_lam_nu_product_value_bounds
    hT hT₁ hT₂ hC hV H₁ H₂
    (fun q hq => by
      rw [abs_of_nonneg (hc.le.trans (hweight₁ q hq).1)]
      exact (hweight₁ q hq).2)
    (fun q hq => by
      rw [abs_of_nonneg (hc.le.trans (hweight₂ q hq).1)]
      exact (hweight₂ q hq).2)
    hnu₁ hnu₂ hcoord.1 hcoord.2.1 hcoord.2.2
  have hWdiff : |S₁.lam p.1 p.2 * S₁.nu p.1 p.2 -
      S₂.lam p.1 p.2 * S₂.nu p.1 p.2| ≤ Wd * E := by
    have hlamdiff := (outgoing_components_le_difference
      hT hT₁ hT₂ H₁ H₂ hcoord.1 hcoord.2.1 hcoord.2.2).1
    have hraw := intervalIntegral.abs_mul_sub_mul_le_of_bounds hC hD
      (by rw [abs_of_nonneg (hc.le.trans (hweight₂ p hp).1)]
          exact (hweight₂ p hp).2)
      (hnu₁ p hp) hlamdiff (show |S₁.nu p.1 p.2 - S₂.nu p.1 p.2| ≤ N from le_rfl)
    calc
      _ ≤ D * V + C * N := hraw
      _ ≤ Wd * E := by dsimp [Wd, E]; nlinarith only [hC, hV, hD, hN]
  have hZ := canonical_inverse_mass_gap_vertical_bounds
    hT hTwidth hT₁ hT₂ hc hC hBv hε H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hgap₁ hgap₂ hp
  rcases hZ with ⟨hz₁, hz₂, _, _, hzd, _⟩
  have hzdE : |(1 - canonicalMassRatio b₁ S₁ p)⁻¹ -
      (1 - canonicalMassRatio b₂ S₂ p)⁻¹| ≤ Zd * d ^ 2 * E := by
    calc
      _ ≤ Zd * d ^ 2 * D := hzd
      _ ≤ Zd * d ^ 2 * E := mul_le_mul_of_nonneg_left hDE
        (mul_nonneg hZd (sq_nonneg d))
  have h := mixed_coefficient_value_difference
    hd hdle (show (1 : ℝ) ≤ 1 by norm_num) hE
    hA0 hAd hW0 hWd hZd
    hAvals.2 hAdiffE hW.1 hW.2.1 hWdiff hz₁ hzdE
  have hK₁ : canonicalMixedCoefficient b₁ S₁ p =
      canonicalMassOverRadiusSq b₁ S₁ p *
        (S₁.lam p.1 p.2 * S₁.nu p.1 p.2) *
        (1 - canonicalMassRatio b₁ S₁ p)⁻¹ := by
    simp only [canonicalMixedCoefficient, div_eq_mul_inv]
    ring
  have hK₂ : canonicalMixedCoefficient b₂ S₂ p =
      canonicalMassOverRadiusSq b₂ S₂ p *
        (S₂.lam p.1 p.2 * S₂.nu p.1 p.2) *
        (1 - canonicalMassRatio b₂ S₂ p)⁻¹ := by
    simp only [canonicalMixedCoefficient, div_eq_mul_inv]
    ring
  rw [hK₁, hK₂]
  simpa only [one_pow, mul_one] using h

end ChristodoulouBV.C1Solution

end
