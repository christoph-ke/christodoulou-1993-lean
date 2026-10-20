module

public import ChristodoulouBV.C1Solution.UniquenessCoefficientJet
public import ChristodoulouBV.C1Solution.UniquenessRegularProductJetDifference
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Nine-term outgoing jet difference for the mixed coefficient

The factors are the squared-radius mass quotient, the regular product
`λν`, and the reciprocal mass gap. The value difference of the coefficient
is used first, so the outgoing product-jet difference is acyclic.
-/

public section

namespace ChristodoulouBV.C1Solution

/-- The canonical mixed-coefficient outgoing jets satisfy the nine-term
two-input bound on a width-one closed triangle. -/
theorem canonical_mixed_coefficient_vertical_jet_sub_le_difference
    {b₁ b₂ T c C Bv V L ε : ℝ}
    (hT : 0 < T) (hTwidth : T ≤ 1)
    (hT₁ : T < b₁) (hT₂ : T < b₂)
    (hc : 0 < c) (hC : 0 ≤ C) (hBv : 0 ≤ Bv)
    (hV : 0 ≤ V) (hL : 0 ≤ L) (hε : 0 < ε)
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
    (hlamvertical₁ : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (fun q : ℝ × ℝ => S₁.lam q.1 q.2)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ L)
    (hlamvertical₂ : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ L)
    (hgap₁ : ∀ p ∈ closedCoordTriangle 0 T,
      ε ≤ 1 - canonicalMassRatio b₁ S₁ p)
    (hgap₂ : ∀ p ∈ closedCoordTriangle 0 T,
      ε ≤ 1 - canonicalMassRatio b₂ S₂ p)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 T) :
    let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
      hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
    let A0 := B.J₀ / c ^ 2
    let Av := B.Jv / c ^ 2 + 2 * B.J₀ * B.Rv / c ^ 3
    let Ad := B.JΔ / c ^ 2 + 2 * B.J₀ / c ^ 3
    let Adv := B.JΔv / c ^ 2 + 2 * B.Jv / c ^ 3 +
      2 * B.JΔ * B.Rv / c ^ 3 + 2 * B.J₀ * B.RΔv / c ^ 3 +
      6 * B.J₀ * B.Rv / c ^ 4
    let W0 := C * V
    let Wd := V + C
    let Z0 := ε⁻¹
    let Zv := (B.Jv / c + B.J₀ * B.Rv / c ^ 2) / ε ^ 2
    let Zd := (B.JΔ / c + B.J₀ / c ^ 2) / ε ^ 2
    let Zdv := (B.JΔv / c + B.Jv / c ^ 2 +
      B.JΔ * B.Rv / c ^ 2 + B.J₀ * B.RΔv / c ^ 2 +
      2 * B.J₀ * B.Rv / c ^ 3) / ε ^ 2 +
      2 * (B.Jv / c + B.J₀ * B.Rv / c ^ 2) *
        (B.JΔ / c + B.J₀ / c ^ 2) / ε ^ 3
    let K0 := A0 * W0 * Z0
    let Kd := Ad * W0 * Z0 + A0 * Wd * Z0 + A0 * W0 * Zd
    let Wv := L * V + C * K0
    let Wdv := V + L + K0 + C * Kd
    |(fderivWithin ℝ (canonicalMixedCoefficient b₁ S₁)
        (closedCoordTriangle 0 T) p) (0, 1) -
      (fderivWithin ℝ (canonicalMixedCoefficient b₂ S₂)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤
      (Adv * W0 * Z0 + Av * Wd * Z0 + Av * W0 * Zd +
       Ad * Wv * Z0 + A0 * Wdv * Z0 + A0 * Wv * Zd +
       Ad * W0 * Zv + A0 * Wd * Zv + A0 * W0 * Zdv) *
        (outgoingDifference T hT.le S₁ S₂ p.1 +
          incomingDifference T hT.le S₁ S₂ p.1) := by
  dsimp only
  let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
    hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
  let d := p.2 - p.1
  let D := outgoingDifference T hT.le S₁ S₂ p.1
  let N := incomingDifference T hT.le S₁ S₂ p.1
  let E := D + N
  let A0 := B.J₀ / c ^ 2
  let Av := B.Jv / c ^ 2 + 2 * B.J₀ * B.Rv / c ^ 3
  let Ad := B.JΔ / c ^ 2 + 2 * B.J₀ / c ^ 3
  let Adv := B.JΔv / c ^ 2 + 2 * B.Jv / c ^ 3 +
    2 * B.JΔ * B.Rv / c ^ 3 + 2 * B.J₀ * B.RΔv / c ^ 3 +
    6 * B.J₀ * B.Rv / c ^ 4
  let W0 := C * V
  let Wd := V + C
  let Z0 := ε⁻¹
  let Zv := (B.Jv / c + B.J₀ * B.Rv / c ^ 2) / ε ^ 2
  let Zd := (B.JΔ / c + B.J₀ / c ^ 2) / ε ^ 2
  let Zdv := (B.JΔv / c + B.Jv / c ^ 2 +
    B.JΔ * B.Rv / c ^ 2 + B.J₀ * B.RΔv / c ^ 2 +
    2 * B.J₀ * B.Rv / c ^ 3) / ε ^ 2 +
    2 * (B.Jv / c + B.J₀ * B.Rv / c ^ 2) *
      (B.JΔ / c + B.J₀ / c ^ 2) / ε ^ 3
  let K0 := A0 * W0 * Z0
  let Kd := Ad * W0 * Z0 + A0 * Wd * Z0 + A0 * W0 * Zd
  let Wv := L * V + C * K0
  let Wdv := V + L + K0 + C * Kd
  have hcoord := closed_triangle_coordinates hp
  have hd : 0 ≤ d := sub_nonneg.mpr hcoord.2.1
  have hdle : d ≤ 1 := by dsimp [d]; linarith only [hcoord.1, hcoord.2.2, hTwidth]
  have hD : 0 ≤ D := outgoing_difference_nonneg hT hT₁ hT₂ H₁ H₂
    ⟨hcoord.1, hcoord.2.1.trans hcoord.2.2⟩
  have hν := incoming_component_le_difference hT hT₁ hT₂ H₁ H₂
    hcoord.1 hcoord.2.1 hcoord.2.2
  have hN : 0 ≤ N := (abs_nonneg _).trans hν
  have hE : 0 ≤ E := add_nonneg hD hN
  have hDE : D ≤ E := le_add_of_nonneg_right hN
  rcases B.bounds_nonneg with ⟨hJ0, hJv, hJd, hJdv, hRv, hRdv⟩
  have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
  have hAv : 0 ≤ Av := by dsimp [Av]; positivity
  have hAd : 0 ≤ Ad := by dsimp [Ad]; positivity
  have hAdv : 0 ≤ Adv := by dsimp [Adv]; positivity
  have hW0 : 0 ≤ W0 := mul_nonneg hC hV
  have hWd : 0 ≤ Wd := add_nonneg hV hC
  have hZ0 : 0 ≤ Z0 := by dsimp [Z0]; positivity
  have hZv : 0 ≤ Zv := by dsimp [Zv]; positivity
  have hZd : 0 ≤ Zd := by dsimp [Zd]; positivity
  have hZdv : 0 ≤ Zdv := by dsimp [Zdv]; positivity
  have hK0 : 0 ≤ K0 := by dsimp [K0]; positivity
  have hKd : 0 ≤ Kd := by dsimp [Kd]; positivity
  have hWv : 0 ≤ Wv := by dsimp [Wv]; positivity
  have hWdv : 0 ≤ Wdv := by dsimp [Wdv]; positivity
  have hid := canonical_vertical_pair_box_mass_quotients
    hT hTwidth hT₁ hT₂ hc hC hBv H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hp
  have hAvals := B.squaredQuotient_value_bounds hc p hp
  rw [hid.1.2, hid.2.2] at hAvals
  have hAjets := (canonical_mass_quotients_vertical_jet_bounds
    hT hTwidth hT₁ hT₂ hc hC hBv H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hp).2
  have hAdiff := canonical_mass_over_radius_sq_sub_le_difference
    hT hTwidth hT₁ hT₂ hc hC hBv H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hp
  have hAdiffE : |canonicalMassOverRadiusSq b₁ S₁ p -
      canonicalMassOverRadiusSq b₂ S₂ p| ≤ Ad * d * E :=
    hAdiff.trans (mul_le_mul_of_nonneg_left hDE (mul_nonneg hAd hd))
  have hAjetdiff := canonical_mass_over_radius_sq_vertical_jet_sub_le_difference
    hT hTwidth hT₁ hT₂ hc hC hBv H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hp
  have hAjetdiffE : |(fderivWithin ℝ (canonicalMassOverRadiusSq b₁ S₁)
        (closedCoordTriangle 0 T) p) (0, 1) -
      (fderivWithin ℝ (canonicalMassOverRadiusSq b₂ S₂)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Adv * E :=
    hAjetdiff.trans (mul_le_mul_of_nonneg_left hDE hAdv)
  have hWvals := canonical_lam_nu_product_value_bounds
    hT hT₁ hT₂ hC hV H₁ H₂
    (fun q hq => by
      rw [abs_of_nonneg (hc.le.trans (hweight₁ q hq).1)]
      exact (hweight₁ q hq).2)
    (fun q hq => by
      rw [abs_of_nonneg (hc.le.trans (hweight₂ q hq).1)]
      exact (hweight₂ q hq).2)
    hnu₁ hnu₂ hcoord.1 hcoord.2.1 hcoord.2.2
  have hZ := canonical_inverse_mass_gap_vertical_bounds
    hT hTwidth hT₁ hT₂ hc hC hBv hε H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hgap₁ hgap₂ hp
  rcases hZ with ⟨hz₁, hz₂, hzi₁, hzi₂, hzd, hzid⟩
  have hzdE : |(1 - canonicalMassRatio b₁ S₁ p)⁻¹ -
      (1 - canonicalMassRatio b₂ S₂ p)⁻¹| ≤ Zd * d ^ 2 * E :=
    hzd.trans (mul_le_mul_of_nonneg_left hDE
      (mul_nonneg hZd (sq_nonneg d)))
  have hzidE : |(fderivWithin ℝ (canonicalMassRatio b₁ S₁)
        (closedCoordTriangle 0 T) p) (0, 1) /
          (1 - canonicalMassRatio b₁ S₁ p) ^ 2 -
      (fderivWithin ℝ (canonicalMassRatio b₂ S₂)
        (closedCoordTriangle 0 T) p) (0, 1) /
          (1 - canonicalMassRatio b₂ S₂ p) ^ 2| ≤ Zdv * d * E :=
    hzid.trans (mul_le_mul_of_nonneg_left hDE (mul_nonneg hZdv hd))
  have hKdiff := canonical_mixed_coefficient_value_sub_le_difference
    hT hTwidth hT₁ hT₂ hc hC hBv hV hε H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hnu₁ hnu₂
    hgap₁ hgap₂ hp
  have hKdiffE : |canonicalMixedCoefficient b₁ S₁ p -
      canonicalMixedCoefficient b₂ S₂ p| ≤ Kd * d * E := hKdiff
  have hKvals : |canonicalMixedCoefficient b₁ S₁ p| ≤ K0 * d ∧
      |canonicalMixedCoefficient b₂ S₂ p| ≤ K0 * d := by
    constructor
    · simp only [canonicalMixedCoefficient, div_eq_mul_inv, abs_mul]
      calc
        _ ≤ (A0 * d) * C * V * Z0 := by
          gcongr
          · exact hAvals.1
          · rw [abs_of_nonneg (hc.le.trans (hweight₁ p hp).1)]
            exact (hweight₁ p hp).2
          · exact hnu₁ p hp
        _ = K0 * d := by ring
    · simp only [canonicalMixedCoefficient, div_eq_mul_inv, abs_mul]
      calc
        _ ≤ (A0 * d) * C * V * Z0 := by
          gcongr
          · exact hAvals.2
          · rw [abs_of_nonneg (hc.le.trans (hweight₂ p hp).1)]
            exact (hweight₂ p hp).2
          · exact hnu₂ p hp
        _ = K0 * d := by ring
  have hWjets :
      |(fderivWithin ℝ (fun q : ℝ × ℝ => S₁.lam q.1 q.2 * S₁.nu q.1 q.2)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Wv ∧
      |(fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2 * S₂.nu q.1 q.2)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Wv := by
    constructor
    · rw [canonical_lam_nu_vertical_jet_eq hT hT₁ H₁ hp]
      calc
        _ ≤ L * V + C * (K0 * d) := by
          calc
            _ ≤ |(fderivWithin ℝ (fun q : ℝ × ℝ => S₁.lam q.1 q.2)
                   (closedCoordTriangle 0 T) p) (0, 1) * S₁.nu p.1 p.2| +
                |S₁.lam p.1 p.2 * canonicalMixedCoefficient b₁ S₁ p| :=
              abs_add_le _ _
            _ ≤ L * V + C * (K0 * d) := by
              rw [abs_mul, abs_mul]
              gcongr
              · exact hlamvertical₁ p hp
              · exact hnu₁ p hp
              · rw [abs_of_nonneg (hc.le.trans (hweight₁ p hp).1)]
                exact (hweight₁ p hp).2
              · exact hKvals.1
        _ ≤ Wv := by
          dsimp [Wv]
          have hK : K0 * d ≤ K0 := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hdle hK0
          linarith only [mul_le_mul_of_nonneg_left hK hC]
    · rw [canonical_lam_nu_vertical_jet_eq hT hT₂ H₂ hp]
      calc
        _ ≤ L * V + C * (K0 * d) := by
          calc
            _ ≤ |(fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2)
                   (closedCoordTriangle 0 T) p) (0, 1) * S₂.nu p.1 p.2| +
                |S₂.lam p.1 p.2 * canonicalMixedCoefficient b₂ S₂ p| :=
              abs_add_le _ _
            _ ≤ L * V + C * (K0 * d) := by
              rw [abs_mul, abs_mul]
              gcongr
              · exact hlamvertical₂ p hp
              · exact hnu₂ p hp
              · rw [abs_of_nonneg (hc.le.trans (hweight₂ p hp).1)]
                exact (hweight₂ p hp).2
              · exact hKvals.2
        _ ≤ Wv := by
          dsimp [Wv]
          have hK : K0 * d ≤ K0 := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hdle hK0
          linarith only [mul_le_mul_of_nonneg_left hK hC]
  have hWjetdiff := canonical_lam_nu_vertical_jet_sub_le_difference
    hT hTwidth hT₁ hT₂ hc hC hBv hV hL hε H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hnu₁ hnu₂
    hlamvertical₂ hgap₁ hgap₂ hp
  have hEeq : E = outgoingDifference T hT.le S₁ S₂ p.1 +
      incomingDifference T hT.le S₁ S₂ p.1 := rfl
  have hscalar := mixed_coefficient_jet_difference
    hd hdle (show (1 : ℝ) ≤ 1 by norm_num) hE
    hA0 hAv hAd hAdv hW0 hWv hWd hWdv
    hZ0 hZv hZd hZdv
    hAvals.2 hAdiffE hAjets.2 hAjetdiffE
    hWvals.1 hWvals.2.1 hWvals.2.2
    hWjets.1 hWjets.2 hWjetdiff
    hz₁ hzdE hzi₁ hzidE
  rw [canonical_mixed_coefficient_vertical_jet_eq hT hT₁ H₁
      (fun q hq => hε.trans_le (hgap₁ q hq)) hp,
    canonical_mixed_coefficient_vertical_jet_eq hT hT₂ H₂
      (fun q hq => hε.trans_le (hgap₂ q hq)) hp]
  simpa only [one_pow, one_mul, mul_one, hEeq] using hscalar

end ChristodoulouBV.C1Solution

end
