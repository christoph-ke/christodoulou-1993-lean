module

public import ChristodoulouBV.C1Solution.UniquenessCoefficientJetDifference
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Common outgoing jet bound for the mixed coefficient

The product-rule bound is paired with the nine-term difference so the source
quotient ledger has both a value and a jet bound for its coefficient.
-/

public section

namespace ChristodoulouBV.C1Solution

/-- The two mixed-coefficient outgoing jets have the common explicit bound
obtained from the squared-radius quotient, regular product, and mass gap. -/
theorem canonical_mixed_coefficient_vertical_jet_bounds
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
    let W0 := C * V
    let Z0 := ε⁻¹
    let Zv := (B.Jv / c + B.J₀ * B.Rv / c ^ 2) / ε ^ 2
    let K0 := A0 * W0 * Z0
    let Wv := L * V + C * K0
    let Kv := Av * W0 * Z0 + A0 * Wv * Z0 + A0 * W0 * Zv
    |(fderivWithin ℝ (canonicalMixedCoefficient b₁ S₁)
      (closedCoordTriangle 0 T) p) (0, 1)| ≤ Kv ∧
    |(fderivWithin ℝ (canonicalMixedCoefficient b₂ S₂)
      (closedCoordTriangle 0 T) p) (0, 1)| ≤ Kv := by
  dsimp only
  let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
    hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
  let d := p.2 - p.1
  let A0 := B.J₀ / c ^ 2
  let Av := B.Jv / c ^ 2 + 2 * B.J₀ * B.Rv / c ^ 3
  let W0 := C * V
  let Z0 := ε⁻¹
  let Zv := (B.Jv / c + B.J₀ * B.Rv / c ^ 2) / ε ^ 2
  let K0 := A0 * W0 * Z0
  let Wv := L * V + C * K0
  let Kv := Av * W0 * Z0 + A0 * Wv * Z0 + A0 * W0 * Zv
  have hcoord := closed_triangle_coordinates hp
  have hd : 0 ≤ d := sub_nonneg.mpr hcoord.2.1
  have hdle : d ≤ 1 := by dsimp [d]; linarith only [hcoord.1, hcoord.2.2, hTwidth]
  rcases B.bounds_nonneg with ⟨hJ0, hJv, _, _, hRv, _⟩
  have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
  have hAv : 0 ≤ Av := by dsimp [Av]; positivity
  have hW0 : 0 ≤ W0 := mul_nonneg hC hV
  have hZv : 0 ≤ Zv := by dsimp [Zv]; positivity
  have hK0 : 0 ≤ K0 := by dsimp [K0]; positivity
  have hWv : 0 ≤ Wv := by dsimp [Wv]; positivity
  have hid := canonical_vertical_pair_box_mass_quotients
    hT hTwidth hT₁ hT₂ hc hC hBv H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hp
  have hAvals := B.squaredQuotient_value_bounds hc p hp
  rw [hid.1.2, hid.2.2] at hAvals
  have hAjets := (canonical_mass_quotients_vertical_jet_bounds
    hT hTwidth hT₁ hT₂ hc hC hBv H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hp).2
  have hZ := canonical_inverse_mass_gap_vertical_bounds
    hT hTwidth hT₁ hT₂ hc hC hBv hε H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hgap₁ hgap₂ hp
  rcases hZ with ⟨hz₁, hz₂, hzi₁, hzi₂, _, _⟩
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
  have hWvals := canonical_lam_nu_product_value_bounds
    hT hT₁ hT₂ hC hV H₁ H₂
    (fun q hq => by
      rw [abs_of_nonneg (hc.le.trans (hweight₁ q hq).1)]
      exact (hweight₁ q hq).2)
    (fun q hq => by
      rw [abs_of_nonneg (hc.le.trans (hweight₂ q hq).1)]
      exact (hweight₂ q hq).2)
    hnu₁ hnu₂ hcoord.1 hcoord.2.1 hcoord.2.2
  have hbound₁ := mixed_coefficient_jet_bound hd hdle
    hA0 hAv hW0 hWv hZv
    hAvals.1 hAjets.1 hWvals.1 hWjets.1 hz₁ hzi₁
  have hbound₂ := mixed_coefficient_jet_bound hd hdle
    hA0 hAv hW0 hWv hZv
    hAvals.2 hAjets.2 hWvals.2.1 hWjets.2 hz₂ hzi₂
  rw [canonical_mixed_coefficient_vertical_jet_eq hT hT₁ H₁
      (fun q hq => hε.trans_le (hgap₁ q hq)) hp,
    canonical_mixed_coefficient_vertical_jet_eq hT hT₂ H₂
      (fun q hq => hε.trans_le (hgap₂ q hq)) hp]
  exact ⟨by simpa only [Kv, one_pow, mul_one] using hbound₁,
    by simpa only [Kv, one_pow, mul_one] using hbound₂⟩

end ChristodoulouBV.C1Solution

end
