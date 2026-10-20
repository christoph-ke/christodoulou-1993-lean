module

public import ChristodoulouBV.C1Solution.UniquenessSourceJet
public import ChristodoulouBV.C1Solution.UniquenessDifference
public import ChristodoulouBV.C1Solution.UniquenessKernelValueJets
public import ChristodoulouBV.C1Solution.UniquenessLedger
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Canonical quotient-source differences

The source factor and the mixed coefficient feed the two-factor product
and quotient rows of the unrestricted uniqueness ledger.
-/

public section

namespace ChristodoulouBV.C1Solution

/-- The quotient source and its outgoing jet satisfy the value and jet
two-solution estimates at width at most one. -/
theorem canonical_quotient_source_value_vertical_jet_sub_le_difference
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
    let Kv := Av * W0 * Z0 + A0 * Wv * Z0 + A0 * W0 * Zv
    let Kdv := Adv * W0 * Z0 + Av * Wd * Z0 + Av * W0 * Zd +
      Ad * Wv * Z0 + A0 * Wdv * Z0 + A0 * Wv * Zd +
      Ad * W0 * Zv + A0 * Wd * Zv + A0 * W0 * Zdv
    let H0 := Bv
    let Hv := Bv + C * Bv / c
    let Hd := (Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2)
    let Hdv := 1 + (Bv + C * Hd) / c + C * Bv / c ^ 2
    let P0 := K0 * H0
    let Pv := Kv * H0 + K0 * Hv
    let Pd := Kd * H0 + K0 * Hd
    let Pdv := Kdv * H0 + Kv * Hd + Kd * Hv + K0 * Hdv
    |canonicalQuotientSource b₁ S₁ p -
      canonicalQuotientSource b₂ S₂ p| ≤
        (Pd / c + P0 / c ^ 2) * (p.2 - p.1) ^ 2 *
          (outgoingDifference T hT.le S₁ S₂ p.1 +
            incomingDifference T hT.le S₁ S₂ p.1) ∧
    |(fderivWithin ℝ (canonicalQuotientSource b₁ S₁)
        (closedCoordTriangle 0 T) p) (0, 1) -
      (fderivWithin ℝ (canonicalQuotientSource b₂ S₂)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤
        (Pdv / c + Pv / c ^ 2 + Pd * L / c ^ 2 +
          P0 / c ^ 2 + 2 * P0 * L / c ^ 3) *
          (p.2 - p.1) *
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
  let Kv := Av * W0 * Z0 + A0 * Wv * Z0 + A0 * W0 * Zv
  let Kdv := Adv * W0 * Z0 + Av * Wd * Z0 + Av * W0 * Zd +
    Ad * Wv * Z0 + A0 * Wdv * Z0 + A0 * Wv * Zd +
    Ad * W0 * Zv + A0 * Wd * Zv + A0 * W0 * Zdv
  let H0 := Bv
  let Hv := Bv + C * Bv / c
  let Hd := (Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2)
  let Hdv := 1 + (Bv + C * Hd) / c + C * Bv / c ^ 2
  let P0 := K0 * H0
  let Pv := Kv * H0 + K0 * Hv
  let Pd := Kd * H0 + K0 * Hd
  let Pdv := Kdv * H0 + Kv * Hd + Kd * Hv + K0 * Hdv
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
  have hKv : 0 ≤ Kv := by dsimp [Kv]; positivity
  have hKdv : 0 ≤ Kdv := by dsimp [Kdv]; positivity
  have hH0 : 0 ≤ H0 := hBv
  have hHv : 0 ≤ Hv := by dsimp [Hv]; positivity
  have hHd : 0 ≤ Hd := by dsimp [Hd]; positivity
  have hHdv : 0 ≤ Hdv := by dsimp [Hdv]; positivity
  have hAvals := (B.squaredQuotient_value_bounds hc p hp).2
  have hid := canonical_vertical_pair_box_mass_quotients
    hT hTwidth hT₁ hT₂ hc hC hBv H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hp
  rw [hid.2.2] at hAvals
  have hZ := canonical_inverse_mass_gap_vertical_bounds
    hT hTwidth hT₁ hT₂ hc hC hBv hε H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hgap₁ hgap₂ hp
  have hKval₂ : |canonicalMixedCoefficient b₂ S₂ p| ≤ K0 * d := by
    simp only [canonicalMixedCoefficient, div_eq_mul_inv, abs_mul]
    calc
      _ ≤ (A0 * d) * C * V * Z0 := by
        gcongr
        · rw [abs_of_nonneg (hc.le.trans (hweight₂ p hp).1)]
          exact (hweight₂ p hp).2
        · exact hnu₂ p hp
        · exact hZ.2.1
      _ = K0 * d := by ring
  have hKdiff := canonical_mixed_coefficient_value_sub_le_difference
    hT hTwidth hT₁ hT₂ hc hC hBv hV hε H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hnu₁ hnu₂
    hgap₁ hgap₂ hp
  have hKjet₂ := (canonical_mixed_coefficient_vertical_jet_bounds
    hT hTwidth hT₁ hT₂ hc hC hBv hV hL hε H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hnu₁ hnu₂
    hlamvertical₁ hlamvertical₂ hgap₁ hgap₂ hp).2
  have hKjetdiff := canonical_mixed_coefficient_vertical_jet_sub_le_difference
    hT hTwidth hT₁ hT₂ hc hC hBv hV hL hε H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hnu₁ hnu₂
    hlamvertical₁ hlamvertical₂ hgap₁ hgap₂ hp
  have hHval₁ := canonical_source_factor_abs_le_gap hT hT₁ hc hBv
    H₁ (fun q hq => (hweight₁ q hq).1) hhvertical₁ hp
  have hHval₂ := canonical_source_factor_abs_le_gap hT hT₂ hc hBv
    H₂ (fun q hq => (hweight₂ q hq).1) hhvertical₂ hp
  have hHjet₁ := canonical_source_factor_vertical_jet_abs_le
    hT hT₁ hc hBv H₁ hweight₁ hhvertical₁ hp
  have hHjet₂ := canonical_source_factor_vertical_jet_abs_le
    hT hT₂ hc hBv H₂ hweight₂ hhvertical₂ hp
  have hHdiff := canonical_source_factor_sub_le_difference
    hT hT₁ hT₂ hc H₁ H₂
    (fun q hq => (hweight₁ q hq).1) hweight₂
    hhvertical₁ hhvertical₂ hcoord.1 hcoord.2.1 hcoord.2.2
  have hHjetdiff := canonical_source_factor_vertical_jet_sub_le_difference
    hT hT₁ hT₂ hc hBv H₁ H₂ hweight₁ hweight₂
    hhvertical₁ hhvertical₂ hp
  have hHdiffE : |canonicalSourceFactor S₁ p -
      canonicalSourceFactor S₂ p| ≤ Hd * d * E := by
    simpa only [Prod.mk.eta] using
      hHdiff.trans (mul_le_mul_of_nonneg_left hDE (mul_nonneg hHd hd))
  have hHjetdiffE : |(fderivWithin ℝ (canonicalSourceFactor S₁)
        (closedCoordTriangle 0 T) p) (0, 1) -
      (fderivWithin ℝ (canonicalSourceFactor S₂)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Hdv * E :=
    hHjetdiff.trans (mul_le_mul_of_nonneg_left hDE hHdv)
  have hlamdiff := (outgoing_components_le_difference
    hT hT₁ hT₂ H₁ H₂ hcoord.1 hcoord.2.1 hcoord.2.2).1
  have hlamjetdiff := (outgoing_components_le_difference
    hT hT₁ hT₂ H₁ H₂ hcoord.1 hcoord.2.1 hcoord.2.2).2.2.1
  have hscalar := source_coefficient_difference_of_factor_bounds
    hc hd hdle (show (1 : ℝ) ≤ 1 by norm_num) hE
    hK0 hKv hKd hKdv hH0 hHv hHd hHdv hL
    hKval₂ hKdiff hKjet₂ hKjetdiff
    hHval₁ hHval₂ hHdiffE hHjet₁ hHjet₂ hHjetdiffE
    (hweight₁ p hp).1 (hweight₂ p hp).1
    (hlamdiff.trans hDE) (hlamvertical₁ p hp)
    (hlamvertical₂ p hp) (hlamjetdiff.trans hDE)
  have hQval₁ : canonicalQuotientSource b₁ S₁ p =
      -(canonicalMixedCoefficient b₁ S₁ p * canonicalSourceFactor S₁ p) /
        S₁.lam p.1 p.2 := by
    simp only [canonicalQuotientSource, canonicalSourceFactor]
    ring
  have hQval₂ : canonicalQuotientSource b₂ S₂ p =
      -(canonicalMixedCoefficient b₂ S₂ p * canonicalSourceFactor S₂ p) /
        S₂.lam p.1 p.2 := by
    simp only [canonicalQuotientSource, canonicalSourceFactor]
    ring
  rw [hQval₁, hQval₂,
    canonical_quotient_source_vertical_jet_eq hT hT₁ H₁ hp,
    canonical_quotient_source_vertical_jet_eq hT hT₂ H₂ hp]
  simpa only [one_mul, mul_one, one_pow] using hscalar

end ChristodoulouBV.C1Solution

end
