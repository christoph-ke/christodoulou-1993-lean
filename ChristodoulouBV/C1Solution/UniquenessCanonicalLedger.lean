module

public import ChristodoulouBV.C1Solution.UniquenessSourceDifference
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Explicit width-one canonical coefficient ledger

The five fields below are the actual coefficients produced by the
vertical-only pair box. They collect the four separate value and outgoing
jet differences without introducing any incoming jet difference.
-/

public section

namespace ChristodoulouBV.C1Solution

/-- Coefficients in the four-term outgoing uniqueness estimate. -/
structure CanonicalVerticalLedger where
  Kd : ℝ
  Qd : ℝ
  Kdv : ℝ
  Qdv : ℝ
  A1 : ℝ

/-- The explicit coefficients obtained by applying the factor ledgers to
the canonical vertical pair box on a triangle of width at most one. -/
@[expose] noncomputable def canonicalVerticalLedger {T c : ℝ}
    (B : intervalIntegral.CubicRationalVerticalPairBox 0 T c)
    (C Bv V L ε : ℝ) : CanonicalVerticalLedger := Id.run do
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
  let Qd := Pd / c + P0 / c ^ 2
  let Qdv := Pdv / c + Pv / c ^ 2 + Pd * L / c ^ 2 +
    P0 / c ^ 2 + 2 * P0 * L / c ^ 3
  return { Kd, Qd, Kdv, Qdv, A1 := Kd + Qd + Kdv + Qdv }

/-- Every coefficient in the canonical ledger is nonnegative under the
common positive lower bounds and nonnegative value and jet bounds. -/
theorem CanonicalVerticalLedger.nonneg {T c C Bv V L ε : ℝ}
    (B : intervalIntegral.CubicRationalVerticalPairBox 0 T c)
    (hc : 0 < c) (hC : 0 ≤ C) (hBv : 0 ≤ Bv)
    (hV : 0 ≤ V) (hL : 0 ≤ L) (hε : 0 < ε) :
    0 ≤ (canonicalVerticalLedger B C Bv V L ε).Kd ∧
    0 ≤ (canonicalVerticalLedger B C Bv V L ε).Qd ∧
    0 ≤ (canonicalVerticalLedger B C Bv V L ε).Kdv ∧
    0 ≤ (canonicalVerticalLedger B C Bv V L ε).Qdv ∧
    0 ≤ (canonicalVerticalLedger B C Bv V L ε).A1 := by
  rcases B.bounds_nonneg with ⟨hJ0, hJv, hJd, hJdv, hRv, hRdv⟩
  dsimp [canonicalVerticalLedger]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> positivity

/-- The four canonical coefficient differences are controlled by one
explicit multiple of the outgoing and incoming moving seminorms. -/
theorem canonical_four_coefficient_difference_bound
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
    let ℓ := canonicalVerticalLedger B C Bv V L ε
    |canonicalMixedCoefficient b₁ S₁ p -
      canonicalMixedCoefficient b₂ S₂ p| +
    |canonicalQuotientSource b₁ S₁ p -
      canonicalQuotientSource b₂ S₂ p| +
    |(fderivWithin ℝ (canonicalMixedCoefficient b₁ S₁)
        (closedCoordTriangle 0 T) p) (0, 1) -
      (fderivWithin ℝ (canonicalMixedCoefficient b₂ S₂)
        (closedCoordTriangle 0 T) p) (0, 1)| +
    |(fderivWithin ℝ (canonicalQuotientSource b₁ S₁)
        (closedCoordTriangle 0 T) p) (0, 1) -
      (fderivWithin ℝ (canonicalQuotientSource b₂ S₂)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤
      ℓ.A1 * (outgoingDifference T hT.le S₁ S₂ p.1 +
        incomingDifference T hT.le S₁ S₂ p.1) := by
  dsimp only
  let B := canonicalVerticalPairBox hT hTwidth hT₁ hT₂
    hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
  let ℓ := canonicalVerticalLedger B C Bv V L ε
  let d := p.2 - p.1
  let D := outgoingDifference T hT.le S₁ S₂ p.1
  let N := incomingDifference T hT.le S₁ S₂ p.1
  let E := D + N
  have hcoord := closed_triangle_coordinates hp
  have hd : 0 ≤ d := sub_nonneg.mpr hcoord.2.1
  have hdle : d ≤ 1 := by dsimp [d]; linarith only [hcoord.1, hcoord.2.2, hTwidth]
  have hD : 0 ≤ D := outgoing_difference_nonneg hT hT₁ hT₂ H₁ H₂
    ⟨hcoord.1, hcoord.2.1.trans hcoord.2.2⟩
  have hν := incoming_component_le_difference hT hT₁ hT₂ H₁ H₂
    hcoord.1 hcoord.2.1 hcoord.2.2
  have hN : 0 ≤ N := (abs_nonneg _).trans hν
  have hE : 0 ≤ E := add_nonneg hD hN
  rcases CanonicalVerticalLedger.nonneg B hc hC hBv hV hL hε with
    ⟨hKd, hQd, _, hQdv, _⟩
  have hK := canonical_mixed_coefficient_value_sub_le_difference
    hT hTwidth hT₁ hT₂ hc hC hBv hV hε H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hnu₁ hnu₂
    hgap₁ hgap₂ hp
  have hKi := canonical_mixed_coefficient_vertical_jet_sub_le_difference
    hT hTwidth hT₁ hT₂ hc hC hBv hV hL hε H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hnu₁ hnu₂
    hlamvertical₁ hlamvertical₂ hgap₁ hgap₂ hp
  have hQ := canonical_quotient_source_value_vertical_jet_sub_le_difference
    hT hTwidth hT₁ hT₂ hc hC hBv hV hL hε H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hnu₁ hnu₂
    hlamvertical₁ hlamvertical₂ hgap₁ hgap₂ hp
  have hK' : |canonicalMixedCoefficient b₁ S₁ p -
      canonicalMixedCoefficient b₂ S₂ p| ≤ ℓ.Kd * d * E := by
    convert hK using 1; rfl
  have hKi' : |(fderivWithin ℝ (canonicalMixedCoefficient b₁ S₁)
        (closedCoordTriangle 0 T) p) (0, 1) -
      (fderivWithin ℝ (canonicalMixedCoefficient b₂ S₂)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ ℓ.Kdv * E := by
    convert hKi using 1; rfl
  have hQ' : |canonicalQuotientSource b₁ S₁ p -
      canonicalQuotientSource b₂ S₂ p| ≤ ℓ.Qd * d ^ 2 * E ∧
      |(fderivWithin ℝ (canonicalQuotientSource b₁ S₁)
          (closedCoordTriangle 0 T) p) (0, 1) -
        (fderivWithin ℝ (canonicalQuotientSource b₂ S₂)
          (closedCoordTriangle 0 T) p) (0, 1)| ≤ ℓ.Qdv * d * E := by
    convert hQ using 1 <;> rfl
  have hfour := four_coefficient_difference_bound hd hdle hE
    hKd hQd hQdv hK' hQ'.1 hKi' hQ'.2
  have hA : ℓ.A1 = ℓ.Kd + ℓ.Qd + ℓ.Kdv + ℓ.Qdv := by rfl
  rw [hA]
  simpa only [one_pow, mul_one] using hfour

end ChristodoulouBV.C1Solution

end
