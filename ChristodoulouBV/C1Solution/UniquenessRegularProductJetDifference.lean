module

public import ChristodoulouBV.C1Solution.UniquenessRegularProductJet
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Acyclic outgoing jet difference for the regular product

The mixed-coefficient value estimate determines `Kd` before it enters the
outgoing jet estimate for `W = λν`.
-/

public section

namespace ChristodoulouBV.C1Solution

/-- The outgoing jets of `λν` differ by the four terms in the audited
ledger, using the previously established value bound for `K_g`. -/
theorem canonical_lam_nu_vertical_jet_sub_le_difference
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
    let Ad := B.JΔ / c ^ 2 + 2 * B.J₀ / c ^ 3
    let W0 := C * V
    let Wd := V + C
    let Z0 := ε⁻¹
    let Zd := (B.JΔ / c + B.J₀ / c ^ 2) / ε ^ 2
    let K0 := A0 * W0 * Z0
    let Kd := Ad * W0 * Z0 + A0 * Wd * Z0 + A0 * W0 * Zd
    |(fderivWithin ℝ
        (fun q : ℝ × ℝ => S₁.lam q.1 q.2 * S₁.nu q.1 q.2)
        (closedCoordTriangle 0 T) p) (0, 1) -
      (fderivWithin ℝ
        (fun q : ℝ × ℝ => S₂.lam q.1 q.2 * S₂.nu q.1 q.2)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤
      (V + L + K0 + C * Kd) *
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
  let Ad := B.JΔ / c ^ 2 + 2 * B.J₀ / c ^ 3
  let W0 := C * V
  let Wd := V + C
  let Z0 := ε⁻¹
  let Zd := (B.JΔ / c + B.J₀ / c ^ 2) / ε ^ 2
  let K0 := A0 * W0 * Z0
  let Kd := Ad * W0 * Z0 + A0 * Wd * Z0 + A0 * W0 * Zd
  have hcoord := closed_triangle_coordinates hp
  have hd : 0 ≤ d := sub_nonneg.mpr hcoord.2.1
  have hdle : d ≤ 1 := by dsimp [d]; linarith only [hcoord.1, hcoord.2.2, hTwidth]
  have hD : 0 ≤ D := outgoing_difference_nonneg hT hT₁ hT₂ H₁ H₂
    ⟨hcoord.1, hcoord.2.1.trans hcoord.2.2⟩
  have hnudiff := incoming_component_le_difference hT hT₁ hT₂ H₁ H₂
    hcoord.1 hcoord.2.1 hcoord.2.2
  have hN : 0 ≤ N := (abs_nonneg _).trans hnudiff
  have hE : 0 ≤ E := add_nonneg hD hN
  have hDE : D ≤ E := le_add_of_nonneg_right hN
  rcases B.bounds_nonneg with ⟨hJ0, _, hJd, _, _, _⟩
  have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
  have hAd : 0 ≤ Ad := by dsimp [Ad]; positivity
  have hW0 : 0 ≤ W0 := mul_nonneg hC hV
  have hWd : 0 ≤ Wd := add_nonneg hV hC
  have hZd : 0 ≤ Zd := by dsimp [Zd]; positivity
  have hK0 : 0 ≤ K0 := by dsimp [K0]; positivity
  have hKd : 0 ≤ Kd := by dsimp [Kd]; positivity
  have hid := canonical_vertical_pair_box_mass_quotients
    hT hTwidth hT₁ hT₂ hc hC hBv H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hp
  have hAvals := B.squaredQuotient_value_bounds hc p hp
  rw [hid.1.2, hid.2.2] at hAvals
  have hW := canonical_lam_nu_product_value_bounds
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
  have hK₁ : |canonicalMixedCoefficient b₁ S₁ p| ≤ K0 * d := by
    have hz₁ := hZ.1
    simp only [canonicalMixedCoefficient, div_eq_mul_inv, abs_mul]
    calc
      _ ≤ (A0 * d) * C * V * Z0 := by
        gcongr
        · exact hAvals.1
        · rw [abs_of_nonneg (hc.le.trans (hweight₁ p hp).1)]
          exact (hweight₁ p hp).2
        · exact hnu₁ p hp
      _ = K0 * d := by ring
  have hKdiff := canonical_mixed_coefficient_value_sub_le_difference
    hT hTwidth hT₁ hT₂ hc hC hBv hV hε H₁ H₂
    hweight₁ hweight₂ hhvertical₁ hhvertical₂ hnu₁ hnu₂
    hgap₁ hgap₂ hp
  have hLidiff := (outgoing_components_le_difference
    hT hT₁ hT₂ H₁ H₂ hcoord.1 hcoord.2.1 hcoord.2.2).2.2.1
  have hlamdiff := (outgoing_components_le_difference
    hT hT₁ hT₂ H₁ H₂ hcoord.1 hcoord.2.1 hcoord.2.2).1
  have hLidiffE : |(fderivWithin ℝ
      (fun q : ℝ × ℝ => S₁.lam q.1 q.2)
      (closedCoordTriangle 0 T) p) (0, 1) -
    (fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2)
      (closedCoordTriangle 0 T) p) (0, 1)| ≤ E :=
    hLidiff.trans hDE
  have hnudiffE : |S₁.nu p.1 p.2 - S₂.nu p.1 p.2| ≤ E :=
    hnudiff.trans (le_add_of_nonneg_left hD)
  have hlamdiffE : |S₁.lam p.1 p.2 - S₂.lam p.1 p.2| ≤ E :=
    hlamdiff.trans hDE
  have hKdiffE : |canonicalMixedCoefficient b₁ S₁ p -
      canonicalMixedCoefficient b₂ S₂ p| ≤ Kd * d * E := hKdiff
  have hscalar := lam_nu_product_jet_difference
    hdle hE hC hL hK0 hKd
    (hnu₁ p hp) (hlamvertical₂ p hp) hLidiffE hnudiffE
    (by rw [abs_of_nonneg (hc.le.trans (hweight₂ p hp).1)]
        exact (hweight₂ p hp).2)
    hlamdiffE hK₁ hKdiffE
  rw [canonical_lam_nu_vertical_jet_eq hT hT₁ H₁ hp,
    canonical_lam_nu_vertical_jet_eq hT hT₂ H₂ hp]
  simpa only [mul_one] using hscalar

end ChristodoulouBV.C1Solution

end
