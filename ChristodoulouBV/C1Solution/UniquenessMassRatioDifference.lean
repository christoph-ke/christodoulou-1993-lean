module

public import ChristodoulouBV.C1Solution.UniquenessVerticalPairBox
import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMeanEstimates
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Fixed-ray difference of canonical mass ratios

The cubic mass numerator and linearly growing radius give a quadratic
difference bound for the removable mass ratio.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

/-- The canonical mass ratios differ quadratically from the regular axis,
with the exact two-input coefficient from the arbitrary-bound ledger. -/
theorem canonical_mass_ratio_sub_le_difference
    {b₁ b₂ T c C Bv : ℝ}
    (hT : 0 < T) (hTwidth : T ≤ 1)
    (hT₁ : T < b₁) (hT₂ : T < b₂)
    (hc : 0 < c) (hC : 0 ≤ C) (hBv : 0 ≤ Bv)
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
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ T) :
    let j₀ := C * Bv ^ 2
    let Hd := (Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2)
    let jΔ := Bv ^ 2 + 2 * C * Bv * Hd
    let kΔ := jΔ / c + j₀ / c ^ 2
    let J₀ := j₀ / 3
    let JΔ := jΔ / 3 + j₀ * kΔ / 6
    |canonicalMassRatio b₁ S₁ (u, v) -
      canonicalMassRatio b₂ S₂ (u, v)| ≤
      (JΔ / c + J₀ / c ^ 2) * (v - u) ^ 2 *
        outgoingDifference T hT.le S₁ S₂ u := by
  dsimp only
  let K := closedCoordTriangle 0 T
  let d := v - u
  let D := outgoingDifference T hT.le S₁ S₂ u
  let r₁ := canonicalRadius S₁ (u, v)
  let r₂ := canonicalRadius S₂ (u, v)
  let J₁ := canonicalMassNumerator b₁ S₁ (u, v)
  let J₂ := canonicalMassNumerator b₂ S₂ (u, v)
  let j₀ := C * Bv ^ 2
  let Hd := (Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2)
  let jΔ := Bv ^ 2 + 2 * C * Bv * Hd
  let kΔ := jΔ / c + j₀ / c ^ 2
  let J₀ := j₀ / 3
  let JΔ := jΔ / 3 + j₀ * kΔ / 6
  rcases eq_or_lt_of_le huv with heq | hlt
  · subst v
    simp [canonicalMassRatio_axis]
  · have hp : (u, v) ∈ K := ⟨hu, hlt.le, hv⟩
    have hd : 0 < d := sub_pos.mpr hlt
    have hr₁ : c * d ≤ r₁ := by
      exact intervalIntegral.mul_sub_le_weightedDiagonalRadius
        (five_fields_contDiffOn hT hT₁ H₁).1.continuousOn
        (fun p hp => (hweight₁ p hp).1) hu hlt.le hv
    have hr₂ : c * d ≤ r₂ := by
      exact intervalIntegral.mul_sub_le_weightedDiagonalRadius
        (five_fields_contDiffOn hT hT₂ H₂).1.continuousOn
        (fun p hp => (hweight₂ p hp).1) hu hlt.le hv
    have hrdiff : |r₁ - r₂| ≤ d * D := by
      let w₁ : ℝ × ℝ → ℝ := fun p => S₁.lam p.1 p.2
      let w₂ : ℝ × ℝ → ℝ := fun p => S₂.lam p.1 p.2
      have hw₁ : ContinuousOn w₁ K :=
        (five_fields_contDiffOn hT hT₁ H₁).1.continuousOn
      have hw₂ : ContinuousOn w₂ K :=
        (five_fields_contDiffOn hT hT₂ H₂).1.continuousOn
      have hwdiff : ∀ t ∈ Icc u v, |w₁ (u, t) - w₂ (u, t)| ≤ D := by
        intro t ht
        exact (outgoing_components_le_difference hT hT₁ hT₂ H₁ H₂
          hu ht.1 (ht.2.trans hv)).1
      have h := intervalIntegral.abs_weightedDiagonalRadius_sub_le_on_ray
        hw₁ hw₂ hu hlt.le hv hwdiff
      simpa only [r₁, r₂, canonicalRadius, w₁, w₂, mul_comm] using h
    have hJ₂ : |J₂| ≤ J₀ * d ^ 3 := by
      have h := canonical_mass_numerator_nonneg_le hT hT₂ hc hBv H₂
        hweight₂ hhvertical₂ hu hlt.le hv
      rw [abs_of_nonneg h.1]
      exact h.2
    have hJdiff : |J₁ - J₂| ≤ JΔ * d ^ 3 * D :=
      canonical_mass_numerator_sub_le_difference hT hTwidth hT₁ hT₂
        hc hC hBv H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂
        hu hlt.le hv
    have h := intervalIntegral.abs_div_sub_div_le
      (mul_pos hc hd) hr₁ hr₂ hJdiff hrdiff hJ₂
    change |J₁ / r₁ - J₂ / r₂| ≤
      (JΔ / c + J₀ / c ^ 2) * d ^ 2 * D
    calc
      _ ≤ (JΔ * d ^ 3 * D) / (c * d) +
          (J₀ * d ^ 3) * (d * D) / (c * d) ^ 2 := h
      _ = _ := by field_simp [hc.ne', hd.ne']

end ChristodoulouBV.C1Solution

end
