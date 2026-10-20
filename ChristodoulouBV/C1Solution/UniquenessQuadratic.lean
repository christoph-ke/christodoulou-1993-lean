module

public import ChristodoulouBV.C1Solution.UniquenessDifference
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraKernel
import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraKernelEstimates
import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraProductDifference
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# The outgoing quadratic kernel on one ray

The value difference of the quadratic kernel needs only the four outgoing
value and vertical-jet differences. Its coefficient is the scalar quadratic-kernel bound.
-/

public section

namespace ChristodoulouBV.C1Solution

/-- The quadratic source products have the fixed-ray quadratic-kernel difference bound. -/
theorem canonical_quadratic_kernel_sub_le_difference
    {b₁ b₂ B c C Bv : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    (hc : 0 < c) (hC : 0 ≤ C) (hBv : 0 ≤ Bv)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hweight₁ : ∀ p ∈ closedCoordTriangle 0 B,
      c ≤ S₁.lam p.1 p.2 ∧ S₁.lam p.1 p.2 ≤ C)
    (hweight₂ : ∀ p ∈ closedCoordTriangle 0 B,
      c ≤ S₂.lam p.1 p.2 ∧ S₂.lam p.1 p.2 ≤ C)
    (hhvertical₁ : ∀ p ∈ closedCoordTriangle 0 B,
      |(fderivWithin ℝ (outgoingQuotient S₁)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ Bv)
    (hhvertical₂ : ∀ p ∈ closedCoordTriangle 0 B,
      |(fderivWithin ℝ (outgoingQuotient S₂)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ Bv)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ B) :
    |intervalIntegral.weightedDiagonalQuadraticKernel
        (fun p => S₁.lam p.1 p.2) (outgoingQuotient S₁) (u, v) -
      intervalIntegral.weightedDiagonalQuadraticKernel
        (fun p => S₂.lam p.1 p.2) (outgoingQuotient S₂) (u, v)| ≤
      (Bv ^ 2 + 2 * C * Bv *
        ((Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2))) *
        (v - u) ^ 2 * outgoingDifference B hB.le S₁ S₂ u := by
  let K := closedCoordTriangle 0 B
  let w₁ : ℝ × ℝ → ℝ := fun p => S₁.lam p.1 p.2
  let w₂ : ℝ × ℝ → ℝ := fun p => S₂.lam p.1 p.2
  let f₁ := outgoingQuotient S₁
  let f₂ := outgoingQuotient S₂
  let D := outgoingDifference B hB.le S₁ S₂ u
  let M := (Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2)
  have hp : (u, v) ∈ closedCoordTriangle 0 B := ⟨hu, huv, hv⟩
  have hD : 0 ≤ D := outgoing_difference_nonneg hB hB₁ hB₂ H₁ H₂
    ⟨hu, huv.trans hv⟩
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hw₂ : |w₂ (u, v)| ≤ C := by
    dsimp [w₂]
    have h := hweight₂ (u, v) hp
    rw [abs_of_nonneg (hc.le.trans h.1)]
    exact h.2
  have hwdiff : |w₁ (u, v) - w₂ (u, v)| ≤ D :=
    (outgoing_components_le_difference hB hB₁ hB₂ H₁ H₂ hu huv hv).1
  have hH₁ : |intervalIntegral.weightedDiagonalError w₁ f₁ (u, v)| ≤
      Bv * (v - u) := by
    rw [← canonical_source_factor_eq_weightedDiagonalError hB hB₁ H₁ hp]
    exact canonical_source_factor_abs_le_gap hB hB₁ hc hBv H₁
      (fun p hp => (hweight₁ p hp).1) hhvertical₁ hp
  have hH₂ : |intervalIntegral.weightedDiagonalError w₂ f₂ (u, v)| ≤
      Bv * (v - u) := by
    rw [← canonical_source_factor_eq_weightedDiagonalError hB hB₂ H₂ hp]
    exact canonical_source_factor_abs_le_gap hB hB₂ hc hBv H₂
      (fun p hp => (hweight₂ p hp).1) hhvertical₂ hp
  have hHdiff :
      |intervalIntegral.weightedDiagonalError w₁ f₁ (u, v) -
        intervalIntegral.weightedDiagonalError w₂ f₂ (u, v)| ≤
        M * (v - u) * D := by
    rw [← canonical_source_factor_eq_weightedDiagonalError hB hB₁ H₁ hp,
      ← canonical_source_factor_eq_weightedDiagonalError hB hB₂ H₂ hp]
    exact canonical_source_factor_sub_le_difference hB hB₁ hB₂ hc
      H₁ H₂ (fun p hp => (hweight₁ p hp).1) hweight₂
      hhvertical₁ hhvertical₂ hu huv hv
  exact intervalIntegral.abs_weightedDiagonalQuadraticKernel_sub_le_of_bounds
    hC hBv hM hD (sub_nonneg.mpr huv) hw₂ hwdiff hH₁ hH₂ hHdiff

/-- The quotient kernel has a linear gap factor in its fixed-ray difference. -/
theorem canonical_quotient_kernel_sub_le_difference
    {b₁ b₂ B c C Bv : ℝ}
    (hB : 0 < B) (hB₁ : B < b₁) (hB₂ : B < b₂)
    (hc : 0 < c) (hBv : 0 ≤ Bv)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hweight₁ : ∀ p ∈ closedCoordTriangle 0 B,
      c ≤ S₁.lam p.1 p.2 ∧ S₁.lam p.1 p.2 ≤ C)
    (hweight₂ : ∀ p ∈ closedCoordTriangle 0 B,
      c ≤ S₂.lam p.1 p.2 ∧ S₂.lam p.1 p.2 ≤ C)
    (hhvertical₁ : ∀ p ∈ closedCoordTriangle 0 B,
      |(fderivWithin ℝ (outgoingQuotient S₁)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ Bv)
    (hhvertical₂ : ∀ p ∈ closedCoordTriangle 0 B,
      |(fderivWithin ℝ (outgoingQuotient S₂)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ Bv)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ B) :
    |intervalIntegral.weightedDiagonalQuotientKernel
        (fun p => S₁.lam p.1 p.2) (outgoingQuotient S₁) (u, v) -
      intervalIntegral.weightedDiagonalQuotientKernel
        (fun p => S₂.lam p.1 p.2) (outgoingQuotient S₂) (u, v)| ≤
      (((Bv ^ 2 + 2 * C * Bv *
        ((Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2))) / c) +
        C * Bv ^ 2 / c ^ 2) *
        (v - u) * outgoingDifference B hB.le S₁ S₂ u := by
  let w₁ : ℝ × ℝ → ℝ := fun p => S₁.lam p.1 p.2
  let w₂ : ℝ × ℝ → ℝ := fun p => S₂.lam p.1 p.2
  let f₁ := outgoingQuotient S₁
  let f₂ := outgoingQuotient S₂
  let D := outgoingDifference B hB.le S₁ S₂ u
  have hp : (u, v) ∈ closedCoordTriangle 0 B := ⟨hu, huv, hv⟩
  have hw₁ : ContinuousOn w₁ (closedCoordTriangle 0 B) :=
    (five_fields_contDiffOn hB hB₁ H₁).1.continuousOn
  have hw₂ : ContinuousOn w₂ (closedCoordTriangle 0 B) :=
    (five_fields_contDiffOn hB hB₂ H₂).1.continuousOn
  have hrdiff :
      |intervalIntegral.weightedDiagonalRadius w₁ (u, v) -
        intervalIntegral.weightedDiagonalRadius w₂ (u, v)| ≤ (v - u) * D := by
    rw [mul_comm]
    apply intervalIntegral.abs_weightedDiagonalRadius_sub_le_on_ray
      hw₁ hw₂ hu huv hv
    intro t ht
    exact (outgoing_components_le_difference hB hB₁ hB₂ H₁ H₂
      hu ht.1 (ht.2.trans hv)).1
  have hC : 0 ≤ C := by
    have h := hweight₂ (u, v) hp
    dsimp at h
    linarith
  have hf₂ : ContinuousOn f₂ (closedCoordTriangle 0 B) :=
    (alpha_div_lam_contDiffOn hB hB₂ H₂).continuousOn
  have hjet₂ : ∀ p ∈ closedCoordTriangle 0 B,
      HasFDerivWithinAt f₂
        (fderivWithin ℝ f₂ (closedCoordTriangle 0 B) p)
        (closedCoordTriangle 0 B) p := by
    intro p hp
    exact ((alpha_div_lam_contDiffOn hB hB₂ H₂).differentiableOn
      (by norm_num) p hp).hasFDerivWithinAt
  have hj₂ : |intervalIntegral.weightedDiagonalQuadraticKernel w₂ f₂ (u, v)| ≤
      (C * Bv ^ 2) * (v - u) ^ 2 := by
    have hnonneg : 0 ≤ intervalIntegral.weightedDiagonalQuadraticKernel
        w₂ f₂ (u, v) := by
      apply intervalIntegral.weightedDiagonalQuadraticKernel_nonneg
      have h := hweight₂ (u, v) hp
      dsimp [w₂] at *
      linarith
    rw [abs_of_nonneg hnonneg]
    exact intervalIntegral.weightedDiagonalQuadraticKernel_le_mul_sq_gap
      hw₂ hf₂ hweight₂ hc hBv hjet₂ hhvertical₂ hp
  have hjdiff :
      |intervalIntegral.weightedDiagonalQuadraticKernel w₁ f₁ (u, v) -
        intervalIntegral.weightedDiagonalQuadraticKernel w₂ f₂ (u, v)| ≤
        (Bv ^ 2 + 2 * C * Bv *
          ((Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2))) *
          (v - u) ^ 2 * D :=
    canonical_quadratic_kernel_sub_le_difference hB hB₁ hB₂ hc hC hBv
      H₁ H₂ hweight₁ hweight₂ hhvertical₁ hhvertical₂ hu huv hv
  rcases eq_or_lt_of_le huv with heq | hlt
  · subst v
    simp [intervalIntegral.weightedDiagonalQuotientKernel_diag]
  · exact intervalIntegral.abs_weightedDiagonalQuotientKernel_sub_le_of_bounds
      hw₁ hw₂ (fun p hp => (hweight₁ p hp).1)
      (fun p hp => (hweight₂ p hp).1) hc hp hlt hj₂ hjdiff hrdiff

/-- At width at most one, the quadratic kernel's outgoing jet difference
uses only the four-field outgoing seminorm. -/
theorem canonical_quadratic_kernel_vertical_jet_sub_le_difference
    {b₁ b₂ B c C Bv L Hc : ℝ}
    (hB : 0 < B) (hBwidth : B ≤ 1)
    (hB₁ : B < b₁) (hB₂ : B < b₂)
    (hc : 0 < c) (hBv : 0 ≤ Bv) (hL : 0 ≤ L)
    {S₁ S₂ : Fields}
    (H₁ : IsC1Solution (developmentWithInitialEdge b₁) S₁)
    (H₂ : IsC1Solution (developmentWithInitialEdge b₂) S₂)
    (hweight₁ : ∀ p ∈ closedCoordTriangle 0 B,
      c ≤ S₁.lam p.1 p.2 ∧ S₁.lam p.1 p.2 ≤ C)
    (hweight₂ : ∀ p ∈ closedCoordTriangle 0 B,
      c ≤ S₂.lam p.1 p.2 ∧ S₂.lam p.1 p.2 ≤ C)
    (hhvertical₁ : ∀ p ∈ closedCoordTriangle 0 B,
      |(fderivWithin ℝ (outgoingQuotient S₁)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ Bv)
    (hhvertical₂ : ∀ p ∈ closedCoordTriangle 0 B,
      |(fderivWithin ℝ (outgoingQuotient S₂)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ Bv)
    (hlamVertical₂ : ∀ p ∈ closedCoordTriangle 0 B,
      |(fderivWithin ℝ (fun q : ℝ × ℝ => S₂.lam q.1 q.2)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ L)
    (hsourceVertical₁ : ∀ p ∈ closedCoordTriangle 0 B,
      |(fderivWithin ℝ (canonicalSourceFactor S₁)
        (closedCoordTriangle 0 B) p) (0, 1)| ≤ Hc)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ B) :
    |(fderivWithin ℝ
        (intervalIntegral.weightedDiagonalQuadraticKernel
          (fun p => S₁.lam p.1 p.2) (outgoingQuotient S₁))
        (closedCoordTriangle 0 B) (u, v)) (0, 1) -
      (fderivWithin ℝ
        (intervalIntegral.weightedDiagonalQuadraticKernel
          (fun p => S₂.lam p.1 p.2) (outgoingQuotient S₂))
        (closedCoordTriangle 0 B) (u, v)) (0, 1)| ≤
      (Bv ^ 2 + 2 * L * Bv *
        ((Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2)) +
        2 * (Bv * Hc + C *
          ((Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2)) * Hc +
          C * Bv * (1 +
            (Bv + C * ((Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2))) / c +
            C * Bv / c ^ 2))) *
        (v - u) * outgoingDifference B hB.le S₁ S₂ u := by
  let K := closedCoordTriangle 0 B
  let w₁ : ℝ × ℝ → ℝ := fun p => S₁.lam p.1 p.2
  let w₂ : ℝ × ℝ → ℝ := fun p => S₂.lam p.1 p.2
  let f₁ := outgoingQuotient S₁
  let f₂ := outgoingQuotient S₂
  let E₁ := intervalIntegral.weightedDiagonalError w₁ f₁
  let E₂ := intervalIntegral.weightedDiagonalError w₂ f₂
  let D := outgoingDifference B hB.le S₁ S₂ u
  let M := (Bv + C) / (2 * c) + C * Bv / (2 * c ^ 2)
  let N := 1 + (Bv + C * M) / c + C * Bv / c ^ 2
  have hp : (u, v) ∈ closedCoordTriangle 0 B := ⟨hu, huv, hv⟩
  have hdle : v - u ≤ 1 := by linarith
  have hD : 0 ≤ D := outgoing_difference_nonneg hB hB₁ hB₂ H₁ H₂
    ⟨hu, huv.trans hv⟩
  have hC : 0 ≤ C := by
    have h := hweight₂ (u, v) hp
    dsimp at h
    linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hwC1₁ := (five_fields_contDiffOn hB hB₁ H₁).1
  have hwC1₂ := (five_fields_contDiffOn hB hB₂ H₂).1
  have hfC1₁ := alpha_div_lam_contDiffOn hB hB₁ H₁
  have hfC1₂ := alpha_div_lam_contDiffOn hB hB₂ H₂
  have hjetw₁ : ∀ p ∈ K,
      HasFDerivWithinAt w₁ (fderivWithin ℝ w₁ K p) K p := by
    intro p hp
    exact (hwC1₁.differentiableOn (by norm_num) p hp).hasFDerivWithinAt
  have hjetw₂ : ∀ p ∈ K,
      HasFDerivWithinAt w₂ (fderivWithin ℝ w₂ K p) K p := by
    intro p hp
    exact (hwC1₂.differentiableOn (by norm_num) p hp).hasFDerivWithinAt
  have heq₁ : Set.EqOn E₁ (canonicalSourceFactor S₁) K := by
    intro p hp
    exact (canonical_source_factor_eq_weightedDiagonalError hB hB₁ H₁ hp).symm
  have heq₂ : Set.EqOn E₂ (canonicalSourceFactor S₂) K := by
    intro p hp
    exact (canonical_source_factor_eq_weightedDiagonalError hB hB₂ H₂ hp).symm
  have hEC1₁ : ContDiffOn ℝ 1 E₁ K :=
    (canonical_source_factor_box_inputs hB hB₁ H₁).1.congr
      (fun p hp => heq₁ hp)
  have hEC1₂ : ContDiffOn ℝ 1 E₂ K :=
    (canonical_source_factor_box_inputs hB hB₂ H₂).1.congr
      (fun p hp => heq₂ hp)
  have hw₂ : |w₂ (u, v)| ≤ C := by
    dsimp [w₂]
    have h := hweight₂ (u, v) hp
    rw [abs_of_nonneg (by linarith [h.1])]
    exact h.2
  have hwdiff : |w₁ (u, v) - w₂ (u, v)| ≤ D :=
    (outgoing_components_le_difference hB hB₁ hB₂ H₁ H₂ hu huv hv).1
  have hGw₂ : |(fderivWithin ℝ w₂ K (u, v)) (0, 1)| ≤ L :=
    hlamVertical₂ (u, v) hp
  have hGwdiff :
      |(fderivWithin ℝ w₁ K (u, v)) (0, 1) -
        (fderivWithin ℝ w₂ K (u, v)) (0, 1)| ≤ D :=
    (outgoing_components_le_difference hB hB₁ hB₂ H₁ H₂ hu huv hv).2.2.1
  have hH₁ : |E₁ (u, v)| ≤ Bv * (v - u) := by
    rw [heq₁ hp]
    exact canonical_source_factor_abs_le_gap hB hB₁ hc hBv H₁
      (fun p hp => (hweight₁ p hp).1) hhvertical₁ hp
  have hH₂ : |E₂ (u, v)| ≤ Bv * (v - u) := by
    rw [heq₂ hp]
    exact canonical_source_factor_abs_le_gap hB hB₂ hc hBv H₂
      (fun p hp => (hweight₂ p hp).1) hhvertical₂ hp
  have hHdiff : |E₁ (u, v) - E₂ (u, v)| ≤ M * (v - u) * D := by
    rw [heq₁ hp, heq₂ hp]
    exact canonical_source_factor_sub_le_difference hB hB₁ hB₂ hc
      H₁ H₂ (fun p hp => (hweight₁ p hp).1) hweight₂
      hhvertical₁ hhvertical₂ hu huv hv
  have hGH₁ : |(fderivWithin ℝ E₁ K (u, v)) (0, 1)| ≤ Hc := by
    rw [fderivWithin_congr' heq₁ hp]
    exact hsourceVertical₁ (u, v) hp
  have hGHdiff :
      |(fderivWithin ℝ E₁ K (u, v)) (0, 1) -
        (fderivWithin ℝ E₂ K (u, v)) (0, 1)| ≤ N * D := by
    rw [fderivWithin_congr' heq₁ hp, fderivWithin_congr' heq₂ hp]
    exact canonical_source_factor_vertical_jet_sub_le_difference
      hB hB₁ hB₂ hc hBv H₁ H₂ hweight₁ hweight₂
      hhvertical₁ hhvertical₂ hp
  exact intervalIntegral.abs_fderivWithin_weightedDiagonalQuadraticKernel_sub_le_of_bounds
    hB hjetw₁ hjetw₂ hEC1₁ hEC1₂ hBv hC hL hM hD hp hdle
    hw₂ hwdiff hGw₂ hGwdiff hH₁ hH₂ hHdiff hGH₁ hGHdiff

end ChristodoulouBV.C1Solution

end
