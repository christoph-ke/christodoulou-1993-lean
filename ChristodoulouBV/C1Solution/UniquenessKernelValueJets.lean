module

public import ChristodoulouBV.C1Solution.UniquenessMassJetDifference
import ChristodoulouBV.ForMathlib.Analysis.Calculus.WeightedDiagonalMeanDerivativeEstimates
import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraKernel
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Outgoing value jets of the canonical kernels

The scalar source factor has the exact vertical bound from the weighted
diagonal mean, which gives the quadratic source's outgoing jet bound.
-/

public section

open Set

namespace ChristodoulouBV.C1Solution

/-- The outgoing source-factor jet has the exact arbitrary-bound source-factor
coefficient `Bv + C Bv/c` on the closed triangle. -/
theorem canonical_source_factor_vertical_jet_abs_le
    {b T c C Bv : ℝ} (hT : 0 < T) (hTb : T < b)
    (hc : 0 < c) (hBv : 0 ≤ Bv)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hweight : ∀ p ∈ closedCoordTriangle 0 T,
      c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C)
    (hhvertical : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (outgoingQuotient S)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Bv)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 T) :
    |(fderivWithin ℝ (canonicalSourceFactor S)
      (closedCoordTriangle 0 T) p) (0, 1)| ≤ Bv + C * Bv / c := by
  let K := closedCoordTriangle 0 T
  let w : ℝ × ℝ → ℝ := fun q => S.lam q.1 q.2
  let f := outgoingQuotient S
  let Gw := fderivWithin ℝ w K
  let Gf := fderivWithin ℝ f K
  have hwC1 : ContDiffOn ℝ 1 w K := (five_fields_contDiffOn hT hTb H).1
  have hfC1 : ContDiffOn ℝ 1 f K := alpha_div_lam_contDiffOn hT hTb H
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 T)
      (by rw [interior_closedCoordTriangle]
          exact openCoordTriangle_nonempty hT)
  have hGw : ContinuousOn Gw K :=
    hwC1.continuousOn_fderivWithin hunique (by norm_num)
  have hGf : ContinuousOn Gf K :=
    hfC1.continuousOn_fderivWithin hunique (by norm_num)
  have hdw : DifferentiableOn ℝ w (interior K) :=
    (hwC1.differentiableOn (by norm_num)).mono interior_subset
  have hdf : DifferentiableOn ℝ f (interior K) :=
    (hfC1.differentiableOn (by norm_num)).mono interior_subset
  have hderivw : ∀ q ∈ interior K, fderiv ℝ w q = Gw q := by
    intro q hq
    exact (fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hq)).symm
  have hderivf : ∀ q ∈ interior K, fderiv ℝ f q = Gf q := by
    intro q hq
    exact (fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hq)).symm
  have hbound : ∀ q ∈ K, |Gf q (0, 1)| ≤ Bv := hhvertical
  have h := intervalIntegral.abs_fderivWithin_weightedDiagonalError_vertical_le
    hT hwC1.continuousOn hfC1.continuousOn hGw hGf
    hdw hdf hderivw hderivf hweight hbound hc hBv hp
  have heq : EqOn (canonicalSourceFactor S)
      (intervalIntegral.weightedDiagonalError w f) K := by
    intro q hq
    exact canonical_source_factor_eq_weightedDiagonalError hT hTb H hq
  rw [fderivWithin_congr' heq hp]
  exact h

/-- At width at most one, the quadratic mass source has the exact outgoing
first-jet value bound derived from the source-factor estimate. -/
theorem canonical_quadratic_kernel_vertical_jet_abs_le
    {b T c C Bv L : ℝ} (hT : 0 < T) (hTwidth : T ≤ 1) (hTb : T < b)
    (hc : 0 < c) (hC : 0 ≤ C) (hBv : 0 ≤ Bv) (hL : 0 ≤ L)
    {S : Fields} (H : IsC1Solution (developmentWithInitialEdge b) S)
    (hweight : ∀ p ∈ closedCoordTriangle 0 T,
      c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C)
    (hhvertical : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (outgoingQuotient S)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ Bv)
    (hlamVertical : ∀ p ∈ closedCoordTriangle 0 T,
      |(fderivWithin ℝ (fun q : ℝ × ℝ => S.lam q.1 q.2)
        (closedCoordTriangle 0 T) p) (0, 1)| ≤ L)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle 0 T) :
    |(fderivWithin ℝ
      (intervalIntegral.weightedDiagonalQuadraticKernel
        (fun q => S.lam q.1 q.2) (outgoingQuotient S))
      (closedCoordTriangle 0 T) p) (0, 1)| ≤
      (L * Bv ^ 2 + 2 * C * Bv * (Bv + C * Bv / c)) * (p.2 - p.1) := by
  let K := closedCoordTriangle 0 T
  let w : ℝ × ℝ → ℝ := fun q => S.lam q.1 q.2
  let f := outgoingQuotient S
  let Hc := intervalIntegral.weightedDiagonalError w f
  have hwC1 : ContDiffOn ℝ 1 w K := (five_fields_contDiffOn hT hTb H).1
  have hHC1 : ContDiffOn ℝ 1 Hc K :=
    (canonical_source_factor_box_inputs hT hTb H).1.congr
      (fun q hq => (canonical_source_factor_eq_weightedDiagonalError
        hT hTb H hq).symm)
  have hjetw : ∀ q ∈ K,
      HasFDerivWithinAt w (fderivWithin ℝ w K q) K q := by
    intro q hq
    exact (hwC1.differentiableOn (by norm_num) q hq).hasFDerivWithinAt
  have hdle : p.2 - p.1 ≤ 1 := by
    have hcoord : 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ T := hp
    linarith
  have hwabs : |w p| ≤ C := by
    rw [abs_of_nonneg (hc.le.trans (hweight p hp).1)]
    exact (hweight p hp).2
  have hHabs : |Hc p| ≤ Bv * (p.2 - p.1) := by
    change |intervalIntegral.weightedDiagonalError
      (fun q => S.lam q.1 q.2) (outgoingQuotient S) p| ≤ _
    rw [← canonical_source_factor_eq_weightedDiagonalError hT hTb H hp]
    exact canonical_source_factor_abs_le_gap hT hTb hc hBv H
      (fun q hq => (hweight q hq).1) hhvertical hp
  have hHjet : |(fderivWithin ℝ Hc K p) (0, 1)| ≤
      Bv + C * Bv / c := by
    have heq : EqOn (canonicalSourceFactor S) Hc K := by
      intro q hq
      exact canonical_source_factor_eq_weightedDiagonalError hT hTb H hq
    rw [← fderivWithin_congr' heq hp]
    exact canonical_source_factor_vertical_jet_abs_le hT hTb hc hBv
      H hweight hhvertical hp
  exact intervalIntegral.abs_fderivWithin_weightedDiagonalQuadraticKernel_apply_le
    hT hjetw hHC1 hC hBv hL hp hdle hwabs
    (hlamVertical p hp) hHabs hHjet

end ChristodoulouBV.C1Solution

end
