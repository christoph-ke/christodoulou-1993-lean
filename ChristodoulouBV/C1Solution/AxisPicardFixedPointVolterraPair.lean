module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointPairQuotient
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.RemovableCoefficientsBoxVolterraPair
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# The common attenuated Volterra pair box for Picard inputs

Two inputs in the closed Picard box determine a pair of cubic numerators.
The source, attenuation, radius, and first-jet estimates are assembled here
without adding hypotheses to the coefficient lemmas.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- Two boxed inputs supply the common attenuated Volterra data with exactly
the weighted diagonal coefficients used by the numerical Picard ledger. -/
@[expose] def Box.toAttenuatedVolterraPairData {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x y : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M) (hsize : b - a ≤ 1) :
    intervalIntegral.AttenuatedVolterraPairData a b (1 / 4) := by
  let S₀ := intervalIntegral.weightedDiagonalQuadraticValueCoefficient (3 / 4) (2 * M)
  let S₁ := intervalIntegral.weightedDiagonalQuadraticDerivativeCoefficient
    (1 / 4) (3 / 4) (2 * M) (2 * M)
  let T₀ := intervalIntegral.weightedDiagonalQuotientValueCoefficient
    (1 / 4) (3 / 4) (2 * M)
  let T₁ := intervalIntegral.weightedDiagonalQuotientDerivativeCoefficient
    (1 / 4) (3 / 4) (2 * M) (2 * M) (3 / 4 + 2 * M)
  let SΔ₀ := intervalIntegral.weightedDiagonalQuadraticValueDifferenceCoefficient
    (1 / 4) (3 / 4) (2 * M)
  let SΔ₁ := intervalIntegral.weightedDiagonalQuadraticDerivativeDifferenceCoefficient
    (1 / 4) (3 / 4) (2 * M) (2 * M)
  let TΔ₀ := intervalIntegral.weightedDiagonalQuotientValueDifferenceCoefficient
    (1 / 4) (3 / 4) (2 * M)
  let TΔ₁ := intervalIntegral.weightedDiagonalQuotientDerivativeDifferenceCoefficient
    (1 / 4) (3 / 4) (2 * M) (2 * M) (3 / 4 + 2 * M) 2
  let D := x.1.coordinateDistance y.1
  have hD : 0 ≤ D :=
    (dist_nonneg).trans (x.1.dist_le_coordinateDistance hab.le y.1)
  have hS₀ : 0 ≤ S₀ := by
    dsimp [S₀, intervalIntegral.weightedDiagonalQuadraticValueCoefficient]
    positivity
  have hS₁ : 0 ≤ S₁ := by
    dsimp [S₁, intervalIntegral.weightedDiagonalQuadraticDerivativeCoefficient,
      intervalIntegral.weightedDiagonalErrorDerivativeCoefficient]
    positivity
  have hT₀ : 0 ≤ T₀ := by
    dsimp [T₀, intervalIntegral.weightedDiagonalQuotientValueCoefficient]
    positivity
  have hT₁ : 0 ≤ T₁ := by
    dsimp [T₁, intervalIntegral.weightedDiagonalQuotientDerivativeCoefficient,
      intervalIntegral.weightedDiagonalQuadraticDerivativeCoefficient,
      intervalIntegral.weightedDiagonalQuadraticValueCoefficient,
      intervalIntegral.weightedDiagonalErrorDerivativeCoefficient]
    positivity
  have hSΔ₀ : 0 ≤ SΔ₀ := by
    dsimp [SΔ₀, intervalIntegral.weightedDiagonalQuadraticValueDifferenceCoefficient,
      intervalIntegral.weightedDiagonalErrorValueDifferenceCoefficient]
    positivity
  have hSΔ₁ : 0 ≤ SΔ₁ := by
    dsimp [SΔ₁, intervalIntegral.weightedDiagonalQuadraticDerivativeDifferenceCoefficient,
      intervalIntegral.weightedDiagonalErrorValueDifferenceCoefficient,
      intervalIntegral.weightedDiagonalErrorDerivativeCoefficient,
      intervalIntegral.weightedDiagonalErrorDerivativeDifferenceCoefficient]
    positivity
  have hTΔ₀ : 0 ≤ TΔ₀ := by
    dsimp [TΔ₀, intervalIntegral.weightedDiagonalQuotientValueDifferenceCoefficient,
      intervalIntegral.weightedDiagonalQuadraticValueDifferenceCoefficient,
      intervalIntegral.weightedDiagonalQuadraticValueCoefficient,
      intervalIntegral.weightedDiagonalErrorValueDifferenceCoefficient]
    positivity
  have hTΔ₁ : 0 ≤ TΔ₁ := by
    dsimp [TΔ₁, intervalIntegral.weightedDiagonalQuotientDerivativeDifferenceCoefficient,
      intervalIntegral.weightedDiagonalQuadraticDerivativeDifferenceCoefficient,
      intervalIntegral.weightedDiagonalQuadraticDerivativeCoefficient,
      intervalIntegral.weightedDiagonalQuadraticValueDifferenceCoefficient,
      intervalIntegral.weightedDiagonalQuadraticValueCoefficient,
      intervalIntegral.weightedDiagonalErrorValueDifferenceCoefficient,
      intervalIntegral.weightedDiagonalErrorDerivativeCoefficient,
      intervalIntegral.weightedDiagonalErrorDerivativeDifferenceCoefficient]
    positivity
  have hxj : (x.toCubicRationalTriangleBox hab hM hsize).J =
      x.1.toTriple.massNumerator := rfl
  have hyj : (y.toCubicRationalTriangleBox hab hM hsize).J =
      y.1.toTriple.massNumerator := rfl
  have hxr : (x.toCubicRationalTriangleBox hab hM hsize).r =
      x.1.toTriple.radius := rfl
  have hyr : (y.toCubicRationalTriangleBox hab hM hsize).r =
      y.1.toTriple.radius := rfl
  refine {
    first := x.toCubicRationalTriangleBox hab hM hsize
    second := y.toCubicRationalTriangleBox hab hM hsize
    j₁ := x.1.toTriple.massSource
    j₂ := y.1.toTriple.massSource
    k₁ := x.1.toTriple.attenuation
    k₂ := y.1.toTriple.attenuation
    first_eq := ?_
    second_eq := ?_
    hab := hab
    width_le_one := hsize
    j₁_c1 := (x.massSource_attenuation_c1 hab).1
    j₂_c1 := (y.massSource_attenuation_c1 hab).1
    k₁_c1 := (x.massSource_attenuation_c1 hab).2
    k₂_c1 := (y.massSource_attenuation_c1 hab).2
    j_diag := ?_
    S₀ := S₀
    S₁ := S₁
    T₀ := T₀
    T₁ := T₁
    SΔ₀ := SΔ₀
    SΔ₁ := SΔ₁
    TΔ₀ := TΔ₀
    TΔ₁ := TΔ₁
    R₁ := 3 / 4 + 2 * M
    RΔ := 2
    D := D
    coeff_nonneg := ⟨hS₀, hS₁, hT₀, hT₁, hSΔ₀, hSΔ₁, hTΔ₀, hTΔ₁,
      by linarith only [hM], by norm_num, hD⟩
    source_bound := ?_
    kernel_bound := ?_
    source_jet_bound := ?_
    kernel_jet_bound := ?_
    source_sub_bound := ?_
    kernel_sub_bound := ?_
    source_jet_sub_bound := ?_
    kernel_jet_sub_bound := ?_
    radius_jet_bound := ?_
    radius_sub_bound := ?_
    radius_jet_sub_bound := ?_
  }
  · rw [hxj]
    rfl
  · rw [hyj]
    rfl
  · constructor
    · intro u hu
      have hpos : x.1.1.extendValue (u, u) ≠ 0 := by
        have hq : (u, u) ∈ closedCoordTriangle a b := by
          exact (diagonalPoint (a := a) (b := b) ⟨u, hu⟩).2
        exact ne_of_gt ((by norm_num : (0 : ℝ) < 1 / 4).trans_le
          (x.lam_value_bounds hq).1)
      exact intervalIntegral.weightedDiagonalQuadraticKernel_diag hpos
    · intro u hu
      have hpos : y.1.1.extendValue (u, u) ≠ 0 := by
        have hq : (u, u) ∈ closedCoordTriangle a b := by
          exact (diagonalPoint (a := a) (b := b) ⟨u, hu⟩).2
        exact ne_of_gt ((by norm_num : (0 : ℝ) < 1 / 4).trans_le
          (y.lam_value_bounds hq).1)
      exact intervalIntegral.weightedDiagonalQuadraticKernel_diag hpos
  · intro p hp
    have hxbound := (x.massSource_bounds hab hM hsize hp).1
    have hybound := (y.massSource_bounds hab hM hsize hp).1
    have hxpos := intervalIntegral.weightedDiagonalQuadraticKernel_nonneg
      (f := x.1.2.2.extendValue) (p := p)
      ((by norm_num : (0 : ℝ) ≤ 1 / 4).trans (x.lam_value_bounds hp).1)
    have hypos := intervalIntegral.weightedDiagonalQuadraticKernel_nonneg
      (f := y.1.2.2.extendValue) (p := p)
      ((by norm_num : (0 : ℝ) ≤ 1 / 4).trans (y.lam_value_bounds hp).1)
    exact ⟨⟨hxpos, (le_abs_self _).trans hxbound⟩,
      ⟨hypos, (le_abs_self _).trans hybound⟩⟩
  · intro p hp
    have hxbound := x.attenuation_bounds hab hM hsize hp
    have hybound := y.attenuation_bounds hab hM hsize hp
    exact ⟨⟨hxbound.1, hxbound.2.1⟩, ⟨hybound.1, hybound.2.1⟩⟩
  · intro p hp
    exact ⟨(x.massSource_bounds hab hM hsize hp).2.1,
      (y.massSource_bounds hab hM hsize hp).2.1⟩
  · intro p hp
    exact ⟨(x.attenuation_bounds hab hM hsize hp).2.2.1,
      (y.attenuation_bounds hab hM hsize hp).2.2.1⟩
  · intro p hp
    exact (x.massSource_difference_bounds y hab hM hsize hp).1
  · intro p hp
    exact (x.attenuation_difference_bounds y hab hM hsize hp).1
  · intro p hp
    exact (x.massSource_difference_bounds y hab hM hsize hp).2.1
  · intro p hp
    exact (x.attenuation_difference_bounds y hab hM hsize hp).2.1
  · intro p hp e he
    rcases he with rfl | rfl
    · exact ⟨x.radius_jet_bound hab hM hsize hp (0 : Fin 2),
        y.radius_jet_bound hab hM hsize hp (0 : Fin 2)⟩
    · exact ⟨x.radius_jet_bound hab hM hsize hp (1 : Fin 2),
        y.radius_jet_bound hab hM hsize hp (1 : Fin 2)⟩
  · intro p hp
    exact (x.radius_difference_bounds y hab hsize hp).1
  · intro p hp e he
    rcases he with rfl | rfl
    · exact (x.radius_difference_bounds y hab hsize hp).2.1
    · exact (x.radius_difference_bounds y hab hsize hp).2.2.trans
        (by nlinarith only [hD])

/-- The two boxed Picard inputs determine a common cubic numerator and
radius coefficient box, retaining the exact Volterra constants. -/
@[expose] def Box.toCubicRationalPairBox {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x y : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M) (hsize : b - a ≤ 1) :
    intervalIntegral.CubicRationalPairBox a b (1 / 4) :=
  (x.toAttenuatedVolterraPairData y hab hM hsize).toCubicRationalPairBox

end ChristodoulouBV.AxisPicard

end
