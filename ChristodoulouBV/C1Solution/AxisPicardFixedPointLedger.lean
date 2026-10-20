module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointCoefficients
import all ChristodoulouBV.C1Solution.AxisPicardFixedPointFullPair
import Mathlib.Tactic

/-!
# The gravitational coefficients in the explicit Picard ledger

The constants stored by the two-input rational coefficient box are bounded by
the corresponding entries of the explicit numerical ledger.
-/

public section

noncomputable section

namespace ChristodoulouBV.AxisPicard

/-- The gravitational value coefficient is within the explicit ledger. -/
theorem Box.coefficientValueBound_le_ledger {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    (x.toCubicRationalFullPairBox y hab hM hsmall).coefficientValueBound ≤
      (numericalLedger M).K₀ := by
  dsimp [intervalIntegral.CubicRationalFullPairBox.coefficientValueBound,
    Box.toCubicRationalFullPairBox, Box.toCubicRationalPairBox,
    intervalIntegral.AttenuatedVolterraPairData.toCubicRationalPairBox,
    Box.toAttenuatedVolterraPairData,
    intervalIntegral.AttenuatedVolterraPairData.valueCoefficient,
    numericalLedger]
  exact le_max_right _ _

/-- The gravitational coordinate-jet coefficient is within the explicit ledger. -/
theorem Box.coefficientJetBound_le_ledger {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    (x.toCubicRationalFullPairBox y hab hM hsmall).coefficientJetBound ≤
      (numericalLedger M).K₁ := by
  dsimp [intervalIntegral.CubicRationalFullPairBox.coefficientJetBound,
    Box.toCubicRationalFullPairBox, Box.toCubicRationalPairBox,
    intervalIntegral.AttenuatedVolterraPairData.toCubicRationalPairBox,
    Box.toAttenuatedVolterraPairData,
    intervalIntegral.AttenuatedVolterraPairData.valueCoefficient,
    intervalIntegral.AttenuatedVolterraPairData.jetCoefficient,
    intervalIntegral.weightedDiagonalQuadraticValueCoefficient,
    intervalIntegral.weightedDiagonalQuadraticDerivativeCoefficient,
    intervalIntegral.weightedDiagonalErrorDerivativeCoefficient,
    intervalIntegral.weightedDiagonalQuotientValueCoefficient,
    intervalIntegral.weightedDiagonalQuotientDerivativeCoefficient,
    numericalLedger]
  convert (le_max_right (0 : ℝ) _) using 1
  ring_nf

/-- The gravitational value-difference coefficient is within the explicit ledger. -/
theorem Box.coefficientValueSubBound_le_ledger {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    (x.toCubicRationalFullPairBox y hab hM hsmall).coefficientValueSubBound ≤
      (numericalLedger M).KΔ₀ := by
  dsimp [intervalIntegral.CubicRationalFullPairBox.coefficientValueSubBound,
    Box.toCubicRationalFullPairBox, Box.toCubicRationalPairBox,
    intervalIntegral.AttenuatedVolterraPairData.toCubicRationalPairBox,
    Box.toAttenuatedVolterraPairData,
    intervalIntegral.AttenuatedVolterraPairData.valueCoefficient,
    intervalIntegral.AttenuatedVolterraPairData.valueSubCoefficient,
    intervalIntegral.weightedDiagonalQuadraticValueCoefficient,
    intervalIntegral.weightedDiagonalQuadraticValueDifferenceCoefficient,
    intervalIntegral.weightedDiagonalQuotientValueCoefficient,
    intervalIntegral.weightedDiagonalQuotientValueDifferenceCoefficient,
    intervalIntegral.weightedDiagonalErrorValueDifferenceCoefficient,
    numericalLedger]
  convert (le_max_right (0 : ℝ) _) using 1

/-- The gravitational coordinate-jet difference coefficient is within the
explicit ledger, including all nine regular-product terms. -/
theorem Box.coefficientJetSubBound_le_ledger {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    (x.toCubicRationalFullPairBox y hab hM hsmall).coefficientJetSubBound ≤
      (numericalLedger M).KΔ₁ := by
  dsimp [intervalIntegral.CubicRationalFullPairBox.coefficientJetSubBound,
    Box.toCubicRationalFullPairBox, Box.toCubicRationalPairBox,
    intervalIntegral.AttenuatedVolterraPairData.toCubicRationalPairBox,
    Box.toAttenuatedVolterraPairData,
    intervalIntegral.AttenuatedVolterraPairData.valueCoefficient,
    intervalIntegral.AttenuatedVolterraPairData.jetCoefficient,
    intervalIntegral.AttenuatedVolterraPairData.valueSubCoefficient,
    intervalIntegral.AttenuatedVolterraPairData.jetSubCoefficient,
    intervalIntegral.weightedDiagonalQuadraticValueCoefficient,
    intervalIntegral.weightedDiagonalQuadraticDerivativeCoefficient,
    intervalIntegral.weightedDiagonalQuadraticValueDifferenceCoefficient,
    intervalIntegral.weightedDiagonalQuadraticDerivativeDifferenceCoefficient,
    intervalIntegral.weightedDiagonalQuotientValueCoefficient,
    intervalIntegral.weightedDiagonalQuotientDerivativeCoefficient,
    intervalIntegral.weightedDiagonalQuotientValueDifferenceCoefficient,
    intervalIntegral.weightedDiagonalQuotientDerivativeDifferenceCoefficient,
    intervalIntegral.weightedDiagonalErrorValueDifferenceCoefficient,
    intervalIntegral.weightedDiagonalErrorDerivativeDifferenceCoefficient,
    intervalIntegral.weightedDiagonalErrorDerivativeCoefficient,
    numericalLedger]
  convert (le_max_right (0 : ℝ) _) using 1
  ring_nf

/-- The actual gravitational terms satisfy the value and two-input
difference estimates with the named numerical-ledger constants. -/
theorem Box.gravitational_value_bounds_ledger {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x y : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |x.1.toTriple.gravitational p| ≤
        (numericalLedger M).K₀ * (p.2 - p.1) ∧
      |y.1.toTriple.gravitational p| ≤
        (numericalLedger M).K₀ * (p.2 - p.1) ∧
      |x.1.toTriple.gravitational p - y.1.toTriple.gravitational p| ≤
        (numericalLedger M).KΔ₀ * (p.2 - p.1) *
          x.1.coordinateDistance y.1 := by
  have h := x.gravitational_value_bounds y hab hM hsmall hp
  dsimp only at h
  have hgap : 0 ≤ p.2 - p.1 := sub_nonneg.mpr hp.2.1
  have hD : 0 ≤ x.1.coordinateDistance y.1 :=
    (dist_nonneg).trans (x.1.dist_le_coordinateDistance hab.le y.1)
  have h₀ := x.coefficientValueBound_le_ledger y hab hM hsmall
  have hΔ := x.coefficientValueSubBound_le_ledger y hab hM hsmall
  refine ⟨h.1.trans ?_, h.2.1.trans ?_, h.2.2.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right h₀ hgap
  · exact mul_le_mul_of_nonneg_right h₀ hgap
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hΔ hgap) hD

/-- The actual gravitational first jets satisfy the coordinate and
two-input difference estimates with the named numerical-ledger constants. -/
theorem Box.gravitational_jet_bounds_ledger {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x y : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    {e : ℝ × ℝ} (he : e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ))) :
    |(fderivWithin ℝ x.1.toTriple.gravitational
      (closedCoordTriangle a b) p) e| ≤ (numericalLedger M).K₁ ∧
    |(fderivWithin ℝ y.1.toTriple.gravitational
      (closedCoordTriangle a b) p) e| ≤ (numericalLedger M).K₁ ∧
    |(fderivWithin ℝ x.1.toTriple.gravitational
      (closedCoordTriangle a b) p) e -
      (fderivWithin ℝ y.1.toTriple.gravitational
        (closedCoordTriangle a b) p) e| ≤
          (numericalLedger M).KΔ₁ * x.1.coordinateDistance y.1 := by
  have h := x.gravitational_jet_bounds y hab hM hsmall hp he
  dsimp only at h
  have hD : 0 ≤ x.1.coordinateDistance y.1 :=
    (dist_nonneg).trans (x.1.dist_le_coordinateDistance hab.le y.1)
  have h₁ := x.coefficientJetBound_le_ledger y hab hM hsmall
  have hΔ := x.coefficientJetSubBound_le_ledger y hab hM hsmall
  exact ⟨h.1.trans h₁, h.2.1.trans h₁,
    h.2.2.trans (mul_le_mul_of_nonneg_right hΔ hD)⟩

/-- The scalar-source value coefficient is within the explicit ledger. -/
theorem Box.sourceValueBound_le_ledger {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    (x.toCubicRationalFullPairBox y hab hM hsmall).sourceProductValueBound /
        (1 / 4 : ℝ) ≤ (numericalLedger M).Q₀ := by
  dsimp [intervalIntegral.CubicRationalFullPairBox.sourceProductValueBound,
    intervalIntegral.CubicRationalFullPairBox.coefficientValueBound,
    Box.toCubicRationalFullPairBox, Box.toCubicRationalPairBox,
    intervalIntegral.AttenuatedVolterraPairData.toCubicRationalPairBox,
    Box.toAttenuatedVolterraPairData,
    intervalIntegral.AttenuatedVolterraPairData.valueCoefficient,
    intervalIntegral.weightedDiagonalQuadraticValueCoefficient,
    numericalLedger]
  exact le_max_right _ _

/-- The scalar-source first-jet coefficient is within the explicit ledger. -/
theorem Box.sourceJetBound_le_ledger {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    (x.toCubicRationalFullPairBox y hab hM hsmall).sourceProductJetBound /
        (1 / 4 : ℝ) +
      (x.toCubicRationalFullPairBox y hab hM hsmall).sourceProductValueBound *
        (x.toCubicRationalFullPairBox y hab hM hsmall).L / (1 / 4 : ℝ) ^ 2 ≤
      (numericalLedger M).Q₁ := by
  dsimp [intervalIntegral.CubicRationalFullPairBox.sourceProductJetBound,
    intervalIntegral.CubicRationalFullPairBox.sourceProductValueBound,
    intervalIntegral.CubicRationalFullPairBox.coefficientJetBound,
    intervalIntegral.CubicRationalFullPairBox.coefficientValueBound,
    Box.toCubicRationalFullPairBox, Box.toCubicRationalPairBox,
    intervalIntegral.AttenuatedVolterraPairData.toCubicRationalPairBox,
    Box.toAttenuatedVolterraPairData,
    intervalIntegral.AttenuatedVolterraPairData.valueCoefficient,
    intervalIntegral.AttenuatedVolterraPairData.jetCoefficient,
    intervalIntegral.weightedDiagonalQuadraticValueCoefficient,
    intervalIntegral.weightedDiagonalQuadraticDerivativeCoefficient,
    intervalIntegral.weightedDiagonalErrorDerivativeCoefficient,
    intervalIntegral.weightedDiagonalQuotientValueCoefficient,
    intervalIntegral.weightedDiagonalQuotientDerivativeCoefficient,
    numericalLedger]
  convert (le_max_right (0 : ℝ) _) using 1
  ring_nf

/-- The scalar-source value-difference coefficient is within the explicit
ledger. -/
theorem Box.sourceValueSubBound_le_ledger {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    (x.toCubicRationalFullPairBox y hab hM hsmall).sourceProductValueSubBound /
        (1 / 4 : ℝ) +
      (x.toCubicRationalFullPairBox y hab hM hsmall).sourceProductValueBound /
        (1 / 4 : ℝ) ^ 2 ≤ (numericalLedger M).QΔ₀ := by
  dsimp [intervalIntegral.CubicRationalFullPairBox.sourceProductValueSubBound,
    intervalIntegral.CubicRationalFullPairBox.sourceProductValueBound,
    intervalIntegral.CubicRationalFullPairBox.coefficientValueSubBound,
    intervalIntegral.CubicRationalFullPairBox.coefficientValueBound,
    Box.toCubicRationalFullPairBox, Box.toCubicRationalPairBox,
    intervalIntegral.AttenuatedVolterraPairData.toCubicRationalPairBox,
    Box.toAttenuatedVolterraPairData,
    intervalIntegral.AttenuatedVolterraPairData.valueCoefficient,
    intervalIntegral.AttenuatedVolterraPairData.valueSubCoefficient,
    intervalIntegral.weightedDiagonalQuadraticValueCoefficient,
    intervalIntegral.weightedDiagonalQuadraticValueDifferenceCoefficient,
    intervalIntegral.weightedDiagonalQuotientValueCoefficient,
    intervalIntegral.weightedDiagonalQuotientValueDifferenceCoefficient,
    intervalIntegral.weightedDiagonalErrorValueDifferenceCoefficient,
    numericalLedger]
  convert (le_max_right (0 : ℝ) _) using 1

/-- The actual scalar sources satisfy quadratic value and two-input
difference estimates with the named numerical-ledger constants. -/
theorem Box.scalarSource_value_bounds_ledger {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x y : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |x.1.toTriple.scalarSource p| ≤
        (numericalLedger M).Q₀ * (p.2 - p.1) ^ 2 ∧
      |y.1.toTriple.scalarSource p| ≤
        (numericalLedger M).Q₀ * (p.2 - p.1) ^ 2 ∧
      |x.1.toTriple.scalarSource p - y.1.toTriple.scalarSource p| ≤
        (numericalLedger M).QΔ₀ * (p.2 - p.1) ^ 2 *
          x.1.coordinateDistance y.1 := by
  have h := x.scalarSource_value_bounds y hab hM hsmall hp
  dsimp only at h
  have hD : 0 ≤ x.1.coordinateDistance y.1 :=
    (dist_nonneg).trans (x.1.dist_le_coordinateDistance hab.le y.1)
  have h₀ := x.sourceValueBound_le_ledger y hab hM hsmall
  have hΔ := x.sourceValueSubBound_le_ledger y hab hM hsmall
  refine ⟨h.1.trans ?_, h.2.1.trans ?_, h.2.2.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right h₀ (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right h₀ (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hΔ (sq_nonneg _)) hD

/-- Both actual scalar-source coordinate derivatives have the linear
axis-gap bound in the numerical ledger. -/
theorem Box.scalarSource_jet_bound_ledger {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x y : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    {e : ℝ × ℝ} (he : e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ))) :
    |(fderivWithin ℝ x.1.toTriple.scalarSource
      (closedCoordTriangle a b) p) e| ≤
        (numericalLedger M).Q₁ * (p.2 - p.1) ∧
      |(fderivWithin ℝ y.1.toTriple.scalarSource
        (closedCoordTriangle a b) p) e| ≤
          (numericalLedger M).Q₁ * (p.2 - p.1) := by
  have h := x.scalarSource_jet_bounds y hab hM hsmall hp he
  dsimp only at h
  have hgap : 0 ≤ p.2 - p.1 := sub_nonneg.mpr hp.2.1
  have h₁ := x.sourceJetBound_le_ledger y hab hM hsmall
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_right h₁ hgap),
    h.2.1.trans (mul_le_mul_of_nonneg_right h₁ hgap)⟩

/-- The five-term scalar-source first-jet difference coefficient is within
the explicit ledger. -/
theorem Box.sourceJetSubBound_le_ledger {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    (x.toCubicRationalFullPairBox y hab hM hsmall).sourceProductJetSubBound /
        (1 / 4 : ℝ) +
      (x.toCubicRationalFullPairBox y hab hM hsmall).sourceProductJetBound /
        (1 / 4 : ℝ) ^ 2 +
      (x.toCubicRationalFullPairBox y hab hM hsmall).sourceProductValueSubBound *
        (x.toCubicRationalFullPairBox y hab hM hsmall).L / (1 / 4 : ℝ) ^ 2 +
      (x.toCubicRationalFullPairBox y hab hM hsmall).sourceProductValueBound /
        (1 / 4 : ℝ) ^ 2 +
      2 * (x.toCubicRationalFullPairBox y hab hM hsmall).sourceProductValueBound *
        (x.toCubicRationalFullPairBox y hab hM hsmall).L / (1 / 4 : ℝ) ^ 3 ≤
      (numericalLedger M).QΔ₁ := by
  dsimp [intervalIntegral.CubicRationalFullPairBox.sourceProductJetSubBound,
    intervalIntegral.CubicRationalFullPairBox.sourceProductJetBound,
    intervalIntegral.CubicRationalFullPairBox.sourceProductValueSubBound,
    intervalIntegral.CubicRationalFullPairBox.sourceProductValueBound,
    intervalIntegral.CubicRationalFullPairBox.coefficientJetSubBound,
    intervalIntegral.CubicRationalFullPairBox.coefficientJetBound,
    intervalIntegral.CubicRationalFullPairBox.coefficientValueSubBound,
    intervalIntegral.CubicRationalFullPairBox.coefficientValueBound,
    Box.toCubicRationalFullPairBox, Box.toCubicRationalPairBox,
    intervalIntegral.AttenuatedVolterraPairData.toCubicRationalPairBox,
    Box.toAttenuatedVolterraPairData,
    intervalIntegral.AttenuatedVolterraPairData.valueCoefficient,
    intervalIntegral.AttenuatedVolterraPairData.jetCoefficient,
    intervalIntegral.AttenuatedVolterraPairData.valueSubCoefficient,
    intervalIntegral.AttenuatedVolterraPairData.jetSubCoefficient,
    intervalIntegral.weightedDiagonalQuadraticValueCoefficient,
    intervalIntegral.weightedDiagonalQuadraticDerivativeCoefficient,
    intervalIntegral.weightedDiagonalQuadraticValueDifferenceCoefficient,
    intervalIntegral.weightedDiagonalQuadraticDerivativeDifferenceCoefficient,
    intervalIntegral.weightedDiagonalQuotientValueCoefficient,
    intervalIntegral.weightedDiagonalQuotientDerivativeCoefficient,
    intervalIntegral.weightedDiagonalQuotientValueDifferenceCoefficient,
    intervalIntegral.weightedDiagonalQuotientDerivativeDifferenceCoefficient,
    intervalIntegral.weightedDiagonalErrorValueDifferenceCoefficient,
    intervalIntegral.weightedDiagonalErrorDerivativeDifferenceCoefficient,
    intervalIntegral.weightedDiagonalErrorDerivativeCoefficient,
    numericalLedger]
  apply le_max_of_le_right
  ring_nf
  exact le_refl _

/-- The actual scalar-source first-jet difference obeys the linear axis-gap
estimate with the named numerical-ledger constant. -/
theorem Box.scalarSource_jet_sub_bound_ledger {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x y : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    {e : ℝ × ℝ} (he : e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ))) :
    |(fderivWithin ℝ x.1.toTriple.scalarSource
      (closedCoordTriangle a b) p) e -
      (fderivWithin ℝ y.1.toTriple.scalarSource
        (closedCoordTriangle a b) p) e| ≤
          (numericalLedger M).QΔ₁ * (p.2 - p.1) *
            x.1.coordinateDistance y.1 := by
  have h := (x.scalarSource_jet_bounds y hab hM hsmall hp he).2.2
  have hgap : 0 ≤ p.2 - p.1 := sub_nonneg.mpr hp.2.1
  have hD : 0 ≤ x.1.coordinateDistance y.1 :=
    (dist_nonneg).trans (x.1.dist_le_coordinateDistance hab.le y.1)
  have hΔ := x.sourceJetSubBound_le_ledger y hab hM hsmall
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hΔ hgap) hD)

end ChristodoulouBV.AxisPicard

end
