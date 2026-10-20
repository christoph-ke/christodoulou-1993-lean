module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointFullPair
import all ChristodoulouBV.C1Solution.AxisPicardFixedPointFullPair
import Mathlib.Tactic

/-!
# Coefficient estimates for the axis Picard update

The full pair box yields relative `C¹` regularity and the value and first-jet
estimates for both nonlinear terms in the Picard integrals.
-/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- The first coefficient box in the two-input construction is the original
one-input coefficient box. -/
theorem Box.fullPair_first {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    (x.toCubicRationalFullPairBox y hab hM hsmall).pair.first =
      x.toCubicRationalTriangleBox hab hM
        ((numerical_lifetime_bounds hM (sub_pos.mpr hab) hsmall).1) := by
  simp [Box.toCubicRationalFullPairBox, Box.toCubicRationalPairBox,
    intervalIntegral.AttenuatedVolterraPairData.toCubicRationalPairBox,
    Box.toAttenuatedVolterraPairData]

/-- The second coefficient box in the two-input construction is the original
one-input coefficient box. -/
theorem Box.fullPair_second {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    (x.toCubicRationalFullPairBox y hab hM hsmall).pair.second =
      y.toCubicRationalTriangleBox hab hM
        ((numerical_lifetime_bounds hM (sub_pos.mpr hab) hsmall).1) := by
  simp [Box.toCubicRationalFullPairBox, Box.toCubicRationalPairBox,
    intervalIntegral.AttenuatedVolterraPairData.toCubicRationalPairBox,
    Box.toAttenuatedVolterraPairData]

/-- The distance stored by the full pair box is the input coordinate-jet
distance. -/
theorem Box.fullPair_distance {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    (x.toCubicRationalFullPairBox y hab hM hsmall).pair.D =
      x.1.coordinateDistance y.1 := by
  simp [Box.toCubicRationalFullPairBox, Box.toCubicRationalPairBox,
    intervalIntegral.AttenuatedVolterraPairData.toCubicRationalPairBox,
    Box.toAttenuatedVolterraPairData]

/-- The one-input rational coefficient box names the gravitational Picard
coefficient. -/
theorem Box.triangle_gravitational_eq {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsize : b - a ≤ 1) :
    intervalIntegral.rationalCubicCoefficient
      (x.toCubicRationalTriangleBox hab hM hsize).J
      (x.toCubicRationalTriangleBox hab hM hsize).r
      (x.toCubicRationalTriangleBox hab hM hsize).w
      (x.toCubicRationalTriangleBox hab hM hsize).z =
        x.1.toTriple.gravitational := by
  rfl

/-- The one-input rational coefficient box names the scalar Picard source. -/
theorem Box.triangle_scalarSource_eq {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsize : b - a ≤ 1) :
    intervalIntegral.rationalCubicSource
      (x.toCubicRationalTriangleBox hab hM hsize).J
      (x.toCubicRationalTriangleBox hab hM hsize).r
      (x.toCubicRationalTriangleBox hab hM hsize).w
      (x.toCubicRationalTriangleBox hab hM hsize).z
      (x.toCubicRationalTriangleBox hab hM hsize).H =
        x.1.toTriple.scalarSource := by
  rfl

/-- The two nonlinear Picard coefficients are relatively `C¹` on the closed
axis triangle for every boxed input at the numerical lifetime. -/
theorem Box.picard_coefficients_c1 {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M) :
    ContDiffOn ℝ 1 x.1.toTriple.gravitational (closedCoordTriangle a b) ∧
      ContDiffOn ℝ 1 x.1.toTriple.scalarSource (closedCoordTriangle a b) := by
  let B := x.toCubicRationalFullPairBox x hab hM hsmall
  have h := B.pair.first.contDiffOn_coefficients hab (by norm_num : (0 : ℝ) < 1 / 4)
    B.ε_pos (fun p hp hoff => by linarith [B.complement_first p hp])
  rw [x.fullPair_first x hab hM hsmall] at h
  rw [x.triangle_gravitational_eq hab hM _, x.triangle_scalarSource_eq hab hM _] at h
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- The gravitational coefficient and its difference obey the linear
axis-gap value estimates of the full pair box. -/
theorem Box.gravitational_value_bounds {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    let B := x.toCubicRationalFullPairBox y hab hM hsmall
    |x.1.toTriple.gravitational p| ≤ B.coefficientValueBound * (p.2 - p.1) ∧
      |y.1.toTriple.gravitational p| ≤ B.coefficientValueBound * (p.2 - p.1) ∧
      |x.1.toTriple.gravitational p - y.1.toTriple.gravitational p| ≤
        B.coefficientValueSubBound * (p.2 - p.1) *
          x.1.coordinateDistance y.1 := by
  dsimp only
  let B := x.toCubicRationalFullPairBox y hab hM hsmall
  have h := B.coefficient_value_bounds hab (by norm_num : (0 : ℝ) < 1 / 4) p hp
  rw [x.fullPair_first y hab hM hsmall,
    x.fullPair_second y hab hM hsmall,
    x.fullPair_distance y hab hM hsmall] at h
  rw [x.triangle_gravitational_eq hab hM _,
    y.triangle_gravitational_eq hab hM _] at h
  simpa only [B, intervalIntegral.CubicRationalFullPairBox.coefficientValueBound,
    intervalIntegral.CubicRationalFullPairBox.coefficientValueSubBound] using h

/-- Both gravitational coordinate derivatives and their difference obey the
uniform first-jet coefficient bounds on the closed triangle. -/
theorem Box.gravitational_jet_bounds {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    {e : ℝ × ℝ} (he : e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ))) :
    let B := x.toCubicRationalFullPairBox y hab hM hsmall
    |(fderivWithin ℝ x.1.toTriple.gravitational
      (closedCoordTriangle a b) p) e| ≤ B.coefficientJetBound ∧
    |(fderivWithin ℝ y.1.toTriple.gravitational
      (closedCoordTriangle a b) p) e| ≤ B.coefficientJetBound ∧
    |(fderivWithin ℝ x.1.toTriple.gravitational
      (closedCoordTriangle a b) p) e -
      (fderivWithin ℝ y.1.toTriple.gravitational
        (closedCoordTriangle a b) p) e| ≤
          B.coefficientJetSubBound * x.1.coordinateDistance y.1 := by
  dsimp only
  let B := x.toCubicRationalFullPairBox y hab hM hsmall
  have h := B.coefficient_jet_bounds hab (by norm_num : (0 : ℝ) < 1 / 4) p hp e he
  rw [x.fullPair_first y hab hM hsmall,
    x.fullPair_second y hab hM hsmall,
    x.fullPair_distance y hab hM hsmall] at h
  rw [x.triangle_gravitational_eq hab hM _,
    y.triangle_gravitational_eq hab hM _] at h
  simpa only [B, intervalIntegral.CubicRationalFullPairBox.coefficientJetBound,
    intervalIntegral.CubicRationalFullPairBox.coefficientJetSubBound] using h

/-- The scalar source and its difference obey the quadratic axis-gap value
estimates of the full pair box. -/
theorem Box.scalarSource_value_bounds {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    let B := x.toCubicRationalFullPairBox y hab hM hsmall
    |x.1.toTriple.scalarSource p| ≤
      B.sourceProductValueBound / (1 / 4 : ℝ) * (p.2 - p.1) ^ 2 ∧
    |y.1.toTriple.scalarSource p| ≤
      B.sourceProductValueBound / (1 / 4 : ℝ) * (p.2 - p.1) ^ 2 ∧
    |x.1.toTriple.scalarSource p - y.1.toTriple.scalarSource p| ≤
      (B.sourceProductValueSubBound / (1 / 4 : ℝ) +
        B.sourceProductValueBound / (1 / 4 : ℝ) ^ 2) *
          (p.2 - p.1) ^ 2 * x.1.coordinateDistance y.1 := by
  dsimp only
  let B := x.toCubicRationalFullPairBox y hab hM hsmall
  have h := B.source_value_bounds hab (by norm_num : (0 : ℝ) < 1 / 4) p hp
  rw [x.fullPair_first y hab hM hsmall,
    x.fullPair_second y hab hM hsmall,
    x.fullPair_distance y hab hM hsmall] at h
  rw [x.triangle_scalarSource_eq hab hM _,
    y.triangle_scalarSource_eq hab hM _] at h
  exact h

/-- Both scalar-source coordinate derivatives and their difference obey the
linear axis-gap first-jet bounds. -/
theorem Box.scalarSource_jet_bounds {a b M : ℝ} {g hEdge : ℝ → ℝ}
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    {e : ℝ × ℝ} (he : e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ))) :
    let B := x.toCubicRationalFullPairBox y hab hM hsmall
    |(fderivWithin ℝ x.1.toTriple.scalarSource
      (closedCoordTriangle a b) p) e| ≤
        (B.sourceProductJetBound / (1 / 4 : ℝ) +
          B.sourceProductValueBound * B.L / (1 / 4 : ℝ) ^ 2) *
          (p.2 - p.1) ∧
    |(fderivWithin ℝ y.1.toTriple.scalarSource
      (closedCoordTriangle a b) p) e| ≤
        (B.sourceProductJetBound / (1 / 4 : ℝ) +
          B.sourceProductValueBound * B.L / (1 / 4 : ℝ) ^ 2) *
          (p.2 - p.1) ∧
    |(fderivWithin ℝ x.1.toTriple.scalarSource
      (closedCoordTriangle a b) p) e -
      (fderivWithin ℝ y.1.toTriple.scalarSource
        (closedCoordTriangle a b) p) e| ≤
          (B.sourceProductJetSubBound / (1 / 4 : ℝ) +
            B.sourceProductJetBound / (1 / 4 : ℝ) ^ 2 +
            B.sourceProductValueSubBound * B.L / (1 / 4 : ℝ) ^ 2 +
            B.sourceProductValueBound / (1 / 4 : ℝ) ^ 2 +
            2 * B.sourceProductValueBound * B.L / (1 / 4 : ℝ) ^ 3) *
              (p.2 - p.1) * x.1.coordinateDistance y.1 := by
  dsimp only
  let B := x.toCubicRationalFullPairBox y hab hM hsmall
  have h := B.source_jet_bounds hab (by norm_num : (0 : ℝ) < 1 / 4) p hp e he
  rw [x.fullPair_first y hab hM hsmall,
    x.fullPair_second y hab hM hsmall,
    x.fullPair_distance y hab hM hsmall] at h
  rw [x.triangle_scalarSource_eq hab hM _,
    y.triangle_scalarSource_eq hab hM _] at h
  exact h

end ChristodoulouBV.AxisPicard

end
