module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointPairJet
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-! # Two-input incoming Picard jet bounds -/

public section

noncomputable section

open Set

namespace ChristodoulouBV.AxisPicard

/-- The horizontal radius primitive derivative difference has one width factor. -/
theorem Box.picard_radius_horizontal_sub_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x y : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |(fderivWithin ℝ
        (intervalIntegral.weightedDiagonalRadius x.1.toTriple.gravitational)
        (closedCoordTriangle a b) p) (1, 0) -
      (fderivWithin ℝ
        (intervalIntegral.weightedDiagonalRadius y.1.toTriple.gravitational)
        (closedCoordTriangle a b) p) (1, 0)| ≤
      (numericalLedger M).KΔ₁ * (b - a) *
        x.1.coordinateDistance y.1 := by
  let B := numericalLedger M
  let D := x.1.coordinateDistance y.1
  let K := closedCoordTriangle a b
  let k₁ := x.1.toTriple.gravitational
  let k₂ := y.1.toTriple.gravitational
  let F₁ := fun q => (fderivWithin ℝ k₁ K q) (1, 0)
  let F₂ := fun q => (fderivWithin ℝ k₂ K q) (1, 0)
  have hk₁ := (x.picard_coefficients_c1 hab hM hsmall).1
  have hk₂ := (y.picard_coefficients_c1 hab hM hsmall).1
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hF₁ : ContinuousOn F₁ K :=
    (hk₁.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hF₂ : ContinuousOn F₂ K :=
    (hk₂.continuousOn_fderivWithin hunique (by norm_num)).clm_apply continuousOn_const
  have hD : 0 ≤ D := (dist_nonneg).trans
    (x.1.dist_le_coordinateDistance hab.le y.1)
  have hC : 0 ≤ B.KΔ₁ := B.nonneg.2.2.2.2.2.2.1
  have hbound : ∀ q ∈ K, |F₁ q - F₂ q| ≤ B.KΔ₁ * D := by
    intro q hq
    exact (x.gravitational_jet_bounds_ledger y hab hM hsmall hq
      (by simp : (1, 0) ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)))).2.2
  have hint := abs_vertical_integral_sub_le_const hF₁ hF₂
    (mul_nonneg hC hD) hbound hp.1 hp.2.1 hp.2.2
  rw [intervalIntegral.radius_horizontal_jet_of_contDiffOn hab hk₁ hp,
    intervalIntegral.radius_horizontal_jet_of_contDiffOn hab hk₂ hp,
    x.1.toTriple.gravitational_diag, y.1.toTriple.gravitational_diag]
  simp only [neg_zero, zero_add]
  convert hint using 1
  ring

/-- The vertical radius primitive derivative difference is the kernel difference. -/
theorem Box.picard_radius_vertical_sub_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x y : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |(fderivWithin ℝ
        (intervalIntegral.weightedDiagonalRadius x.1.toTriple.gravitational)
        (closedCoordTriangle a b) p) (0, 1) -
      (fderivWithin ℝ
        (intervalIntegral.weightedDiagonalRadius y.1.toTriple.gravitational)
        (closedCoordTriangle a b) p) (0, 1)| ≤
      (numericalLedger M).KΔ₀ * (b - a) *
        x.1.coordinateDistance y.1 := by
  rw [intervalIntegral.radius_vertical_jet_of_contDiffOn hab
      (x.picard_coefficients_c1 hab hM hsmall).1 hp,
    intervalIntegral.radius_vertical_jet_of_contDiffOn hab
      (y.picard_coefficients_c1 hab hM hsmall).1 hp]
  have hgap : p.2 - p.1 ≤ b - a := by linarith only [hp.1, hp.2.2]
  have hD : 0 ≤ x.1.coordinateDistance y.1 := (dist_nonneg).trans
    (x.1.dist_le_coordinateDistance hab.le y.1)
  exact (x.gravitational_value_bounds_ledger y hab hM hsmall hp).2.2.trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgap
        (numericalLedger M).nonneg.2.2.2.2.2.1) hD)

/-- Diagonal outgoing derivative differences are bounded by the two
coordinate differences. -/
theorem Box.picard_lam_diagonal_derivative_sub_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {u : ℝ} (hu : u ∈ Icc a b) :
    |(fderivWithin ℝ (x.1.toTriple.picard a g hEdge).lam
        (closedCoordTriangle a b) (u, u)) (1, 1) -
      (fderivWithin ℝ (y.1.toTriple.picard a g hEdge).lam
        (closedCoordTriangle a b) (u, u)) (1, 1)| ≤
      2 * ((numericalLedger M).KΔ₀ + (numericalLedger M).KΔ₁) *
        (b - a) * x.1.coordinateDistance y.1 := by
  let p : closedCoordTriangle a b :=
    ⟨(u, u), ⟨hu.1, le_refl _, hu.2⟩⟩
  have h₀ := x.picard_lam_coordinate_sub_bound D y hab hM hsmall p 0
  have h₁ := x.picard_lam_coordinate_sub_bound D y hab hM hsmall p 1
  change |(fderivWithin ℝ (x.1.toTriple.picard a g hEdge).lam
      (closedCoordTriangle a b) (u, u)) (1, 0) -
    (fderivWithin ℝ (y.1.toTriple.picard a g hEdge).lam
      (closedCoordTriangle a b) (u, u)) (1, 0)| ≤ _ at h₀
  change |(fderivWithin ℝ (x.1.toTriple.picard a g hEdge).lam
      (closedCoordTriangle a b) (u, u)) (0, 1) -
    (fderivWithin ℝ (y.1.toTriple.picard a g hEdge).lam
      (closedCoordTriangle a b) (u, u)) (0, 1)| ≤ _ at h₁
  have heq : ((1 : ℝ), (1 : ℝ)) = (1, 0) + (0, 1) := by ext <;> norm_num
  rw [heq, map_add, map_add]
  have htriangle := abs_add_le
    ((fderivWithin ℝ (x.1.toTriple.picard a g hEdge).lam
      (closedCoordTriangle a b) (u, u)) (1, 0) -
      (fderivWithin ℝ (y.1.toTriple.picard a g hEdge).lam
        (closedCoordTriangle a b) (u, u)) (1, 0))
    ((fderivWithin ℝ (x.1.toTriple.picard a g hEdge).lam
      (closedCoordTriangle a b) (u, u)) (0, 1) -
      (fderivWithin ℝ (y.1.toTriple.picard a g hEdge).lam
        (closedCoordTriangle a b) (u, u)) (0, 1))
  have hrew :
      |(fderivWithin ℝ (x.1.toTriple.picard a g hEdge).lam
          (closedCoordTriangle a b) (u, u)) (1, 0) +
        (fderivWithin ℝ (x.1.toTriple.picard a g hEdge).lam
          (closedCoordTriangle a b) (u, u)) (0, 1) -
        ((fderivWithin ℝ (y.1.toTriple.picard a g hEdge).lam
          (closedCoordTriangle a b) (u, u)) (1, 0) +
        (fderivWithin ℝ (y.1.toTriple.picard a g hEdge).lam
          (closedCoordTriangle a b) (u, u)) (0, 1))| =
      |(fderivWithin ℝ (x.1.toTriple.picard a g hEdge).lam
          (closedCoordTriangle a b) (u, u)) (1, 0) -
        (fderivWithin ℝ (y.1.toTriple.picard a g hEdge).lam
          (closedCoordTriangle a b) (u, u)) (1, 0) +
        ((fderivWithin ℝ (x.1.toTriple.picard a g hEdge).lam
          (closedCoordTriangle a b) (u, u)) (0, 1) -
        (fderivWithin ℝ (y.1.toTriple.picard a g hEdge).lam
          (closedCoordTriangle a b) (u, u)) (0, 1))| := by
    congr 1
    ring
  rw [hrew]
  nlinarith only [h₀, h₁, htriangle]

/-- The incoming Picard horizontal coordinate derivative difference has
one width factor. -/
theorem Box.picard_nu_horizontal_sub_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (p : closedCoordTriangle a b) :
    |(x.picardJets D hab hM hsmall).2.1.1.2 p (1, 0) -
      (y.picardJets D hab hM hsmall).2.1.1.2 p (1, 0)| ≤
      (2 * (numericalLedger M).KΔ₀ +
        3 * (numericalLedger M).KΔ₁) * (b - a) *
        x.1.coordinateDistance y.1 := by
  let K := closedCoordTriangle a b
  let A₁ := (fderivWithin ℝ (x.1.toTriple.picard a g hEdge).lam K
    (p.1.1, p.1.1)) (1, 1)
  let A₂ := (fderivWithin ℝ (y.1.toTriple.picard a g hEdge).lam K
    (p.1.1, p.1.1)) (1, 1)
  let R₁ := (fderivWithin ℝ
    (intervalIntegral.weightedDiagonalRadius x.1.toTriple.gravitational) K p.1) (1, 0)
  let R₂ := (fderivWithin ℝ
    (intervalIntegral.weightedDiagonalRadius y.1.toTriple.gravitational) K p.1) (1, 0)
  have hu : p.1.1 ∈ Icc a b := ⟨p.2.1, p.2.2.1.trans p.2.2.2⟩
  have hA := x.picard_lam_diagonal_derivative_sub_bound D y hab hM hsmall hu
  have hR := x.picard_radius_horizontal_sub_bound y hab hM hsmall p.2
  have htriangle := abs_add_le (-(A₁ - A₂)) (R₁ - R₂)
  change |(fderivWithin ℝ (x.1.toTriple.picard a g hEdge).nu K p.1) (1, 0) -
    (fderivWithin ℝ (y.1.toTriple.picard a g hEdge).nu K p.1) (1, 0)| ≤ _
  rw [x.picard_nu_fderiv_apply D hab hM hsmall p.2,
    y.picard_nu_fderiv_apply D hab hM hsmall p.2]
  change |(-A₁ + R₁) - (-A₂ + R₂)| ≤ _
  calc
    _ = |-(A₁ - A₂) + (R₁ - R₂)| := by congr 1; ring
    _ ≤ |A₁ - A₂| + |R₁ - R₂| := by simpa only [abs_neg] using htriangle
    _ ≤ 2 * ((numericalLedger M).KΔ₀ +
        (numericalLedger M).KΔ₁) * (b - a) *
        x.1.coordinateDistance y.1 +
        (numericalLedger M).KΔ₁ * (b - a) *
        x.1.coordinateDistance y.1 := add_le_add hA hR
    _ = _ := by ring

/-- The incoming Picard vertical coordinate derivative difference is the
gravitational kernel difference. -/
theorem Box.picard_nu_vertical_sub_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (x y : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (p : closedCoordTriangle a b) :
    |(x.picardJets D hab hM hsmall).2.1.1.2 p (0, 1) -
      (y.picardJets D hab hM hsmall).2.1.1.2 p (0, 1)| ≤
      (numericalLedger M).KΔ₀ * (b - a) *
        x.1.coordinateDistance y.1 := by
  change |(fderivWithin ℝ (x.1.toTriple.picard a g hEdge).nu
      (closedCoordTriangle a b) p.1) (0, 1) -
    (fderivWithin ℝ (y.1.toTriple.picard a g hEdge).nu
      (closedCoordTriangle a b) p.1) (0, 1)| ≤ _
  rw [x.picard_nu_fderiv_apply D hab hM hsmall p.2,
    y.picard_nu_fderiv_apply D hab hM hsmall p.2]
  have hx : (fderivWithin ℝ (x.1.toTriple.picard a g hEdge).lam
      (closedCoordTriangle a b) (p.1.1, p.1.1)) (0, 0) = 0 := by
    exact map_zero _
  have hy : (fderivWithin ℝ (y.1.toTriple.picard a g hEdge).lam
      (closedCoordTriangle a b) (p.1.1, p.1.1)) (0, 0) = 0 := by
    exact map_zero _
  rw [hx, hy]
  simpa only [neg_zero, zero_add] using
    x.picard_radius_vertical_sub_bound y hab hM hsmall p.2

end ChristodoulouBV.AxisPicard

end
