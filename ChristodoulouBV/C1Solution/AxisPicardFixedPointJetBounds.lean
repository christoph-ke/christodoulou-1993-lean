module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointHorizontalBounds
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# First-jet bounds for the axis Picard output

The horizontal primitive formula combines the normalized mean and its
derivative. This module applies that formula to the gravitational and scalar
Picard coefficients.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.AxisPicard

/-- Any nonnegative ledger coefficient below `Cstar` costs at most one
hundredth after multiplication by the permitted triangle width. -/
theorem Ledger.coefficient_mul_width_le {a b M c : ℝ} (B : Ledger)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ B.lifetime M)
    (hc : c ≤ B.Cstar M) :
    c * (b - a) ≤ 1 / 100 := by
  have hT : 0 < b - a := sub_pos.mpr hab
  have hCpos : 0 < B.Cstar M :=
    lt_of_lt_of_le (by norm_num) (B.coefficients_le_Cstar hM).1
  have hCT : B.Cstar M * (b - a) ≤ 1 / 100 := by
    have h := mul_le_mul_of_nonneg_left hsmall hCpos.le
    rw [Ledger.lifetime] at h
    convert h using 1
    field_simp
  exact (mul_le_mul_of_nonneg_right hc hT.le).trans hCT

/-- The coordinate components of a horizontal primitive jet are bounded
by the normalized value and derivative bounds. -/
theorem abs_horizontalIntegralJet_coordinate_le {a b A B : ℝ}
    {k : ℝ × ℝ → ℝ}
    {G : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (hmean : |horizontalMean a k p| ≤ A)
    (hjet : ∀ i : Fin 2,
      |horizontalMeanJet a G p (coordinateDirection i)| ≤ B)
    (i : Fin 2) :
    |horizontalIntegralJet a k G p (coordinateDirection i)| ≤
      A + B * (b - a) := by
  have hspan0 : 0 ≤ p.1 - a := sub_nonneg.mpr hp.1
  have hspan : p.1 - a ≤ b - a := by linarith only [hp.2.1, hp.2.2]
  have he : |(coordinateDirection i).1| ≤ (1 : ℝ) := by
    fin_cases i <;> norm_num [coordinateDirection]
  have hprod : |p.1 - a| *
      |horizontalMeanJet a G p (coordinateDirection i)| ≤ B * (b - a) := by
    rw [abs_of_nonneg hspan0]
    calc
      (p.1 - a) * |horizontalMeanJet a G p (coordinateDirection i)| ≤
          (p.1 - a) * B := mul_le_mul_of_nonneg_left (hjet i) hspan0
      _ ≤ B * (b - a) := by nlinarith only [hspan, hB]
  have hmeanprod : |horizontalMean a k p| *
      |(coordinateDirection i).1| ≤ A := by
    calc
      _ ≤ A * |(coordinateDirection i).1| :=
        mul_le_mul_of_nonneg_right hmean (abs_nonneg _)
      _ ≤ A := by nlinarith only [he, hA]
  rw [horizontalIntegralJet, add_apply, smul_apply, smul_apply]
  have hfst : (ContinuousLinearMap.fst ℝ ℝ ℝ)
      (coordinateDirection i) = (coordinateDirection i).1 := rfl
  rw [hfst]
  simp only [smul_eq_mul]
  calc
    _ ≤ |p.1 - a| * |horizontalMeanJet a G p (coordinateDirection i)| +
        |horizontalMean a k p| * |(coordinateDirection i).1| := by
      simpa only [abs_mul] using abs_add_le
        ((p.1 - a) * horizontalMeanJet a G p (coordinateDirection i))
        (horizontalMean a k p * (coordinateDirection i).1)
    _ ≤ A + B * (b - a) := by linarith only [hprod, hmeanprod]

/-- The gravitational horizontal primitive jet is bounded by the first two
ledger coefficients times the width. -/
theorem Box.picard_lam_primitive_coordinate_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (i : Fin 2) :
    |horizontalIntegralJet a x.1.toTriple.gravitational
      (fderivWithin ℝ x.1.toTriple.gravitational
        (closedCoordTriangle a b)) p (coordinateDirection i)| ≤
      ((numericalLedger M).K₀ + (numericalLedger M).K₁) * (b - a) := by
  let B := numericalLedger M
  have hmean : |horizontalMean a x.1.toTriple.gravitational p| ≤
      B.K₀ * (b - a) := by
    apply abs_horizontalMean_le_linear B.nonneg.2.1 ?_ hp
    intro q hq
    exact (x.gravitational_value_bounds_ledger x hab hM hsmall hq).1
  have hG : ContinuousOn
      (fderivWithin ℝ x.1.toTriple.gravitational
        (closedCoordTriangle a b)) (closedCoordTriangle a b) := by
    exact (x.picard_coefficients_c1 hab hM hsmall).1.continuousOn_fderivWithin
      (uniqueDiffOn_convex (convex_closedCoordTriangle a b)
        (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab))
      (by norm_num)
  have hjet : ∀ j : Fin 2,
      |horizontalMeanJet a
        (fderivWithin ℝ x.1.toTriple.gravitational
          (closedCoordTriangle a b)) p (coordinateDirection j)| ≤ B.K₁ := by
    intro j
    apply abs_horizontalMeanJet_coordinate_le hG B.nonneg.2.2.1 ?_ hp j
    intro q hq
    exact ⟨(x.gravitational_jet_bounds_ledger x hab hM hsmall hq
      (by simp : (1, 0) ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)))).1,
      (x.gravitational_jet_bounds_ledger x hab hM hsmall hq
      (by simp : (0, 1) ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)))).1⟩
  have h := abs_horizontalIntegralJet_coordinate_le
    (mul_nonneg B.nonneg.2.1 (sub_nonneg.mpr hab.le))
    B.nonneg.2.2.1 hp hmean hjet i
  convert h using 1
  ring

/-- The derivative of the outgoing Picard field is the edge derivative plus
the horizontal primitive jet. -/
theorem Box.picard_lam_fderiv_apply {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (e : ℝ × ℝ) :
    (fderivWithin ℝ (x.1.toTriple.picard a g hEdge).lam
      (closedCoordTriangle a b) p) e =
      (fderiv ℝ g p.2) e.2 +
        horizontalIntegralJet a x.1.toTriple.gravitational
          (fderivWithin ℝ x.1.toTriple.gravitational
            (closedCoordTriangle a b)) p e := by
  let K := closedCoordTriangle a b
  let k := x.1.toTriple.gravitational
  let G := fderivWithin ℝ k K
  have hk := (x.picard_coefficients_c1 hab hM hsmall).1
  have hunique : UniqueDiffWithinAt ℝ K p :=
    (uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)) p hp
  have hG : ContinuousOn G K :=
    hk.continuousOn_fderivWithin
      (uniqueDiffOn_convex (convex_closedCoordTriangle a b)
        (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab))
      (by norm_num)
  have hdiff : DifferentiableOn ℝ k (interior K) :=
    (hk.differentiableOn (by norm_num)).mono interior_subset
  have hderiv : ∀ q ∈ interior K, fderiv ℝ k q = G q := by
    intro q hq
    exact (fderivWithin_eq_fderiv
      ((uniqueDiffOn_convex (convex_closedCoordTriangle a b)
        (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab))
        q (interior_subset hq))
      ((hdiff q hq).differentiableAt (isOpen_interior.mem_nhds hq))).symm
  have hedge : DifferentiableWithinAt ℝ (fun q : ℝ × ℝ => g q.2) K p :=
    ((D.g_c1.comp contDiff_snd).differentiable (by norm_num) p)
      |>.differentiableWithinAt
  have hint : DifferentiableWithinAt ℝ
      (fun q : ℝ × ℝ => ∫ s in a..q.1, k (s, q.2)) K p :=
    (hasFDerivWithinAt_horizontal_integral hab hk.continuousOn hG
      hdiff hderiv hp).differentiableWithinAt
  have hsum := fderivWithin_fun_add hunique hedge hint
  have hedgeFormula := fderivWithin_upper_lift hab
    (D.g_c1.differentiable (by norm_num)) hp e
  have hintFormula := fderivWithin_horizontal_integral hab
    hk.continuousOn hG hdiff hderiv hp
  change (fderivWithin ℝ
      (fun q : ℝ × ℝ => g q.2 + ∫ s in a..q.1, k (s, q.2)) K p) e = _
  rw [hsum, add_apply, hedgeFormula, hintFormula]

/-- The outgoing Picard jet satisfies both coordinate derivative bounds of
the physical box. -/
theorem Box.picardJets_lam_coordinate_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (p : closedCoordTriangle a b) (i : Fin 2) :
    |(x.picardJets D hab hM hsmall).1.1.2 p
      (coordinateDirection i)| ≤ 2 * M := by
  let B := numericalLedger M
  have hpu : p.1.2 ∈ Icc a b := ⟨p.2.1.trans p.2.2.1, p.2.2.2⟩
  have hedge := upper_lift_coordinate_bound hab
    (D.g_c1.differentiable (by norm_num)) p.2 (by linarith only [hM])
    (D.g_deriv_bound p.1.2 hpu) i
  have hint := x.picard_lam_primitive_coordinate_bound hab hM hsmall p.2 i
  have hsmallB := B.lifetime_bounds hM (sub_pos.mpr hab) hsmall
  have hK₀ : B.K₀ * (b - a) ≤ 1 / 100 := by
    have hcoeff := (B.coefficients_le_Cstar hM).2.2.2.1
    have hT : 0 < b - a := sub_pos.mpr hab
    have hCpos : 0 < B.Cstar M :=
      lt_of_lt_of_le (by norm_num) (B.coefficients_le_Cstar hM).1
    have hC : B.Cstar M * (b - a) ≤ 1 / 100 := by
      have hsmall' : b - a ≤ B.lifetime M := hsmall
      have h := mul_le_mul_of_nonneg_left hsmall' hCpos.le
      rw [Ledger.lifetime] at h
      convert h using 1
      field_simp
    exact (mul_le_mul_of_nonneg_right hcoeff hT.le).trans hC
  have hK₁ : B.K₁ * (b - a) ≤ 1 / 100 := hsmallB.2.2.2.2.1
  change |(fderivWithin ℝ (x.1.toTriple.picard a g hEdge).lam
    (closedCoordTriangle a b) p.1) (coordinateDirection i)| ≤ 2 * M
  rw [x.picard_lam_fderiv_apply D hab hM hsmall p.2]
  have hedge' : |(fderiv ℝ g p.1.2) (coordinateDirection i).2| ≤ M := by
    rw [← fderivWithin_upper_lift hab
      (D.g_c1.differentiable (by norm_num)) p.2]
    exact hedge
  have htriangle := abs_add_le
    ((fderiv ℝ g p.1.2) (coordinateDirection i).2)
    (horizontalIntegralJet a x.1.toTriple.gravitational
      (fderivWithin ℝ x.1.toTriple.gravitational
        (closedCoordTriangle a b)) p.1 (coordinateDirection i))
  have hT : 0 ≤ b - a := sub_nonneg.mpr hab.le
  have hsum : (B.K₀ + B.K₁) * (b - a) ≤ 1 / 50 := by
    nlinarith only [hK₀, hK₁]
  linarith only [htriangle, hedge', hint, hsum, hM]

/-- The scalar horizontal primitive jet has a squared-width bound. -/
theorem Box.picard_h_primitive_coordinate_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (x : Box a b M g hEdge)
    (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (i : Fin 2) :
    |horizontalIntegralJet a x.1.toTriple.scalarSource
      (fderivWithin ℝ x.1.toTriple.scalarSource
        (closedCoordTriangle a b)) p (coordinateDirection i)| ≤
      ((numericalLedger M).Q₀ + (numericalLedger M).Q₁) * (b - a) ^ 2 := by
  let B := numericalLedger M
  have hT : 0 ≤ b - a := sub_nonneg.mpr hab.le
  have hmean : |horizontalMean a x.1.toTriple.scalarSource p| ≤
      B.Q₀ * (b - a) ^ 2 := by
    apply abs_horizontalMean_le_square B.nonneg.2.2.2.1 ?_ hp
    intro q hq
    exact (x.scalarSource_value_bounds_ledger x hab hM hsmall hq).1
  have hk := (x.picard_coefficients_c1 hab hM hsmall).2
  have hG : ContinuousOn
      (fderivWithin ℝ x.1.toTriple.scalarSource
        (closedCoordTriangle a b)) (closedCoordTriangle a b) :=
    hk.continuousOn_fderivWithin
      (uniqueDiffOn_convex (convex_closedCoordTriangle a b)
        (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab))
      (by norm_num)
  have hjet : ∀ j : Fin 2,
      |horizontalMeanJet a
        (fderivWithin ℝ x.1.toTriple.scalarSource
          (closedCoordTriangle a b)) p (coordinateDirection j)| ≤
        B.Q₁ * (b - a) := by
    intro j
    apply abs_horizontalMeanJet_coordinate_le hG
      (mul_nonneg B.nonneg.2.2.2.2.1 hT) ?_ hp j
    intro q hq
    have hgap : q.2 - q.1 ≤ b - a := by linarith only [hq.1, hq.2.2]
    have hu := (x.scalarSource_jet_bound_ledger x hab hM hsmall hq
      (by simp : (1, 0) ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)))).1
    have hv := (x.scalarSource_jet_bound_ledger x hab hM hsmall hq
      (by simp : (0, 1) ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)))).1
    exact ⟨hu.trans (mul_le_mul_of_nonneg_left hgap B.nonneg.2.2.2.2.1),
      hv.trans (mul_le_mul_of_nonneg_left hgap B.nonneg.2.2.2.2.1)⟩
  have h := abs_horizontalIntegralJet_coordinate_le
    (mul_nonneg B.nonneg.2.2.2.1 (sq_nonneg _))
    (mul_nonneg B.nonneg.2.2.2.2.1 hT) hp hmean hjet i
  convert h using 1
  ring

/-- The derivative of the scalar Picard field is the scalar edge derivative
plus the horizontal source primitive jet. -/
theorem Box.picard_h_fderiv_apply {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (e : ℝ × ℝ) :
    (fderivWithin ℝ (x.1.toTriple.picard a g hEdge).h
      (closedCoordTriangle a b) p) e =
      (fderiv ℝ hEdge p.2) e.2 +
        horizontalIntegralJet a x.1.toTriple.scalarSource
          (fderivWithin ℝ x.1.toTriple.scalarSource
            (closedCoordTriangle a b)) p e := by
  let K := closedCoordTriangle a b
  let k := x.1.toTriple.scalarSource
  let G := fderivWithin ℝ k K
  have hk := (x.picard_coefficients_c1 hab hM hsmall).2
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hG : ContinuousOn G K :=
    hk.continuousOn_fderivWithin hunique (by norm_num)
  have hdiff : DifferentiableOn ℝ k (interior K) :=
    (hk.differentiableOn (by norm_num)).mono interior_subset
  have hderiv : ∀ q ∈ interior K, fderiv ℝ k q = G q := by
    intro q hq
    exact (fderivWithin_eq_fderiv (hunique q (interior_subset hq))
      ((hdiff q hq).differentiableAt (isOpen_interior.mem_nhds hq))).symm
  have hedge : DifferentiableWithinAt ℝ (fun q : ℝ × ℝ => hEdge q.2) K p :=
    ((D.h_c1.comp contDiff_snd).differentiable (by norm_num) p)
      |>.differentiableWithinAt
  have hint : DifferentiableWithinAt ℝ
      (fun q : ℝ × ℝ => ∫ s in a..q.1, k (s, q.2)) K p :=
    (hasFDerivWithinAt_horizontal_integral hab hk.continuousOn hG
      hdiff hderiv hp).differentiableWithinAt
  have hsum := fderivWithin_fun_add (hunique p hp) hedge hint
  have hedgeFormula := fderivWithin_upper_lift hab
    (D.h_c1.differentiable (by norm_num)) hp e
  have hintFormula := fderivWithin_horizontal_integral hab
    hk.continuousOn hG hdiff hderiv hp
  change (fderivWithin ℝ
      (fun q : ℝ × ℝ => hEdge q.2 + ∫ s in a..q.1, k (s, q.2)) K p) e = _
  rw [hsum, add_apply, hedgeFormula, hintFormula]

/-- The scalar Picard output satisfies both coordinate derivative bounds of
the physical box. -/
theorem Box.picardJets_h_coordinate_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (p : closedCoordTriangle a b) (i : Fin 2) :
    |(x.picardJets D hab hM hsmall).2.2.1.2 p
      (coordinateDirection i)| ≤ 2 * M := by
  let B := numericalLedger M
  have hpu : p.1.2 ∈ Icc a b := ⟨p.2.1.trans p.2.2.1, p.2.2.2⟩
  have hedge := upper_lift_coordinate_bound hab
    (D.h_c1.differentiable (by norm_num)) p.2 (by linarith only [hM])
    (D.h_deriv_bound p.1.2 hpu) i
  have hint := x.picard_h_primitive_coordinate_bound hab hM hsmall p.2 i
  have hT : 0 < b - a := sub_pos.mpr hab
  have hTle : b - a ≤ 1 :=
    ((numericalLedger M).lifetime_bounds hM hT hsmall).1
  have hC := B.coefficients_le_Cstar hM
  have hCpos : 0 < B.Cstar M := lt_of_lt_of_le (by norm_num) hC.1
  have hCT : B.Cstar M * (b - a) ≤ 1 / 100 := by
    have hsmall' : b - a ≤ B.lifetime M := hsmall
    have h := mul_le_mul_of_nonneg_left hsmall' hCpos.le
    rw [Ledger.lifetime] at h
    convert h using 1
    field_simp
  have hQ₀T : B.Q₀ * (b - a) ≤ 1 / 100 :=
    (mul_le_mul_of_nonneg_right hC.2.2.2.2.2.1 hT.le).trans hCT
  have hQ₁T : B.Q₁ * (b - a) ≤ 1 / 100 :=
    (mul_le_mul_of_nonneg_right hC.2.2.2.2.2.2.1 hT.le).trans hCT
  have hQ₀Tsq : B.Q₀ * (b - a) ^ 2 ≤ 1 / 100 := by
    nlinarith only [hQ₀T, hTle, B.nonneg.2.2.2.1, hT.le]
  have hQ₁Tsq : B.Q₁ * (b - a) ^ 2 ≤ 1 / 100 := by
    nlinarith only [hQ₁T, hTle, B.nonneg.2.2.2.2.1, hT.le]
  change |(fderivWithin ℝ (x.1.toTriple.picard a g hEdge).h
    (closedCoordTriangle a b) p.1) (coordinateDirection i)| ≤ 2 * M
  rw [x.picard_h_fderiv_apply D hab hM hsmall p.2]
  have hedge' : |(fderiv ℝ hEdge p.1.2) (coordinateDirection i).2| ≤ M := by
    rw [← fderivWithin_upper_lift hab
      (D.h_c1.differentiable (by norm_num)) p.2]
    exact hedge
  have htriangle := abs_add_le
    ((fderiv ℝ hEdge p.1.2) (coordinateDirection i).2)
    (horizontalIntegralJet a x.1.toTriple.scalarSource
      (fderivWithin ℝ x.1.toTriple.scalarSource
        (closedCoordTriangle a b)) p.1 (coordinateDirection i))
  have hsum : (B.Q₀ + B.Q₁) * (b - a) ^ 2 ≤ 1 / 50 := by
    nlinarith only [hQ₀Tsq, hQ₁Tsq]
  linarith only [htriangle, hedge', hint, hsum, hM]

end ChristodoulouBV.AxisPicard

end
