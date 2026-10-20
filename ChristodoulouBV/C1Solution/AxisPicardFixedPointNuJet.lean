module

public import ChristodoulouBV.C1Solution.AxisPicardFixedPointJetBounds
public import ChristodoulouBV.ForMathlib.Analysis.Calculus.DiagonalVolterraRadiusJet
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# The incoming Picard output jet

The incoming field differentiates as the negative outgoing field on the
diagonal plus a vertical Volterra radius. The formula holds on the whole
closed triangle.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace ChristodoulouBV.AxisPicard

/-- Integrating a uniformly bounded triangle kernel vertically costs at
most the width of the triangle. -/
theorem abs_vertical_integral_le_const {a b A u v : ℝ}
    {k : ℝ × ℝ → ℝ} (hA : 0 ≤ A)
    (hk : ∀ p ∈ closedCoordTriangle a b, |k p| ≤ A)
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    |∫ s in u..v, k (u, s)| ≤ A * (b - a) := by
  have hbound : ∀ s ∈ Ι u v, ‖k (u, s)‖ ≤ A := by
    intro s hs
    have hsI : s ∈ Icc u v := by
      rw [uIoc_of_le huv] at hs
      exact ⟨hs.1.le, hs.2⟩
    simpa only [Real.norm_eq_abs] using
      hk (u, s) ⟨hau, hsI.1, hsI.2.trans hvb⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := u) (b := v) (C := A) (f := fun s => k (u, s)) hbound
  have hspan : v - u ≤ b - a := by linarith only [hau, hvb]
  have hnorm : |∫ s in u..v, k (u, s)| ≤ A * (v - u) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr huv)] using h
  exact hnorm.trans (mul_le_mul_of_nonneg_left hspan hA)

/-- The two outgoing coordinate derivatives have the sharper bounds needed
when the incoming field differentiates the diagonal outgoing trace. -/
theorem Box.picard_lam_fderiv_axes_bounds {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b) :
    |(fderivWithin ℝ (x.1.toTriple.picard a g hEdge).lam
      (closedCoordTriangle a b) p) (1, 0)| ≤
        ((numericalLedger M).K₀ + (numericalLedger M).K₁) * (b - a) ∧
      |(fderivWithin ℝ (x.1.toTriple.picard a g hEdge).lam
        (closedCoordTriangle a b) p) (0, 1)| ≤
        M + ((numericalLedger M).K₀ + (numericalLedger M).K₁) * (b - a) := by
  let C := ((numericalLedger M).K₀ + (numericalLedger M).K₁) * (b - a)
  have hu := x.picard_lam_primitive_coordinate_bound hab hM hsmall hp (0 : Fin 2)
  have hv := x.picard_lam_primitive_coordinate_bound hab hM hsmall hp (1 : Fin 2)
  simp only [coordinateDirection, ↓reduceIte] at hu
  have hv' : |horizontalIntegralJet a x.1.toTriple.gravitational
      (fderivWithin ℝ x.1.toTriple.gravitational
        (closedCoordTriangle a b)) p (0, 1)| ≤
      ((numericalLedger M).K₀ + (numericalLedger M).K₁) * (b - a) := by
    simpa [coordinateDirection] using hv
  have hpv : p.2 ∈ Icc a b := ⟨hp.1.trans hp.2.1, hp.2.2⟩
  have hedge := D.g_deriv_bound p.2 hpv
  constructor
  · rw [x.picard_lam_fderiv_apply D hab hM hsmall hp]
    simpa only [map_zero, zero_add] using hu
  · rw [x.picard_lam_fderiv_apply D hab hM hsmall hp]
    have hgedge : |(fderiv ℝ g p.2) (1 : ℝ)| ≤ M := by
      simpa only [fderiv_eq_deriv_mul, mul_one] using hedge
    have htriangle := abs_add_le ((fderiv ℝ g p.2) (1 : ℝ))
      (horizontalIntegralJet a x.1.toTriple.gravitational
        (fderivWithin ℝ x.1.toTriple.gravitational
          (closedCoordTriangle a b)) p (0, 1))
    have hfinal := htriangle.trans (add_le_add hgedge hv')
    simpa only [Prod.snd] using hfinal

/-- The derivative of the incoming Picard field is the vertical-radius
derivative minus the diagonal outgoing derivative. -/
theorem Box.picard_nu_fderiv_apply {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    {p : ℝ × ℝ} (hp : p ∈ closedCoordTriangle a b)
    (e : ℝ × ℝ) :
    (fderivWithin ℝ (x.1.toTriple.picard a g hEdge).nu
      (closedCoordTriangle a b) p) e =
      -((fderivWithin ℝ (x.1.toTriple.picard a g hEdge).lam
        (closedCoordTriangle a b) (p.1, p.1)) (e.1, e.1)) +
        (fderivWithin ℝ
          (intervalIntegral.weightedDiagonalRadius x.1.toTriple.gravitational)
          (closedCoordTriangle a b) p) e := by
  let K := closedCoordTriangle a b
  let lamNew := (x.1.toTriple.picard a g hEdge).lam
  let k := x.1.toTriple.gravitational
  let R := intervalIntegral.weightedDiagonalRadius k
  let diag : ℝ × ℝ → ℝ × ℝ := fun q => (q.1, q.1)
  let diagCLM : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hunique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b)
      (by rw [interior_closedCoordTriangle]; exact openCoordTriangle_nonempty hab)
  have hdiagMem : MapsTo diag K K := by
    intro q hq
    exact ⟨hq.1, le_refl _, hq.2.1.trans hq.2.2⟩
  have hdiagDeriv : fderivWithin ℝ diag K p = diagCLM := by
    have heq : diag = diagCLM := by
      funext q
      rfl
    rw [heq]
    exact diagCLM.hasFDerivAt.hasFDerivWithinAt.fderivWithin (hunique p hp)
  have hdiagDiff : DifferentiableWithinAt ℝ diag K p := by
    rw [show diag = diagCLM by funext q; rfl]
    exact diagCLM.hasFDerivAt.differentiableAt.differentiableWithinAt
  have hlamDiff : DifferentiableWithinAt ℝ lamNew K (diag p) :=
    ((x.picard_lam_c1 D hab hM hsmall).differentiableOn (by norm_num))
      (diag p) (hdiagMem hp)
  have hRDiff : DifferentiableWithinAt ℝ R K p := by
    have hR : ContDiffOn ℝ 1 R K :=
      intervalIntegral.contDiffOn_attenuatedVolterraPotential hab
        (x.picard_coefficients_c1 hab hM hsmall).1
    exact (hR.differentiableOn (by norm_num)) p hp
  have hcomp := fderivWithin_comp p hlamDiff hdiagDiff hdiagMem (hunique p hp)
  have hcomp' : fderivWithin ℝ (fun q => lamNew (diag q)) K p =
      (fderivWithin ℝ lamNew K (diag p)).comp
        (fderivWithin ℝ diag K p) := by
    simpa only [Function.comp_def] using hcomp
  have hneg := fderivWithin_fun_neg (𝕜 := ℝ) (f := fun q => lamNew (diag q))
    (hunique p hp)
  have hcompDiff : DifferentiableWithinAt ℝ
      (fun q => lamNew (diag q)) K p :=
    (hlamDiff.hasFDerivWithinAt.comp p hdiagDiff.hasFDerivWithinAt
      hdiagMem).differentiableWithinAt
  have hsum := fderivWithin_fun_add (hunique p hp) hcompDiff.neg hRDiff
  have hsum' : fderivWithin ℝ (fun q => -lamNew (diag q) + R q) K p =
      fderivWithin ℝ (fun q => -lamNew (diag q)) K p +
        fderivWithin ℝ R K p := by
    convert hsum using 1
  change (fderivWithin ℝ (fun q => -lamNew (diag q) + R q) K p) e = _
  rw [hsum', add_apply, hneg, neg_apply, hcomp', ContinuousLinearMap.comp_apply,
    hdiagDeriv]
  change -((fderivWithin ℝ lamNew K (p.1, p.1)) (e.1, e.1)) +
    (fderivWithin ℝ R K p) e = _
  rfl

/-- The incoming Picard output satisfies both coordinate derivative bounds
of the physical box. -/
theorem Box.picardJets_nu_coordinate_bound {a b M : ℝ}
    {g hEdge : ℝ → ℝ} (D : EdgeData a b M g hEdge)
    (x : Box a b M g hEdge) (hab : a < b) (hM : 1 ≤ M)
    (hsmall : b - a ≤ (numericalLedger M).lifetime M)
    (p : closedCoordTriangle a b) (i : Fin 2) :
    |(x.picardJets D hab hM hsmall).2.1.1.2 p
      (coordinateDirection i)| ≤ 2 * M := by
  let K := closedCoordTriangle a b
  let k := x.1.toTriple.gravitational
  let lamNew := (x.1.toTriple.picard a g hEdge).lam
  let R := intervalIntegral.weightedDiagonalRadius k
  let B := numericalLedger M
  have hdiag : (p.1.1, p.1.1) ∈ K :=
    ⟨p.2.1, le_refl _, p.2.2.1.trans p.2.2.2⟩
  have hLamAxes := x.picard_lam_fderiv_axes_bounds D hab hM hsmall hdiag
  have hLamDiag : |(fderivWithin ℝ lamNew K (p.1.1, p.1.1)) (1, 1)| ≤
      M + 2 * (B.K₀ + B.K₁) * (b - a) := by
    have heq : ((1 : ℝ), (1 : ℝ)) = (1, 0) + (0, 1) := by ext <;> norm_num
    rw [heq, map_add]
    have h := abs_add_le
      ((fderivWithin ℝ lamNew K (p.1.1, p.1.1)) (1, 0))
      ((fderivWithin ℝ lamNew K (p.1.1, p.1.1)) (0, 1))
    linarith only [h, hLamAxes.1, hLamAxes.2]
  have hk := (x.picard_coefficients_c1 hab hM hsmall).1
  have hRadU : |(fderivWithin ℝ R K p.1) (1, 0)| ≤ B.K₁ * (b - a) := by
    have hformula := intervalIntegral.radius_horizontal_jet_of_contDiffOn hab hk p.2
    have hbound : |∫ s in p.1.1..p.1.2,
        (fderivWithin ℝ k K (p.1.1, s)) (1, 0)| ≤ B.K₁ * (b - a) := by
      apply abs_vertical_integral_le_const
        (k := fun q => (fderivWithin ℝ k K q) (1, 0))
        B.nonneg.2.2.1 ?_
        p.2.1 p.2.2.1 p.2.2.2
      intro q hq
      exact (x.gravitational_jet_bounds_ledger x hab hM hsmall hq
        (by simp : (1, 0) ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)))).1
    rw [hformula, x.1.toTriple.gravitational_diag]
    simpa only [neg_zero, zero_add] using hbound
  have hRadV : (fderivWithin ℝ R K p.1) (0, 1) = k p.1 :=
    intervalIntegral.radius_vertical_jet_of_contDiffOn hab hk p.2
  have hkVal : |k p.1| ≤ B.K₀ * (b - a) :=
    x.picard_lam_horizontal_deriv_bound hab hM hsmall p.2
  have hC := B.coefficients_le_Cstar hM
  have hK₀T : B.K₀ * (b - a) ≤ 1 / 100 :=
    B.coefficient_mul_width_le hab hM hsmall hC.2.2.2.1
  have hK₁T : B.K₁ * (b - a) ≤ 1 / 100 :=
    B.coefficient_mul_width_le hab hM hsmall hC.2.2.2.2.1
  change |(fderivWithin ℝ (x.1.toTriple.picard a g hEdge).nu K p.1)
    (coordinateDirection i)| ≤ 2 * M
  fin_cases i
  · have hformula := x.picard_nu_fderiv_apply D hab hM hsmall p.2 (1, 0)
    have htriangle := abs_add_le
      (-((fderivWithin ℝ lamNew K (p.1.1, p.1.1)) (1, 1)))
      ((fderivWithin ℝ R K p.1) (1, 0))
    rw [abs_neg] at htriangle
    have hsum : M + 2 * (B.K₀ + B.K₁) * (b - a) +
        B.K₁ * (b - a) ≤ 2 * M := by
      nlinarith only [hK₀T, hK₁T, hM]
    have hbound : |(fderivWithin ℝ (x.1.toTriple.picard a g hEdge).nu K p.1)
        (1, 0)| ≤ 2 * M := by
      rw [hformula]
      linarith only [htriangle, hLamDiag, hRadU, hsum]
    simpa [coordinateDirection] using hbound
  · have hformula := x.picard_nu_fderiv_apply D hab hM hsmall p.2 (0, 1)
    have hzero : (fderivWithin ℝ lamNew K (p.1.1, p.1.1)) (0, 0) = 0 := by
      exact map_zero _
    have hresult : (fderivWithin ℝ (x.1.toTriple.picard a g hEdge).nu K p.1)
        (0, 1) = k p.1 := by
      calc
        _ = -(fderivWithin ℝ lamNew K (p.1.1, p.1.1)) (0, 0) +
            (fderivWithin ℝ R K p.1) (0, 1) := by simpa using hformula
        _ = k p.1 := by rw [hzero, neg_zero, zero_add, hRadV]
    have hbound : |(fderivWithin ℝ (x.1.toTriple.picard a g hEdge).nu K p.1)
        (0, 1)| ≤ 2 * M := by
      rw [hresult]
      linarith only [hkVal, hK₀T, hM]
    simpa [coordinateDirection] using hbound

end ChristodoulouBV.AxisPicard

end
