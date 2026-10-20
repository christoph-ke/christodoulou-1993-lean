module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesFromFrozen
public import ChristodoulouBV.Uniqueness.RouteBLowerTilesOldCharacteristic
public import ChristodoulouBV.Uniqueness.RouteBLowerTilesHorizontalSafe
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# Characteristic equations recovered from the glued strip

The assembled strip has classical full jets. These imply the two
seven-state characteristic equations on every closed slice.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A safe classical seven-state strip solves the two characteristic
equations on every closed horizontal and vertical slice. -/
theorem characteristic_jets_of_classical_strip
    {a vStar η b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (hη : 0 < η) (hTop : vStar + η < b)
    (Z : ℝ × ℝ → C1Solution.RectangleState)
    (hZ : ContDiffOn ℝ 1 Z
      (Goursat.rectangle 0 a vStar (vStar + η)))
    (hsafe : ∀ p ∈ Goursat.rectangle 0 a vStar (vStar + η),
      C1Solution.IsSafeRectangleState (Z p))
    (hclassical : RouteBClassicalJetOn b
      (Goursat.rectangle 0 a vStar (vStar + η))
      (rectangleStateFields Z)) :
    ∀ u ∈ Icc 0 a, ∀ v ∈ Icc vStar (vStar + η),
      HasDerivWithinAt (fun s => (Z (s, v)).1)
        (C1Solution.rectangleF (Z (u, v))) (Icc 0 a) u ∧
      HasDerivWithinAt (fun t => (Z (u, t)).2)
        (C1Solution.rectangleG (Z (u, v)))
        (Icc vStar (vStar + η)) v := by
  intro u hu v hv
  let K := Goursat.rectangle 0 a vStar (vStar + η)
  let S := rectangleStateFields Z
  have hp : (u, v) ∈ K := Goursat.pair_mem_rectangle hu hv
  have hdev : (u, v) ∈ developmentWithInitialEdge b := by
    change 0 ≤ u ∧ u < v ∧ v < b
    exact ⟨hu.1, lt_of_le_of_lt hu.2 (haStar.trans_le hv.1),
      hv.2.trans_lt hTop⟩
  have hsafeP := hsafe (u, v) hp
  have hr : C1Solution.stateRadius (Z (u, v)) ≠ 0 :=
    ne_of_gt hsafeP.1
  have hgap : C1Solution.stateMassGap (Z (u, v)) ≠ 0 :=
    ne_of_gt hsafeP.2.2.2
  have hgrav : routeBMixedExpr (fun c => routeBField S c (u, v)) =
      C1Solution.stateGrav (Z (u, v)) := by
    change ((2 * C1Solution.stateMass (Z (u, v)) /
        C1Solution.stateRadius (Z (u, v))) *
        C1Solution.stateLam (Z (u, v)) *
        C1Solution.stateNu (Z (u, v))) /
        ((1 - 2 * C1Solution.stateMass (Z (u, v)) /
          C1Solution.stateRadius (Z (u, v))) *
          C1Solution.stateRadius (Z (u, v))) = _
    exact mixed_coefficient_eq_rectangle_grav hr hgap
  have hmass : routeBMassOutgoingExpr
      (fun c => routeBField S c (u, v)) =
      C1Solution.stateMassGap (Z (u, v)) /
        C1Solution.stateRadius (Z (u, v)) *
        C1Solution.stateTheta (Z (u, v)) ^ 2 /
        (2 * C1Solution.stateLam (Z (u, v))) := by
    change (1 - 2 * C1Solution.stateMass (Z (u, v)) /
        C1Solution.stateRadius (Z (u, v))) *
        C1Solution.stateTheta (Z (u, v)) ^ 2 /
        (2 * C1Solution.stateLam (Z (u, v))) = _
    exact mass_out_density_eq_rectangle_density hr
  have hψeq : EqOn (routeBScalarExpression routeBScalarRadiusExpr S)
      (fun p => C1Solution.statePsi (Z p)) K := by
    intro p hpk
    have hrp : C1Solution.stateRadius (Z p) ≠ 0 :=
      ne_of_gt (hsafe p hpk).1
    change C1Solution.stateRadius (Z p) *
      C1Solution.statePhi (Z p) = C1Solution.statePsi (Z p)
    unfold C1Solution.statePhi
    field_simp [hrp]
  have hlamU := hclassical.expansion_in (u, v) hp hdev
  have halphaU := hclassical.outgoing_in (u, v) hp hdev
  have hnuV := hclassical.contraction_out (u, v) hp hdev
  have hbetaV := hclassical.incoming_out (u, v) hp hdev
  have hmV := hclassical.mass_out (u, v) hp hdev
  have hrV := hclassical.radius_out (u, v) hp hdev
  have hψV := hclassical.scalar_radius_out (u, v) hp hdev
  change (fderivWithin ℝ
      (fun p => C1Solution.stateLam (Z p)) K (u, v)) (1, 0) =
      routeBMixedExpr (fun c => routeBField S c (u, v)) at hlamU
  change (fderivWithin ℝ
      (fun p => C1Solution.stateAlpha (Z p)) K (u, v)) (1, 0) =
      routeBMixedExpr (fun c => routeBField S c (u, v)) *
        C1Solution.statePhi (Z (u, v)) at halphaU
  change (fderivWithin ℝ
      (fun p => C1Solution.stateNu (Z p)) K (u, v)) (0, 1) =
      routeBMixedExpr (fun c => routeBField S c (u, v)) at hnuV
  change (fderivWithin ℝ
      (fun p => C1Solution.stateBeta (Z p)) K (u, v)) (0, 1) =
      routeBMixedExpr (fun c => routeBField S c (u, v)) *
        C1Solution.statePhi (Z (u, v)) at hbetaV
  change (fderivWithin ℝ
      (fun p => C1Solution.stateMass (Z p)) K (u, v)) (0, 1) =
      routeBMassOutgoingExpr (fun c => routeBField S c (u, v)) at hmV
  change (fderivWithin ℝ
      (fun p => C1Solution.stateRadius (Z p)) K (u, v)) (0, 1) =
      C1Solution.stateLam (Z (u, v)) at hrV
  change (fderivWithin ℝ
      (routeBScalarExpression routeBScalarRadiusExpr S) K (u, v))
      (0, 1) = C1Solution.stateAlpha (Z (u, v)) at hψV
  rw [fderivWithin_congr' hψeq hp] at hψV
  rw [hgrav] at hlamU halphaU hnuV hbetaV
  rw [hmass] at hmV
  have hlamC1 : ContDiffOn ℝ 1
      (fun p => C1Solution.stateLam (Z p)) K := hZ.fst.fst
  have halphaC1 : ContDiffOn ℝ 1
      (fun p => C1Solution.stateAlpha (Z p)) K := hZ.fst.snd
  have hnuC1 : ContDiffOn ℝ 1
      (fun p => C1Solution.stateNu (Z p)) K := hZ.snd.fst
  have hbetaC1 : ContDiffOn ℝ 1
      (fun p => C1Solution.stateBeta (Z p)) K := hZ.snd.snd.fst
  have hmC1 : ContDiffOn ℝ 1
      (fun p => C1Solution.stateMass (Z p)) K := hZ.snd.snd.snd.fst
  have hrC1 : ContDiffOn ℝ 1
      (fun p => C1Solution.stateRadius (Z p)) K :=
    hZ.snd.snd.snd.snd.fst
  have hψC1 : ContDiffOn ℝ 1
      (fun p => C1Solution.statePsi (Z p)) K :=
    hZ.snd.snd.snd.snd.snd
  have hLam := (C1Solution.coordinate_derivatives_of_contDiffOn_rectangle
    ha (by linarith only [hη]) hlamC1 hu hv).1
  have hAlpha := (C1Solution.coordinate_derivatives_of_contDiffOn_rectangle
    ha (by linarith only [hη]) halphaC1 hu hv).1
  have hNu := (C1Solution.coordinate_derivatives_of_contDiffOn_rectangle
    ha (by linarith only [hη]) hnuC1 hu hv).2
  have hBeta := (C1Solution.coordinate_derivatives_of_contDiffOn_rectangle
    ha (by linarith only [hη]) hbetaC1 hu hv).2
  have hMass := (C1Solution.coordinate_derivatives_of_contDiffOn_rectangle
    ha (by linarith only [hη]) hmC1 hu hv).2
  have hRadius := (C1Solution.coordinate_derivatives_of_contDiffOn_rectangle
    ha (by linarith only [hη]) hrC1 hu hv).2
  have hPsi := (C1Solution.coordinate_derivatives_of_contDiffOn_rectangle
    ha (by linarith only [hη]) hψC1 hu hv).2
  rw [hlamU] at hLam
  rw [halphaU] at hAlpha
  rw [hnuV] at hNu
  rw [hbetaV] at hBeta
  rw [hmV] at hMass
  rw [hrV] at hRadius
  rw [hψV] at hPsi
  change HasDerivWithinAt (fun s => (Z (s, v)).1.1) _ _ _ at hLam
  change HasDerivWithinAt (fun s => (Z (s, v)).1.2) _ _ _ at hAlpha
  change HasDerivWithinAt (fun t => (Z (u, t)).2.1) _ _ _ at hNu
  change HasDerivWithinAt (fun t => (Z (u, t)).2.2.1) _ _ _ at hBeta
  change HasDerivWithinAt (fun t => (Z (u, t)).2.2.2.1) _ _ _ at hMass
  change HasDerivWithinAt (fun t => (Z (u, t)).2.2.2.2.1) _ _ _ at hRadius
  change HasDerivWithinAt (fun t => (Z (u, t)).2.2.2.2.2) _ _ _ at hPsi
  constructor
  · simpa only [C1Solution.rectangleF] using hLam.prodMk hAlpha
  · simpa only [C1Solution.rectangleG] using
      hNu.prodMk (hBeta.prodMk
        (hMass.prodMk (hRadius.prodMk hPsi)))

end ChristodoulouBV.Uniqueness

end
