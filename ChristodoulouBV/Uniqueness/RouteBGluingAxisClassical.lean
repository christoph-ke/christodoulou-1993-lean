module

public import ChristodoulouBV.Uniqueness.RouteBGluingAxisJetCore
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Closed classical jet construction for an axis solution

The ordinary equations of an axis solution extend as relative jets across
its incoming edge. Rational source equations are used only off the axis.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- All seven primary axis fields are relatively C¹ on the closed triangle. -/
theorem routeB_axis_fields_c1
    {a b : ℝ} {T : Fields}
    (H : C1Solution.AxisClassicalSolution a b T) :
    RouteBFieldsC1On T (closedCoordTriangle a b) := by
  intro c
  cases c with
  | radius => exact H.r_c1
  | scalar => exact H.phi_c1
  | mass => exact H.m_c1
  | expansion => exact H.lam_c1
  | contraction => exact H.nu_c1
  | outgoing => exact H.alpha_c1
  | incoming => exact H.beta_c1

/-- The axis values and physical signs required by the clipped patch. -/
theorem routeB_axis_values_signs
    {a b : ℝ} {T : Fields}
    (H : C1Solution.AxisClassicalSolution a b T) :
    (∀ u ∈ Icc a b, T.r u u = 0 ∧ T.m u u = 0) ∧
    (∀ p ∈ closedCoordTriangle a b, 0 < T.lam p.1 p.2) ∧
    (∀ p ∈ closedCoordTriangle a b,
      p ∈ developmentWithInitialEdge b →
      0 < T.r p.1 p.2 ∧ T.nu p.1 p.2 < 0 ∧
        0 < 1 - 2 * T.m p.1 p.2 / T.r p.1 p.2) := by
  refine ⟨fun u hu => ⟨H.r_axis u hu, H.m_axis u hu⟩,
    H.lam_pos, ?_⟩
  intro p hp hpD
  have hD : p ∈ C1Solution.axisTriangleDevelopment a b :=
    ⟨hp.1, hpD.2.1, hpD.2.2⟩
  exact ⟨H.r_pos p hD, H.nu_neg p hD, H.gap_pos p hD⟩

/-- All twelve axis equations hold as relative jets, including on the
incoming edge and at its off-axis corner. -/
theorem routeB_axis_classicalJetOn
    {a b : ℝ} {T : Fields}
    (ha : 0 ≤ a) (hab : a < b)
    (H : C1Solution.AxisClassicalSolution a b T) :
    RouteBClassicalJetOn b (closedCoordTriangle a b) T := by
  let K := closedCoordTriangle a b
  let U := K ∩ developmentWithInitialEdge b
  have hC1 : RouteBFieldsC1On T K := routeB_axis_fields_c1 H
  have hCont (c : RouteBField) :
      ContinuousOn (fun p => routeBField T c p) U :=
    (hC1 c).continuousOn.mono inter_subset_left
  have hTheta : ContinuousOn
      (fun p : ℝ × ℝ => T.theta p.1 p.2) U :=
    (hC1.theta_zeta).1.continuousOn.mono inter_subset_left
  have hZeta : ContinuousOn
      (fun p : ℝ × ℝ => T.zeta p.1 p.2) U :=
    (hC1.theta_zeta).2.continuousOn.mono inter_subset_left
  have hRadiusNe : ∀ p ∈ U, T.r p.1 p.2 ≠ 0 :=
    fun p hp => ne_of_gt (H.r_pos p ⟨hp.1.1, hp.2.2.1, hp.2.2.2⟩)
  have hNuNe : ∀ p ∈ U, T.nu p.1 p.2 ≠ 0 :=
    fun p hp => ne_of_lt (H.nu_neg p ⟨hp.1.1, hp.2.2.1, hp.2.2.2⟩)
  have hRatio : ContinuousOn (fun p : ℝ × ℝ =>
      2 * T.m p.1 p.2 / T.r p.1 p.2) U :=
    (continuousOn_const.mul (hCont .mass)).div
      (hCont .radius) hRadiusNe
  have hGap : ContinuousOn (fun p : ℝ × ℝ =>
      1 - 2 * T.m p.1 p.2 / T.r p.1 p.2) U :=
    continuousOn_const.sub hRatio
  have hDenNe : ∀ p ∈ U,
      (1 - 2 * T.m p.1 p.2 / T.r p.1 p.2) *
        T.r p.1 p.2 ≠ 0 := by
    intro p hp
    exact mul_ne_zero
      (ne_of_gt (H.gap_pos p ⟨hp.1.1, hp.2.2.1, hp.2.2.2⟩))
      (hRadiusNe p hp)
  have hMixed : ContinuousOn (fun p : ℝ × ℝ =>
      routeBMixedExpr (fun c => routeBField T c p)) U := by
    change ContinuousOn (fun p : ℝ × ℝ =>
      ((2 * T.m p.1 p.2 / T.r p.1 p.2) *
        T.lam p.1 p.2 * T.nu p.1 p.2) /
        ((1 - 2 * T.m p.1 p.2 / T.r p.1 p.2) *
          T.r p.1 p.2)) U
    exact ((hRatio.mul (hCont .expansion)).mul (hCont .contraction)).div
      (hGap.mul (hCont .radius)) hDenNe
  have hMassOut : ContinuousOn (fun p : ℝ × ℝ =>
      routeBMassOutgoingExpr (fun c => routeBField T c p)) U := by
    change ContinuousOn (fun p : ℝ × ℝ =>
      (1 - 2 * T.m p.1 p.2 / T.r p.1 p.2) *
        T.theta p.1 p.2 ^ 2 / (2 * T.lam p.1 p.2)) U
    exact (hGap.mul (hTheta.pow 2)).div
      (continuousOn_const.mul (hCont .expansion))
      (fun p hp => mul_ne_zero (by norm_num) (ne_of_gt (H.lam_pos p hp.1)))
  have hMassIn : ContinuousOn (fun p : ℝ × ℝ =>
      routeBMassIncomingExpr (fun c => routeBField T c p)) U := by
    change ContinuousOn (fun p : ℝ × ℝ =>
      (1 - 2 * T.m p.1 p.2 / T.r p.1 p.2) *
        T.zeta p.1 p.2 ^ 2 / (2 * T.nu p.1 p.2)) U
    exact (hGap.mul (hZeta.pow 2)).div
      (continuousOn_const.mul (hCont .contraction))
      (fun p hp => mul_ne_zero (by norm_num) (hNuNe p hp))
  have hThetaSource : ContinuousOn (fun p : ℝ × ℝ =>
      routeBThetaIncomingExpr (fun c => routeBField T c p)) U := by
    change ContinuousOn (fun p : ℝ × ℝ =>
      -(T.lam p.1 p.2 / T.r p.1 p.2 * T.zeta p.1 p.2)) U
    exact (((hCont .expansion).div (hCont .radius) hRadiusNe).mul
      hZeta).neg
  have hZetaSource : ContinuousOn (fun p : ℝ × ℝ =>
      routeBZetaOutgoingExpr (fun c => routeBField T c p)) U := by
    change ContinuousOn (fun p : ℝ × ℝ =>
      -(T.nu p.1 p.2 / T.r p.1 p.2 * T.theta p.1 p.2)) U
    exact (((hCont .contraction).div (hCont .radius) hRadiusNe).mul
      hTheta).neg
  have hMixedScalar : ContinuousOn (fun p : ℝ × ℝ =>
      routeBMixedScalarExpr (fun c => routeBField T c p)) U :=
    hMixed.mul (hCont .scalar)
  have hSelect (c : RouteBField) :
      ContDiffOn ℝ 1
        (routeBScalarExpression (routeBSelector c) T) K := hC1 c
  have hPsi : ContDiffOn ℝ 1
      (routeBScalarExpression routeBScalarRadiusExpr T) K :=
    (hC1 .radius).mul (hC1 .scalar)
  have hThetaC1 : ContDiffOn ℝ 1
      (routeBScalarExpression routeBThetaExpr T) K :=
    (hC1.theta_zeta).1
  have hZetaC1 : ContDiffOn ℝ 1
      (routeBScalarExpression routeBZetaExpr T) K :=
    (hC1.theta_zeta).2
  refine {
    radius_out := ?_,
    radius_in := ?_,
    scalar_radius_out := ?_,
    scalar_radius_in := ?_,
    mass_out := ?_,
    mass_in := ?_,
    expansion_in := ?_,
    contraction_out := ?_,
    theta_in := ?_,
    zeta_out := ?_,
    outgoing_in := ?_,
    incoming_out := ?_
  }
  · intro p hp hpD
    exact routeB_axis_vertical_jet_of_slices ha hab (hSelect .radius)
      (hCont .expansion)
      (fun u v hu huv hvb => H.r_v u v ⟨hu.le, huv, hvb⟩) hp hpD
  · intro p hp hpD
    exact routeB_axis_horizontal_jet_of_slices ha hab (hSelect .radius)
      (hCont .contraction)
      (fun u v hu huv hvb => H.r_u u v hu ⟨hu.le, huv, hvb⟩) hp hpD
  · intro p hp hpD
    exact routeB_axis_vertical_jet_of_slices ha hab (hPsi)
      (hCont .outgoing)
      (fun u v hu huv hvb => H.psi_v u v ⟨hu.le, huv, hvb⟩) hp hpD
  · intro p hp hpD
    exact routeB_axis_horizontal_jet_of_slices ha hab (hPsi)
      (hCont .incoming)
      (fun u v hu huv hvb => H.psi_u u v hu ⟨hu.le, huv, hvb⟩) hp hpD
  · intro p hp hpD
    exact routeB_axis_vertical_jet_of_slices ha hab (hSelect .mass)
      (hMassOut)
      (fun u v hu huv hvb => H.m_v u v ⟨hu.le, huv, hvb⟩) hp hpD
  · intro p hp hpD
    exact routeB_axis_horizontal_jet_of_slices ha hab (hSelect .mass)
      (hMassIn)
      (fun u v hu huv hvb => H.m_u u v hu ⟨hu.le, huv, hvb⟩) hp hpD
  · intro p hp hpD
    exact routeB_axis_horizontal_jet_of_slices ha hab (hSelect .expansion)
      (hMixed)
      (fun u v hu huv hvb => H.lam_u u v hu ⟨hu.le, huv, hvb⟩) hp hpD
  · intro p hp hpD
    exact routeB_axis_vertical_jet_of_slices ha hab (hSelect .contraction)
      (hMixed)
      (fun u v hu huv hvb => H.nu_v u v ⟨hu.le, huv, hvb⟩) hp hpD
  · intro p hp hpD
    exact routeB_axis_horizontal_jet_of_slices ha hab (hThetaC1)
      (hThetaSource)
      (fun u v hu huv hvb => H.theta_u u v hu ⟨hu.le, huv, hvb⟩) hp hpD
  · intro p hp hpD
    exact routeB_axis_vertical_jet_of_slices ha hab (hZetaC1)
      (hZetaSource)
      (fun u v hu huv hvb => H.zeta_v u v ⟨hu.le, huv, hvb⟩) hp hpD
  · intro p hp hpD
    exact routeB_axis_horizontal_jet_of_slices ha hab (hSelect .outgoing)
      (hMixedScalar)
      (fun u v hu huv hvb => H.alpha_u u v hu ⟨hu.le, huv, hvb⟩) hp hpD
  · intro p hp hpD
    exact routeB_axis_vertical_jet_of_slices ha hab (hSelect .incoming)
      (hMixedScalar)
      (fun u v hu huv hvb => H.beta_v u v ⟨hu.le, huv, hvb⟩) hp hpD

end ChristodoulouBV.Uniqueness

end
