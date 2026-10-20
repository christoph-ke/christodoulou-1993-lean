module

public import ChristodoulouBV.Uniqueness.RouteBGluingOldEquationTransfer
import Mathlib.Tactic

/-!
# Classical equations on the closed old Route B piece

The finite canonical family determines every equation below the terminal
level. The old piece is C¹ on its whole closed region, and its physical
signs make each rational source continuous there off the axis. The
equations therefore extend to the terminal edge.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Finite-cutoff matching and the closed old physical signs imply all
twelve classical relative-jet equations on the clipped old region. -/
theorem routeB_closed_old_classicalJetOn
    {alpha₀ : ℝ → ℝ} {a vStar b : ℝ} {S : ℝ → Fields}
    (ha : 0 < a) (haStar : a < vStar) (hStarb : vStar < b)
    (hfamily : ∀ d ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge d) (S d) ∧
      (∀ v ∈ Ioo (0 : ℝ) d,
        (S d).r 0 v = v / 2 ∧ (S d).alpha 0 v = alpha₀ v))
    {SOld : Fields}
    (hC1 : RouteBFieldsC1On SOld (routeBOldRegion a vStar))
    (hMatch : ∀ e ∈ Ioo a vStar, ∀ d ∈ Ioo e vStar,
      RouteBFieldsEqOn SOld (routeBCanonicalOldFields d (S d))
        (routeBOldRegion a e))
    (hLam : ∀ p ∈ routeBOldRegion a vStar,
      0 < SOld.lam p.1 p.2)
    (hSigns : ∀ p ∈ routeBOldRegion a vStar,
      p ∈ developmentWithInitialEdge b →
      0 < SOld.r p.1 p.2 ∧ SOld.nu p.1 p.2 < 0 ∧
        0 < 1 - 2 * SOld.m p.1 p.2 / SOld.r p.1 p.2) :
    RouteBClassicalJetOn b (routeBOldRegion a vStar) SOld := by
  let K := routeBOldRegion a vStar
  let U := K ∩ developmentWithInitialEdge b
  have hUSub : U ⊆ K := fun _ hp => hp.1
  have hCont (c : RouteBField) :
      ContinuousOn (fun p => routeBField SOld c p) U :=
    (hC1 c).continuousOn.mono hUSub
  have hTheta : ContinuousOn (fun p : ℝ × ℝ => SOld.theta p.1 p.2) U :=
    (hC1.theta_zeta).1.continuousOn.mono hUSub
  have hZeta : ContinuousOn (fun p : ℝ × ℝ => SOld.zeta p.1 p.2) U :=
    (hC1.theta_zeta).2.continuousOn.mono hUSub
  have hRadiusNe : ∀ p ∈ U, SOld.r p.1 p.2 ≠ 0 :=
    fun p hp => ne_of_gt (hSigns p hp.1 hp.2).1
  have hNuNe : ∀ p ∈ U, SOld.nu p.1 p.2 ≠ 0 :=
    fun p hp => ne_of_lt (hSigns p hp.1 hp.2).2.1
  have hRatio : ContinuousOn (fun p : ℝ × ℝ =>
      2 * SOld.m p.1 p.2 / SOld.r p.1 p.2) U :=
    (continuousOn_const.mul (hCont .mass)).div
      (hCont .radius) hRadiusNe
  have hGap : ContinuousOn (fun p : ℝ × ℝ =>
      1 - 2 * SOld.m p.1 p.2 / SOld.r p.1 p.2) U :=
    continuousOn_const.sub hRatio
  have hDenNe : ∀ p ∈ U,
      (1 - 2 * SOld.m p.1 p.2 / SOld.r p.1 p.2) *
        SOld.r p.1 p.2 ≠ 0 := by
    intro p hp
    exact mul_ne_zero (ne_of_gt (hSigns p hp.1 hp.2).2.2)
      (hRadiusNe p hp)
  have hMixed : ContinuousOn (fun p : ℝ × ℝ =>
      routeBMixedExpr (fun c => routeBField SOld c p)) U := by
    change ContinuousOn (fun p : ℝ × ℝ =>
      ((2 * SOld.m p.1 p.2 / SOld.r p.1 p.2) *
        SOld.lam p.1 p.2 * SOld.nu p.1 p.2) /
        ((1 - 2 * SOld.m p.1 p.2 / SOld.r p.1 p.2) *
          SOld.r p.1 p.2)) U
    exact ((hRatio.mul (hCont .expansion)).mul (hCont .contraction)).div
      (hGap.mul (hCont .radius)) hDenNe
  have hMassOut : ContinuousOn (fun p : ℝ × ℝ =>
      routeBMassOutgoingExpr (fun c => routeBField SOld c p)) U := by
    change ContinuousOn (fun p : ℝ × ℝ =>
      (1 - 2 * SOld.m p.1 p.2 / SOld.r p.1 p.2) *
        SOld.theta p.1 p.2 ^ 2 / (2 * SOld.lam p.1 p.2)) U
    exact (hGap.mul (hTheta.pow 2)).div
      (continuousOn_const.mul (hCont .expansion))
      (fun p hp => mul_ne_zero (by norm_num) (ne_of_gt (hLam p hp.1)))
  have hMassIn : ContinuousOn (fun p : ℝ × ℝ =>
      routeBMassIncomingExpr (fun c => routeBField SOld c p)) U := by
    change ContinuousOn (fun p : ℝ × ℝ =>
      (1 - 2 * SOld.m p.1 p.2 / SOld.r p.1 p.2) *
        SOld.zeta p.1 p.2 ^ 2 / (2 * SOld.nu p.1 p.2)) U
    exact (hGap.mul (hZeta.pow 2)).div
      (continuousOn_const.mul (hCont .contraction))
      (fun p hp => mul_ne_zero (by norm_num) (hNuNe p hp))
  have hThetaSource : ContinuousOn (fun p : ℝ × ℝ =>
      routeBThetaIncomingExpr (fun c => routeBField SOld c p)) U := by
    change ContinuousOn (fun p : ℝ × ℝ =>
      -(SOld.lam p.1 p.2 / SOld.r p.1 p.2 *
        SOld.zeta p.1 p.2)) U
    exact (((hCont .expansion).div (hCont .radius) hRadiusNe).mul
      hZeta).neg
  have hZetaSource : ContinuousOn (fun p : ℝ × ℝ =>
      routeBZetaOutgoingExpr (fun c => routeBField SOld c p)) U := by
    change ContinuousOn (fun p : ℝ × ℝ =>
      -(SOld.nu p.1 p.2 / SOld.r p.1 p.2 *
        SOld.theta p.1 p.2)) U
    exact (((hCont .contraction).div (hCont .radius) hRadiusNe).mul
      hTheta).neg
  have hMixedScalar : ContinuousOn (fun p : ℝ × ℝ =>
      routeBMixedScalarExpr (fun c => routeBField SOld c p)) U :=
    hMixed.mul (hCont .scalar)
  have hOldSelect (c : RouteBField) :
      ContDiffOn ℝ 1 (routeBScalarExpression (routeBSelector c) SOld) K :=
    hC1 c
  have hOldPsi : ContDiffOn ℝ 1
      (routeBScalarExpression routeBScalarRadiusExpr SOld) K := by
    exact (hC1 .radius).mul (hC1 .scalar)
  have hOldTheta : ContDiffOn ℝ 1
      (routeBScalarExpression routeBThetaExpr SOld) K :=
    (hC1.theta_zeta).1
  have hOldZeta : ContDiffOn ℝ 1
      (routeBScalarExpression routeBZetaExpr SOld) K :=
    (hC1.theta_zeta).2
  have hFinC1 (e : ℝ) (he : e ∈ Ioo a vStar)
      (d : ℝ) (hd : d ∈ Ioo e vStar) :
      RouteBFieldsC1On (routeBCanonicalOldFields d (S d))
        (closedCoordTriangle 0 e) :=
    routeBCanonicalOldFields_c1 (ha.trans he.1) hd.1
      (hfamily d ⟨ha.trans (he.1.trans hd.1), hd.2⟩).1
  have hFinSelect (c : RouteBField) :
      ∀ e ∈ Ioo a vStar, ∀ d ∈ Ioo e vStar,
      ContDiffOn ℝ 1
        (routeBScalarExpression (routeBSelector c)
          (routeBCanonicalOldFields d (S d)))
        (closedCoordTriangle 0 e) := by
    intro e he d hd
    exact hFinC1 e he d hd c
  have hFinPsi :
      ∀ e ∈ Ioo a vStar, ∀ d ∈ Ioo e vStar,
      ContDiffOn ℝ 1
        (routeBScalarExpression routeBScalarRadiusExpr
          (routeBCanonicalOldFields d (S d)))
        (closedCoordTriangle 0 e) := by
    intro e he d hd
    exact (hFinC1 e he d hd .radius).mul (hFinC1 e he d hd .scalar)
  have hFinTheta :
      ∀ e ∈ Ioo a vStar, ∀ d ∈ Ioo e vStar,
      ContDiffOn ℝ 1
        (routeBScalarExpression routeBThetaExpr
          (routeBCanonicalOldFields d (S d)))
        (closedCoordTriangle 0 e) := by
    intro e he d hd
    exact (hFinC1 e he d hd).theta_zeta.1
  have hFinZeta :
      ∀ e ∈ Ioo a vStar, ∀ d ∈ Ioo e vStar,
      ContDiffOn ℝ 1
        (routeBScalarExpression routeBZetaExpr
          (routeBCanonicalOldFields d (S d)))
        (closedCoordTriangle 0 e) := by
    intro e he d hd
    exact (hFinC1 e he d hd).theta_zeta.2
  have hFin (e : ℝ) (he : e ∈ Ioo a vStar)
      (d : ℝ) (hd : d ∈ Ioo e vStar) :
      RouteBClassicalJetOn b (closedCoordTriangle 0 e)
        (routeBCanonicalOldFields d (S d)) :=
    routeBCanonicalOldFields_classicalJetOn (ha.trans he.1) hd.1
      (hfamily d ⟨ha.trans (he.1.trans hd.1), hd.2⟩).1
  have hTransfer (E rhs : (RouteBField → ℝ) → ℝ)
      (direction : ℝ × ℝ)
      (hE : ContDiffOn ℝ 1 (routeBScalarExpression E SOld) K)
      (hFE : ∀ e ∈ Ioo a vStar, ∀ d ∈ Ioo e vStar,
        ContDiffOn ℝ 1
          (routeBScalarExpression E (routeBCanonicalOldFields d (S d)))
          (closedCoordTriangle 0 e))
      (hR : ContinuousOn (fun p : ℝ × ℝ =>
        rhs (fun c => routeBField SOld c p)) U)
      (hEq : ∀ e ∈ Ioo a vStar, ∀ d ∈ Ioo e vStar,
        RouteBLocalJetEquation b (closedCoordTriangle 0 e)
          (routeBCanonicalOldFields d (S d)) E rhs direction) :
      RouteBLocalJetEquation b K SOld E rhs direction :=
    routeB_old_localJetEquation_of_finite_match ha haStar hStarb
      hMatch E rhs direction hE hFE hEq hR
  exact {
    radius_out := hTransfer _ _ _ (hOldSelect .radius)
      (hFinSelect .radius) (hCont .expansion)
      (fun e he d hd => (hFin e he d hd).radius_out)
    radius_in := hTransfer _ _ _ (hOldSelect .radius)
      (hFinSelect .radius) (hCont .contraction)
      (fun e he d hd => (hFin e he d hd).radius_in)
    scalar_radius_out := hTransfer _ _ _ hOldPsi hFinPsi
      (hCont .outgoing)
      (fun e he d hd => (hFin e he d hd).scalar_radius_out)
    scalar_radius_in := hTransfer _ _ _ hOldPsi hFinPsi
      (hCont .incoming)
      (fun e he d hd => (hFin e he d hd).scalar_radius_in)
    mass_out := hTransfer _ _ _ (hOldSelect .mass)
      (hFinSelect .mass) hMassOut
      (fun e he d hd => (hFin e he d hd).mass_out)
    mass_in := hTransfer _ _ _ (hOldSelect .mass)
      (hFinSelect .mass) hMassIn
      (fun e he d hd => (hFin e he d hd).mass_in)
    expansion_in := hTransfer _ _ _ (hOldSelect .expansion)
      (hFinSelect .expansion) hMixed
      (fun e he d hd => (hFin e he d hd).expansion_in)
    contraction_out := hTransfer _ _ _ (hOldSelect .contraction)
      (hFinSelect .contraction) hMixed
      (fun e he d hd => (hFin e he d hd).contraction_out)
    theta_in := hTransfer _ _ _ hOldTheta hFinTheta hThetaSource
      (fun e he d hd => (hFin e he d hd).theta_in)
    zeta_out := hTransfer _ _ _ hOldZeta hFinZeta hZetaSource
      (fun e he d hd => (hFin e he d hd).zeta_out)
    outgoing_in := hTransfer _ _ _ (hOldSelect .outgoing)
      (hFinSelect .outgoing) hMixedScalar
      (fun e he d hd => (hFin e he d hd).outgoing_in)
    incoming_out := hTransfer _ _ _ (hOldSelect .incoming)
      (hFinSelect .incoming) hMixedScalar
      (fun e he d hd => (hFin e he d hd).incoming_out)
  }

end ChristodoulouBV.Uniqueness

end
