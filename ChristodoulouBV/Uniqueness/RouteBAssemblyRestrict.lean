module

public import ChristodoulouBV.Uniqueness.RouteBAssemblyAxis
public import ChristodoulouBV.Uniqueness.RouteBLowerTilesEndpoint
public import ChristodoulouBV.Uniqueness.RouteBGluingClassicalJet
public import ChristodoulouBV.Uniqueness.RouteBGluingJetTransfer
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# Restricting the lower strip after the edge bounds are fixed

The joined edge may need a shorter new interval. Relative first jets on
the shortened rectangle agree with the original relative jets, including
on its new top and at the triple corner.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The shorter lower rectangle is contained in the original rectangle. -/
theorem routeB_lowerRegion_mono_top
    {a vStar b' b : ℝ} (hbb : b' ≤ b) :
    routeBLowerRegion a vStar b' ⊆ routeBLowerRegion a vStar b := by
  intro p hp
  exact ⟨hp.1, ⟨hp.2.1, hp.2.2.trans hbb⟩⟩

/-- The relative first jet of a C¹ lower-strip scalar survives shortening
the strip's upper endpoint. -/
theorem routeB_lower_fderivWithin_eq_on_shorter
    {a vStar b' b : ℝ} (ha : 0 < a) (hStarb' : vStar < b')
    (hbb : b' ≤ b) {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (routeBLowerRegion a vStar b))
    {p : ℝ × ℝ} (hp : p ∈ routeBLowerRegion a vStar b') :
    fderivWithin ℝ f (routeBLowerRegion a vStar b) p =
      fderivWithin ℝ f (routeBLowerRegion a vStar b') p := by
  exact fderivWithin_eq_of_eqOn_subset hf
    (routeB_lowerRegion_mono_top hbb)
    (uniqueDiffOn_convex
      (routeBLowerRegion_closed_convex a vStar b').2
      (routeBLowerRegion_interior_nonempty ha hStarb'))
    (fun _ _ => rfl) hp

/-- One classical equation restricts to a shorter lower rectangle and a
smaller development endpoint. -/
theorem routeB_localJetEquation_mono_lower_top
    {a vStar b' b : ℝ} {S : Fields}
    (ha : 0 < a) (hStarb' : vStar < b') (hbb : b' ≤ b)
    (E rhs : (RouteBField → ℝ) → ℝ) (direction : ℝ × ℝ)
    (hEC1 : ContDiffOn ℝ 1 (routeBScalarExpression E S)
      (routeBLowerRegion a vStar b))
    (hEq : RouteBLocalJetEquation b (routeBLowerRegion a vStar b)
      S E rhs direction) :
    RouteBLocalJetEquation b' (routeBLowerRegion a vStar b')
      S E rhs direction := by
  intro p hp hpDev
  have hpBig := routeB_lowerRegion_mono_top hbb hp
  have hpDevBig : p ∈ developmentWithInitialEdge b :=
    ⟨hpDev.1, hpDev.2.1, hpDev.2.2.trans_le hbb⟩
  rw [← routeB_lower_fderivWithin_eq_on_shorter ha hStarb'
    hbb hEC1 hp]
  exact hEq p hpBig hpDevBig

/-- All twelve lower-strip equations remain valid after shortening its
upper endpoint. -/
theorem RouteBClassicalJetOn.restrict_lower_top
    {a vStar b' b : ℝ} {S : Fields}
    (ha : 0 < a) (hStarb' : vStar < b') (hbb : b' ≤ b)
    (hC1 : RouteBFieldsC1On S (routeBLowerRegion a vStar b))
    (hJet : RouteBClassicalJetOn b
      (routeBLowerRegion a vStar b) S) :
    RouteBClassicalJetOn b'
      (routeBLowerRegion a vStar b') S := by
  let K := routeBLowerRegion a vStar b
  have hSelect (c : RouteBField) :
      ContDiffOn ℝ 1
        (routeBScalarExpression (routeBSelector c) S) K := hC1 c
  have hPsi : ContDiffOn ℝ 1
      (routeBScalarExpression routeBScalarRadiusExpr S) K :=
    (hC1 .radius).mul (hC1 .scalar)
  have hTheta : ContDiffOn ℝ 1
      (routeBScalarExpression routeBThetaExpr S) K :=
    (hC1.theta_zeta).1
  have hZeta : ContDiffOn ℝ 1
      (routeBScalarExpression routeBZetaExpr S) K :=
    (hC1.theta_zeta).2
  refine {
    radius_out := ?_, radius_in := ?_,
    scalar_radius_out := ?_, scalar_radius_in := ?_,
    mass_out := ?_, mass_in := ?_,
    expansion_in := ?_, contraction_out := ?_,
    theta_in := ?_, zeta_out := ?_,
    outgoing_in := ?_, incoming_out := ?_
  }
  · exact routeB_localJetEquation_mono_lower_top ha hStarb' hbb
      _ _ _ (hSelect .radius) hJet.radius_out
  · exact routeB_localJetEquation_mono_lower_top ha hStarb' hbb
      _ _ _ (hSelect .radius) hJet.radius_in
  · exact routeB_localJetEquation_mono_lower_top ha hStarb' hbb
      _ _ _ hPsi hJet.scalar_radius_out
  · exact routeB_localJetEquation_mono_lower_top ha hStarb' hbb
      _ _ _ hPsi hJet.scalar_radius_in
  · exact routeB_localJetEquation_mono_lower_top ha hStarb' hbb
      _ _ _ (hSelect .mass) hJet.mass_out
  · exact routeB_localJetEquation_mono_lower_top ha hStarb' hbb
      _ _ _ (hSelect .mass) hJet.mass_in
  · exact routeB_localJetEquation_mono_lower_top ha hStarb' hbb
      _ _ _ (hSelect .expansion) hJet.expansion_in
  · exact routeB_localJetEquation_mono_lower_top ha hStarb' hbb
      _ _ _ (hSelect .contraction) hJet.contraction_out
  · exact routeB_localJetEquation_mono_lower_top ha hStarb' hbb
      _ _ _ hTheta hJet.theta_in
  · exact routeB_localJetEquation_mono_lower_top ha hStarb' hbb
      _ _ _ hZeta hJet.zeta_out
  · exact routeB_localJetEquation_mono_lower_top ha hStarb' hbb
      _ _ _ (hSelect .outgoing) hJet.outgoing_in
  · exact routeB_localJetEquation_mono_lower_top ha hStarb' hbb
      _ _ _ (hSelect .incoming) hJet.incoming_out

end ChristodoulouBV.Uniqueness

end
