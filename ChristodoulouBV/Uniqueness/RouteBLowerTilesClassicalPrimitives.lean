module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesTileJet
public import ChristodoulouBV.Uniqueness.RouteBLowerTilesConstraints
public import ChristodoulouBV.Uniqueness.RouteBLowerTilesFields
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# Primitive classical equations on a lower tile

The characteristic equations and propagated incoming constraints give both
coordinate jets of the area radius and scalar radius on the closed tile.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The radius and scalar-radius equations hold as full relative jets on
one constrained safe tile, including all its edges and corners. -/
theorem LowerCoverTile.radius_psi_classical_jets
    {a vStar L u₀ u₁ H b : ℝ} {D : LowerCoverBaseData a vStar L}
    {B : C1Solution.SafeRectangleBox}
    (T : LowerCoverTile D B u₀ u₁ H)
    (hu : u₀ < u₁) (hH : 0 < H)
    (hu₀ : 0 ≤ u₀) (hu₁ : u₁ ≤ a) :
    let K := Goursat.rectangle u₀ u₁ vStar (vStar + H)
    let S := rectangleStateFields fun p => (T.incoming p, T.outgoing p)
    RouteBLocalJetEquation b K S
      (routeBSelector .radius) (routeBSelector .expansion) (0, 1) ∧
    RouteBLocalJetEquation b K S
      (routeBSelector .radius) (routeBSelector .contraction) (1, 0) ∧
    RouteBLocalJetEquation b K S
      routeBScalarRadiusExpr (routeBSelector .outgoing) (0, 1) ∧
    RouteBLocalJetEquation b K S
      routeBScalarRadiusExpr (routeBSelector .incoming) (1, 0) := by
  dsimp only
  let K := Goursat.rectangle u₀ u₁ vStar (vStar + H)
  let Z : ℝ × ℝ → C1Solution.RectangleState :=
    fun p => (T.incoming p, T.outgoing p)
  let S := rectangleStateFields Z
  have hZ : ContDiffOn ℝ 1 Z K :=
    T.incoming_c1.prodMk T.outgoing_c1
  have hsafe : ∀ p ∈ K, C1Solution.IsSafeRectangleState (Z p) := by
    intro p hp
    exact B.safe (T.safe p hp)
  have hS : RouteBFieldsC1On S K :=
    routeBFieldsC1On_rectangleStateFields hZ hsafe
  have hrC1 : ContDiffOn ℝ 1
      (fun p => C1Solution.stateRadius (Z p)) K := hS .radius
  have hψC1 : ContDiffOn ℝ 1
      (fun p => C1Solution.statePsi (Z p)) K := by
    change ContDiffOn ℝ 1 (fun p => (T.outgoing p).2.2.2.2) K
    exact T.outgoing_c1.snd.snd.snd.snd
  have hψeq : EqOn (routeBScalarExpression routeBScalarRadiusExpr S)
      (fun p => C1Solution.statePsi (Z p)) K := by
    intro p hp
    have hr : C1Solution.stateRadius (Z p) ≠ 0 :=
      ne_of_gt (hsafe p hp).1
    change C1Solution.stateRadius (Z p) *
      C1Solution.statePhi (Z p) = C1Solution.statePsi (Z p)
    unfold C1Solution.statePhi
    field_simp [hr]
  have hc := T.incoming_constraints hu hH hu₀ hu₁
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp _
    rcases p with ⟨u, v⟩
    have hp' : (u, v) ∈ Icc u₀ u₁ ×ˢ Icc vStar (vStar + H) := by
      simpa only [Goursat.rectangle] using hp
    have hu' : u ∈ Icc u₀ u₁ := hp'.1
    have hv' : v ∈ Icc vStar (vStar + H) := hp'.2
    have hY := (T.characteristic_jets u hu' v hv').2
    have hrv : HasDerivWithinAt
        (fun t => C1Solution.stateRadius (Z (u, t)))
        (C1Solution.stateLam (Z (u, v)))
        (Icc vStar (vStar + H)) v := by
      convert hY.snd.snd.snd.fst using 1; rfl
    change (fderivWithin ℝ (fun q => C1Solution.stateRadius (Z q))
      K (u, v)) (0, 1) = C1Solution.stateLam (Z (u, v))
    exact vertical_jet_eq_of_slice_derivative hu
      (by linarith only [hH]) hrC1 hu' hv' hrv
  · intro p hp _
    rcases p with ⟨u, v⟩
    have hp' : (u, v) ∈ Icc u₀ u₁ ×ˢ Icc vStar (vStar + H) := by
      simpa only [Goursat.rectangle] using hp
    change (fderivWithin ℝ (fun q => C1Solution.stateRadius (Z q))
      K (u, v)) (1, 0) = C1Solution.stateNu (Z (u, v))
    exact hc.1 u hp'.1 v hp'.2
  · intro p hp _
    rcases p with ⟨u, v⟩
    have hp' : (u, v) ∈ Icc u₀ u₁ ×ˢ Icc vStar (vStar + H) := by
      simpa only [Goursat.rectangle] using hp
    have hu' : u ∈ Icc u₀ u₁ := hp'.1
    have hv' : v ∈ Icc vStar (vStar + H) := hp'.2
    have hY := (T.characteristic_jets u hu' v hv').2
    have hψv : HasDerivWithinAt
        (fun t => C1Solution.statePsi (Z (u, t)))
        (C1Solution.stateAlpha (Z (u, v)))
        (Icc vStar (vStar + H)) v := by
      convert hY.snd.snd.snd.snd using 1; rfl
    change (fderivWithin ℝ
      (routeBScalarExpression routeBScalarRadiusExpr S) K
        (u, v)) (0, 1) = C1Solution.stateAlpha (Z (u, v))
    rw [fderivWithin_congr' hψeq hp]
    exact vertical_jet_eq_of_slice_derivative hu
      (by linarith only [hH]) hψC1 hu' hv' hψv
  · intro p hp _
    rcases p with ⟨u, v⟩
    have hp' : (u, v) ∈ Icc u₀ u₁ ×ˢ Icc vStar (vStar + H) := by
      simpa only [Goursat.rectangle] using hp
    change (fderivWithin ℝ
      (routeBScalarExpression routeBScalarRadiusExpr S) K
        (u, v)) (1, 0) = C1Solution.stateBeta (Z (u, v))
    rw [fderivWithin_congr' hψeq hp]
    exact hc.2.1 u hp'.1 v hp'.2

end ChristodoulouBV.Uniqueness

end
