module

public import ChristodoulouBV.Uniqueness.RouteBGluingFields
public import ChristodoulouBV.Frozen.DevelopmentWithInitialEdge
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Relative first jets of the glued field

The derivative of a glued field on the large closed triangle restricts to
the relative derivative of each piece, even at either seam or the triple
corner. This permits regionwise jet equations to be read as global equations.
-/

public section

open Set Filter
open scoped Topology

namespace ChristodoulouBV.Uniqueness

/-- A relative C¹ derivative on a large set agrees with the derivative of
an equal function on a uniquely differentiable subset. -/
theorem fderivWithin_eq_of_eqOn_subset
    {K S : Set (ℝ × ℝ)} {f g : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f K) (hSK : S ⊆ K)
    (hunique : UniqueDiffOn ℝ S) (heq : EqOn f g S)
    {p : ℝ × ℝ} (hp : p ∈ S) :
    fderivWithin ℝ f K p = fderivWithin ℝ g S p := by
  have hF := (hf.differentiableOn (by norm_num) p (hSK hp)).hasFDerivWithinAt
  have hF' := (hF.mono hSK).congr' (fun x hx => (heq hx).symm) hp
  exact (hF'.fderivWithin (hunique p hp)).symm

/-- A relative C¹ scalar on the enlarged closed triangle has the ordinary
vertical derivative on every point of the open development, including the
initial edge `u = 0`. -/
theorem vertical_hasDerivAt_of_routeB_c1
    {b : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle 0 b))
    {u v : ℝ} (hp : (u, v) ∈ developmentWithInitialEdge b) :
    HasDerivAt (fun t => f (u, t))
      ((fderivWithin ℝ f (closedCoordTriangle 0 b) (u, v)) (0, 1)) v := by
  have hpK : (u, v) ∈ closedCoordTriangle 0 b :=
    ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc u b)
      (closedCoordTriangle 0 b) := by
    intro t ht
    exact ⟨hp.1, ht.1, ht.2⟩
  have hpair : HasDerivAt (fun t : ℝ => (u, t)) (0, 1) v :=
    (hasDerivAt_const v u).prodMk (hasDerivAt_id' v)
  have hFd := (hf.differentiableOn (by norm_num) (u, v) hpK).hasFDerivWithinAt
  have hslice : HasDerivWithinAt (fun t => f (u, t))
      ((fderivWithin ℝ f (closedCoordTriangle 0 b) (u, v)) (0, 1))
      (Icc u b) v := by
    simpa only [Function.comp_def] using
      hFd.comp_hasDerivWithinAt v hpair.hasDerivWithinAt hmap
  exact hslice.hasDerivAt (Icc_mem_nhds hp.2.1 hp.2.2)

/-- A relative C¹ scalar on the enlarged closed triangle has the ordinary
horizontal derivative at each point with positive incoming coordinate. -/
theorem horizontal_hasDerivAt_of_routeB_c1
    {b : ℝ} {f : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (closedCoordTriangle 0 b))
    {u v : ℝ} (hu : 0 < u)
    (hp : (u, v) ∈ developmentWithInitialEdge b) :
    HasDerivAt (fun t => f (t, v))
      ((fderivWithin ℝ f (closedCoordTriangle 0 b) (u, v)) (1, 0)) u := by
  have hpK : (u, v) ∈ closedCoordTriangle 0 b :=
    ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
  have hmap : MapsTo (fun t : ℝ => (t, v)) (Icc 0 v)
      (closedCoordTriangle 0 b) := by
    intro t ht
    exact ⟨ht.1, ht.2, hp.2.2.le⟩
  have hpair : HasDerivAt (fun t : ℝ => (t, v)) (1, 0) u :=
    (hasDerivAt_id' u).prodMk (hasDerivAt_const u v)
  have hFd := (hf.differentiableOn (by norm_num) (u, v) hpK).hasFDerivWithinAt
  have hslice : HasDerivWithinAt (fun t => f (t, v))
      ((fderivWithin ℝ f (closedCoordTriangle 0 b) (u, v)) (1, 0))
      (Icc 0 v) u := by
    simpa only [Function.comp_def] using
      hFd.comp_hasDerivWithinAt u hpair.hasDerivWithinAt hmap
  exact hslice.hasDerivAt (Icc_mem_nhds hu hp.2.1)

/-- On every Route B piece, every global first jet is exactly its piece's
relative first jet. The three pairwise seam equalities are already consumed
by the existence theorem producing the glued C¹ state. -/
theorem routeB_glued_jets_eq_piece_jets
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar) (hStarb : vStar < b)
    (SOld SLow SAx T : Fields)
    (hT : RouteBFieldsC1On T (closedCoordTriangle 0 b))
    (hOld : RouteBFieldsEqOn T SOld (closedCoordTriangle 0 vStar))
    (hLow : RouteBFieldsEqOn T SLow (routeBLowerRegion a vStar b))
    (hAx : RouteBFieldsEqOn T SAx (closedCoordTriangle a b)) :
    (∀ c : RouteBField, ∀ p ∈ closedCoordTriangle 0 vStar,
      fderivWithin ℝ (routeBField T c) (closedCoordTriangle 0 b) p =
        fderivWithin ℝ (routeBField SOld c)
          (closedCoordTriangle 0 vStar) p) ∧
    (∀ c : RouteBField, ∀ p ∈ routeBLowerRegion a vStar b,
      fderivWithin ℝ (routeBField T c) (closedCoordTriangle 0 b) p =
        fderivWithin ℝ (routeBField SLow c)
          (routeBLowerRegion a vStar b) p) ∧
    (∀ c : RouteBField, ∀ p ∈ closedCoordTriangle a b,
      fderivWithin ℝ (routeBField T c) (closedCoordTriangle 0 b) p =
        fderivWithin ℝ (routeBField SAx c)
          (closedCoordTriangle a b) p) := by
  have hOldSub : closedCoordTriangle 0 vStar ⊆ closedCoordTriangle 0 b := by
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.trans hStarb.le⟩
  have hLowSub : routeBLowerRegion a vStar b ⊆ closedCoordTriangle 0 b := by
    intro p hp
    exact ⟨hp.1.1, hp.1.2.trans (haStar.le.trans hp.2.1), hp.2.2⟩
  have hAxSub : closedCoordTriangle a b ⊆ closedCoordTriangle 0 b := by
    intro p hp
    exact ⟨ha.le.trans hp.1, hp.2.1, hp.2.2⟩
  have hOldUnique : UniqueDiffOn ℝ (closedCoordTriangle 0 vStar) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle 0 vStar) (by
      rw [interior_closedCoordTriangle]
      exact openCoordTriangle_nonempty (ha.trans haStar))
  have hLowUnique : UniqueDiffOn ℝ (routeBLowerRegion a vStar b) :=
    uniqueDiffOn_convex (routeBLowerRegion_closed_convex a vStar b).2
      (routeBLowerRegion_interior_nonempty ha hStarb)
  have hAxUnique : UniqueDiffOn ℝ (closedCoordTriangle a b) :=
    uniqueDiffOn_convex (convex_closedCoordTriangle a b) (by
      rw [interior_closedCoordTriangle]
      exact openCoordTriangle_nonempty (haStar.trans hStarb))
  refine ⟨?_, ?_, ?_⟩
  · intro c p hp
    exact fderivWithin_eq_of_eqOn_subset (hT c)
      hOldSub hOldUnique (hOld c) hp
  · intro c p hp
    exact fderivWithin_eq_of_eqOn_subset (hT c)
      hLowSub hLowUnique (hLow c) hp
  · intro c p hp
    exact fderivWithin_eq_of_eqOn_subset (hT c)
      hAxSub hAxUnique (hAx c) hp

/-- Any pointwise first-order equation for one of the seven fields passes
from the three pieces to the glued field, including at both seams. The
right-hand side is an arbitrary expression in the seven field values, so
this one lemma covers the algebraic forms of the classical equations. -/
theorem routeB_glued_component_jet_equation
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar) (hStarb : vStar < b)
    (SOld SLow SAx T : Fields)
    (hT : RouteBFieldsC1On T (closedCoordTriangle 0 b))
    (hOld : RouteBFieldsEqOn T SOld (closedCoordTriangle 0 vStar))
    (hLow : RouteBFieldsEqOn T SLow (routeBLowerRegion a vStar b))
    (hAx : RouteBFieldsEqOn T SAx (closedCoordTriangle a b))
    (c : RouteBField) (direction : ℝ × ℝ)
    (rhs : (RouteBField → ℝ) → ℝ)
    (hOldEq : ∀ p ∈ closedCoordTriangle 0 vStar,
      p ∈ developmentWithInitialEdge b →
      (fderivWithin ℝ (routeBField SOld c)
        (closedCoordTriangle 0 vStar) p) direction =
        rhs (fun d => routeBField SOld d p))
    (hLowEq : ∀ p ∈ routeBLowerRegion a vStar b,
      p ∈ developmentWithInitialEdge b →
      (fderivWithin ℝ (routeBField SLow c)
        (routeBLowerRegion a vStar b) p) direction =
        rhs (fun d => routeBField SLow d p))
    (hAxEq : ∀ p ∈ closedCoordTriangle a b,
      p ∈ developmentWithInitialEdge b →
      (fderivWithin ℝ (routeBField SAx c)
        (closedCoordTriangle a b) p) direction =
        rhs (fun d => routeBField SAx d p)) :
    ∀ p ∈ developmentWithInitialEdge b,
      (fderivWithin ℝ (routeBField T c) (closedCoordTriangle 0 b) p)
        direction = rhs (fun d => routeBField T d p) := by
  have hJ := routeB_glued_jets_eq_piece_jets ha haStar hStarb
    SOld SLow SAx T hT hOld hLow hAx
  have hcover := routeB_three_region_cover ha.le haStar.le hStarb.le
  intro p hpU
  have hpK : p ∈ closedCoordTriangle 0 b :=
    ⟨hpU.1, hpU.2.1.le, hpU.2.2.le⟩
  have hpiece : p ∈ closedCoordTriangle 0 vStar ∨
      p ∈ routeBLowerRegion a vStar b ∨
        p ∈ closedCoordTriangle a b := by
    have h := hcover.symm ▸ hpK
    rcases h with (hOld' | hLow') | hAx'
    · exact Or.inl hOld'
    · exact Or.inr (Or.inl hLow')
    · exact Or.inr (Or.inr hAx')
  rcases hpiece with hpOld | hpLow | hpAx
  · rw [hJ.1 c p hpOld, hOldEq p hpOld hpU]
    have hval : (fun d => routeBField SOld d p) =
        (fun d => routeBField T d p) := by
      funext d
      exact (hOld d hpOld).symm
    exact congrArg rhs hval
  · rw [hJ.2.1 c p hpLow, hLowEq p hpLow hpU]
    have hval : (fun d => routeBField SLow d p) =
        (fun d => routeBField T d p) := by
      funext d
      exact (hLow d hpLow).symm
    exact congrArg rhs hval
  · rw [hJ.2.2 c p hpAx, hAxEq p hpAx hpU]
    have hval : (fun d => routeBField SAx d p) =
        (fun d => routeBField T d p) := by
      funext d
      exact (hAx d hpAx).symm
    exact congrArg rhs hval

end ChristodoulouBV.Uniqueness

end
