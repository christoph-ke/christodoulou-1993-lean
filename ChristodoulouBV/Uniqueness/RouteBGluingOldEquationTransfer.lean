module

public import ChristodoulouBV.Uniqueness.RouteBGluingOldFiniteEquations
public import ChristodoulouBV.Uniqueness.RouteBGluingClippedTopEquations
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# Transfer of a finite old equation to the terminal edge

Finite canonical members determine the old representative below the terminal
level. Relative C¹ jets restrict uniquely to each clipped finite cutoff;
continuity then closes the equation on the terminal edge.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A local relative-jet equation on every strict canonical old member
passes to the clipped closed old representative, including its top edge. -/
theorem routeB_old_localJetEquation_of_finite_match
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (hStarb : vStar < b)
    {S : ℝ → Fields} {SOld : Fields}
    (hMatch : ∀ e ∈ Ioo a vStar, ∀ d ∈ Ioo e vStar,
      RouteBFieldsEqOn SOld (routeBCanonicalOldFields d (S d))
        (routeBOldRegion a e))
    (E rhs : (RouteBField → ℝ) → ℝ) (direction : ℝ × ℝ)
    (hEC1 : ContDiffOn ℝ 1 (routeBScalarExpression E SOld)
      (routeBOldRegion a vStar))
    (hFC1 : ∀ e ∈ Ioo a vStar, ∀ d ∈ Ioo e vStar,
      ContDiffOn ℝ 1
        (routeBScalarExpression E (routeBCanonicalOldFields d (S d)))
        (closedCoordTriangle 0 e))
    (hFinite : ∀ e ∈ Ioo a vStar, ∀ d ∈ Ioo e vStar,
      RouteBLocalJetEquation b (closedCoordTriangle 0 e)
        (routeBCanonicalOldFields d (S d)) E rhs direction)
    (hRhs : ContinuousOn (fun p : ℝ × ℝ =>
      rhs (fun c => routeBField SOld c p))
      (routeBOldRegion a vStar ∩ developmentWithInitialEdge b)) :
    RouteBLocalJetEquation b (routeBOldRegion a vStar)
      SOld E rhs direction := by
  apply routeB_clipped_localJetEquation_of_below_top
    ha haStar hStarb SOld E rhs direction hEC1 hRhs
  intro p hp hpD hpStar
  let e := (max a p.2 + vStar) / 2
  let d := (e + vStar) / 2
  have hMaxStar : max a p.2 < vStar := max_lt haStar hpStar
  have he : e ∈ Ioo a vStar := by
    dsimp [e]
    constructor
    · have := le_max_left a p.2
      linarith only [this, hMaxStar]
    · linarith only [hMaxStar]
  have hd : d ∈ Ioo e vStar := by
    dsimp [d]
    constructor <;> linarith only [he.2]
  have hpClip : p ∈ routeBOldRegion a e := by
    obtain ⟨hu0, hua, huv, _⟩ := mem_routeBOldRegion.mp hp
    apply mem_routeBOldRegion.mpr
    refine ⟨hu0, hua, huv, ?_⟩
    dsimp [e]
    have := le_max_right a p.2
    linarith only [this, hMaxStar]
  have hSub : routeBOldRegion a e ⊆ routeBOldRegion a vStar := by
    intro q hq
    obtain ⟨hu0, hua, huv, hqe⟩ := mem_routeBOldRegion.mp hq
    exact mem_routeBOldRegion.mpr ⟨hu0, hua, huv, hqe.trans he.2.le⟩
  have hClipTri : routeBOldRegion a e ⊆ closedCoordTriangle 0 e :=
    fun _ hq => hq.1
  have hUnique : UniqueDiffOn ℝ (routeBOldRegion a e) :=
    uniqueDiffOn_convex (routeBOldRegion_closed_convex a e).2
      (routeBOldRegion_interior_nonempty ha he.1)
  let F := routeBCanonicalOldFields d (S d)
  have hEq : EqOn (routeBScalarExpression E SOld)
      (routeBScalarExpression E F) (routeBOldRegion a e) := by
    intro q hq
    change E (fun c => routeBField SOld c q) =
      E (fun c => routeBField F c q)
    congr 1
    funext c
    exact hMatch e he d hd c hq
  have hOldJet := fderivWithin_eq_of_eqOn_subset hEC1 hSub hUnique
    hEq hpClip
  have hFiniteJet := fderivWithin_eq_of_eqOn_subset
    (hFC1 e he d hd) hClipTri hUnique (fun _ _ => rfl) hpClip
  have hpTri : p ∈ closedCoordTriangle 0 e := hClipTri hpClip
  change (fderivWithin ℝ (routeBScalarExpression E SOld)
      (routeBOldRegion a vStar) p) direction =
    rhs (fun c => routeBField SOld c p)
  rw [hOldJet, ← hFiniteJet, hFinite e he d hd p hpTri hpD]
  congr 1
  funext c
  exact (hMatch e he d hd c hpClip).symm

end ChristodoulouBV.Uniqueness

end
