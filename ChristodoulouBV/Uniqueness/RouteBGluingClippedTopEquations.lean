module

public import ChristodoulouBV.Uniqueness.RouteBGluingClippedClassicalTransfer
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Closing a classical equation at the old terminal edge

Once a scalar expression is C¹ on the clipped old region and its right-hand
side is continuous where the classical equation is used, equality below
`vStar` extends to the terminal edge by continuity.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A relative first-jet equation on the strict old union extends to
`v = vStar` after the clipped old C¹ representative has been constructed. -/
theorem routeB_clipped_localJetEquation_of_below_top
    {a vStar b : ℝ} (ha : 0 < a) (haStar : a < vStar) (hStarb : vStar < b)
    (S : Fields) (E rhs : (RouteBField → ℝ) → ℝ)
    (direction : ℝ × ℝ)
    (hEC1 : ContDiffOn ℝ 1 (routeBScalarExpression E S)
      (routeBOldRegion a vStar))
    (hRhs : ContinuousOn (fun p : ℝ × ℝ =>
      rhs (fun c => routeBField S c p))
      (routeBOldRegion a vStar ∩ developmentWithInitialEdge b))
    (hBelow : ∀ p ∈ routeBOldRegion a vStar,
      p ∈ developmentWithInitialEdge b → p.2 < vStar →
      (fderivWithin ℝ (routeBScalarExpression E S)
        (routeBOldRegion a vStar) p) direction =
        rhs (fun c => routeBField S c p)) :
    RouteBLocalJetEquation b (routeBOldRegion a vStar) S E rhs direction := by
  let K := routeBOldRegion a vStar
  let L : ℝ × ℝ → ℝ := fun p =>
    (fderivWithin ℝ (routeBScalarExpression E S) K p) direction
  let R : ℝ × ℝ → ℝ := fun p => rhs (fun c => routeBField S c p)
  have hUnique : UniqueDiffOn ℝ K :=
    uniqueDiffOn_convex (routeBOldRegion_closed_convex a vStar).2
      (routeBOldRegion_interior_nonempty ha haStar)
  have hL : ContinuousOn L K :=
    (hEC1.continuousOn_fderivWithin hUnique (by norm_num)).clm_apply
      continuousOn_const
  intro p hp hpD
  by_cases hlt : p.2 < vStar
  · exact hBelow p hp hpD hlt
  have htop : p.2 = vStar := le_antisymm hp.1.2.2 (le_of_not_gt hlt)
  let u := p.1
  let t₀ := (u + vStar) / 2
  have huStar : u < vStar := htop ▸ hpD.2.1
  have hu0 : 0 ≤ u := hp.1.1
  have hua : u ≤ a := hp.2
  have hut₀ : u < t₀ := by dsimp [t₀]; linarith only [huStar]
  have ht₀Star : t₀ < vStar := by dsimp [t₀]; linarith only [huStar]
  let J := Icc t₀ vStar
  have hmapK : MapsTo (fun v : ℝ => (u, v)) J K := by
    intro v hv
    exact mem_routeBOldRegion.mpr
      ⟨hu0, hua, hut₀.le.trans hv.1, hv.2⟩
  have hmapD : MapsTo (fun v : ℝ => (u, v)) J
      (K ∩ developmentWithInitialEdge b) := by
    intro v hv
    exact ⟨hmapK hv, ⟨hu0, hut₀.trans_le hv.1, hv.2.trans_lt hStarb⟩⟩
  have hpair : ContinuousOn (fun v : ℝ => (u, v)) J :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hLJ : ContinuousOn (fun v : ℝ => L (u, v)) J :=
    hL.comp hpair hmapK
  have hRJ : ContinuousOn (fun v : ℝ => R (u, v)) J :=
    hRhs.comp hpair hmapD
  have hEq : EqOn (fun v : ℝ => L (u, v))
      (fun v : ℝ => R (u, v)) (Ico t₀ vStar) := by
    intro v hv
    have hvJ : v ∈ J := ⟨hv.1, hv.2.le⟩
    exact hBelow (u, v) (hmapK hvJ) (hmapD hvJ).2 hv.2
  have hClosed : EqOn (fun v : ℝ => L (u, v))
      (fun v : ℝ => R (u, v)) J :=
    hEq.of_subset_closure hLJ hRJ Ico_subset_Icc_self (by
      rw [closure_Ico ht₀Star.ne])
  have hpEq : p = (u, vStar) := Prod.ext rfl htop
  change L p = R p
  rw [hpEq]
  exact hClosed ⟨ht₀Star.le, le_rfl⟩

end ChristodoulouBV.Uniqueness

end
