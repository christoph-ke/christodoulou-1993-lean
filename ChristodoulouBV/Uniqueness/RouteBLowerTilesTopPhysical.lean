module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesPhysicalSeam
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# Physical field matching on the terminal rectangle seam

The seven-state seam result transfers to all seven physical fields,
including the quotient scalar field.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The reconstructed old and lower physical fields have equal values and
full relative first jets on the common horizontal edge of their rectangles. -/
theorem RouteBTerminalBaseJets.physical_fields_eq_lower_strip_on_top
    {a vBar vStar c η b : ℝ} {alpha₀ : ℝ → ℝ} {S : ℝ → Fields}
    {P : OffAxisTerminalC1Packet a vBar vStar S}
    (J : RouteBTerminalBaseJets P)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hc : 0 < c) (hη : 0 < η) (hTop : vStar + η < b)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ t ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge t) (S t) ∧
      (∀ v ∈ Ioo (0 : ℝ) t,
        (S t).r 0 v = v / 2 ∧ (S t).alpha 0 v = alpha₀ v))
    (hfloor : ∀ t ∈ Ioo (0 : ℝ) vStar,
      ∀ u v : ℝ, 0 ≤ u → u < v → v < t → c ≤ (S t).lam u v)
    (Z : ℝ × ℝ → C1Solution.RectangleState)
    (hZ : ContDiffOn ℝ 1 Z
      (Goursat.rectangle 0 a vStar (vStar + η)))
    (hsafe : ∀ p ∈ Goursat.rectangle 0 a vStar (vStar + η),
      C1Solution.IsSafeRectangleState (Z p))
    (hclassical : RouteBClassicalJetOn b
      (Goursat.rectangle 0 a vStar (vStar + η))
      (rectangleStateFields Z))
    (htrace : ∀ u ∈ Icc 0 a,
      Z (u, vStar) = P.state.rectangleState (u, vStar))
    (hinit : ∀ v ∈ Icc vStar (vStar + η),
      (Z (0, v)).1 = (1 / 2, alpha₀ v)) :
    let Kold := Goursat.rectangle 0 a vBar vStar
    let Knew := Goursat.rectangle 0 a vStar (vStar + η)
    RouteBFieldsEqOn
      (rectangleStateFields P.state.rectangleState)
      (rectangleStateFields Z) (Kold ∩ Knew) ∧
    RouteBFieldsJetEqOn
      (rectangleStateFields P.state.rectangleState)
      (rectangleStateFields Z) Kold Knew := by
  dsimp only
  let Kold := Goursat.rectangle 0 a vBar vStar
  let Knew := Goursat.rectangle 0 a vStar (vStar + η)
  have hOldC1 : ContDiffOn ℝ 1 P.state.rectangleState Kold := by
    simpa only [Kold, Goursat.rectangle] using J.state_c1
  have hOldSafe : ∀ p ∈ Kold,
      C1Solution.IsSafeRectangleState (P.state.rectangleState p) := by
    intro p hp
    exact P.safe_on_closed_base ha haBar hBarStar hc hfamily hfloor
      hp.1 hp.2
  have hVal : EqOn P.state.rectangleState Z (Kold ∩ Knew) := by
    intro p hp
    rcases p with ⟨u, v⟩
    have hv : v = vStar := le_antisymm hp.1.2.2 hp.2.2.1
    subst v
    exact (htrace u hp.1.1).symm
  have hJet : EqOn
      (fderivWithin ℝ P.state.rectangleState Kold)
      (fderivWithin ℝ Z Knew) (Kold ∩ Knew) := by
    intro p hp
    rcases p with ⟨u, v⟩
    have hv : v = vStar := le_antisymm hp.1.2.2 hp.2.2.1
    subst v
    have hdiffOldX : DifferentiableWithinAt ℝ
        (fun p => (P.state.rectangleState p).1) Kold (u, vStar) :=
      ((hOldC1.fst.differentiableOn (by norm_num)) (u, vStar) hp.1)
    have hdiffOldY : DifferentiableWithinAt ℝ
        (fun p => (P.state.rectangleState p).2) Kold (u, vStar) :=
      ((hOldC1.snd.differentiableOn (by norm_num)) (u, vStar) hp.1)
    have hdiffNewX : DifferentiableWithinAt ℝ
        (fun p => (Z p).1) Knew (u, vStar) :=
      ((hZ.fst.differentiableOn (by norm_num)) (u, vStar) hp.2)
    have hdiffNewY : DifferentiableWithinAt ℝ
        (fun p => (Z p).2) Knew (u, vStar) :=
      ((hZ.snd.differentiableOn (by norm_num)) (u, vStar) hp.2)
    have hprodOld := hdiffOldX.fderivWithin_prodMk hdiffOldY
      ((C1Solution.uniqueDiffOn_rectangle ha hBarStar) (u, vStar) hp.1)
    have hprodNew := hdiffNewX.fderivWithin_prodMk hdiffNewY
      ((C1Solution.uniqueDiffOn_rectangle ha
        (by linarith only [hη])) (u, vStar) hp.2)
    have hpair := J.full_jets_eq_lower_strip_on_top
      ha haBar hBarStar hc hη hTop hα hfamily hfloor
      Z hZ hsafe hclassical htrace hinit u hp.1.1
    rw [hprodOld, hprodNew]
    exact congrArg₂ ContinuousLinearMap.prod hpair.1 hpair.2
  constructor
  · intro f p hp
    rw [routeBField_rectangleStateFields_eq,
      routeBField_rectangleStateFields_eq]
    exact congrArg (lowerRectangleSelector f) (hVal hp)
  · exact routeBFieldsJetEqOn_rectangleStateFields
      (C1Solution.uniqueDiffOn_rectangle ha hBarStar)
      (C1Solution.uniqueDiffOn_rectangle ha (by linarith only [hη]))
      P.state.rectangleState Z hOldC1 hZ hOldSafe hVal hJet

end ChristodoulouBV.Uniqueness

end
