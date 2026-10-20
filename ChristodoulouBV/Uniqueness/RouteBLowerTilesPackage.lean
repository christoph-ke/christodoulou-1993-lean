module

public import ChristodoulouBV.Uniqueness.RouteBLowerTilesClippedSeam
public import ChristodoulouBV.Uniqueness.RouteBGluingOldClassical
public import ChristodoulouBV.Uniqueness.RouteBGluingOldSigns
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# Closed old and lower pieces for Route B

The finite tile cover and the canonical closed old representative supply
the two pieces and their complete horizontal seam. The vertical lower/axis
seam is supplied separately.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A safe seven-state lower strip has the field signs required by the
corrected clipped gluing theorem. -/
theorem routeB_lower_fields_signs_of_safe
    {a vStar b : ℝ} {Z : ℝ × ℝ → C1Solution.RectangleState}
    (hsafe : ∀ p ∈ routeBLowerRegion a vStar b,
      C1Solution.IsSafeRectangleState (Z p)) :
    (∀ p ∈ routeBLowerRegion a vStar b,
      0 < (rectangleStateFields Z).lam p.1 p.2) ∧
      (∀ p ∈ routeBLowerRegion a vStar b,
        p ∈ developmentWithInitialEdge b →
        0 < (rectangleStateFields Z).r p.1 p.2 ∧
          (rectangleStateFields Z).nu p.1 p.2 < 0 ∧
          0 < 1 - 2 * (rectangleStateFields Z).m p.1 p.2 /
            (rectangleStateFields Z).r p.1 p.2) := by
  constructor
  · intro p hp
    change 0 < C1Solution.stateLam (Z p)
    exact (hsafe p hp).2.1
  · intro p hp _
    have hz := hsafe p hp
    have hr : 0 < C1Solution.stateRadius (Z p) := hz.1
    have hgap : 0 < C1Solution.stateMassGap (Z p) := hz.2.2.2
    have hratio : 0 < C1Solution.stateMassGap (Z p) /
        C1Solution.stateRadius (Z p) := div_pos hgap hr
    change 0 < C1Solution.stateRadius (Z p) ∧
      C1Solution.stateNu (Z p) < 0 ∧
      0 < 1 - 2 * C1Solution.stateMass (Z p) /
        C1Solution.stateRadius (Z p)
    refine ⟨hr, hz.2.2.1, ?_⟩
    have heq :
        1 - 2 * C1Solution.stateMass (Z p) /
          C1Solution.stateRadius (Z p) =
        C1Solution.stateMassGap (Z p) /
          C1Solution.stateRadius (Z p) := by
      rw [C1Solution.stateMassGap]
      field_simp [ne_of_gt hr]
    rw [heq]
    exact hratio

/-- The frozen family produces a positive-height lower cover and a clipped
old piece whose values and full first jets agree on their common edge.
These are the old/lower inputs to clipped gluing; the lower/axis
vertical seam remains a separate input. -/
theorem exists_routeB_lower_cover
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε a vBar L : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hL : 0 < L)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ d ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge d) (S d) ∧
      (∀ v ∈ Ioo (0 : ℝ) d,
        (S d).r 0 v = v / 2 ∧ (S d).alpha 0 v = alpha₀ v))
    (hε : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ d ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge d,
        2 * (S d).m p.1 p.2 / (S d).r p.1 p.2 ≤ ε) :
    ∃ P : OffAxisTerminalC1Packet a vBar vStar S,
      ∃ _J : RouteBTerminalBaseJets P,
        ∃ η : ℝ, 0 < η ∧ η < L ∧
          ∃ SOld SLow : Fields,
            let b := vStar + η
            RouteBFieldsC1On SOld (routeBOldRegion a vStar) ∧
            RouteBClassicalJetOn b (routeBOldRegion a vStar) SOld ∧
            (∀ e ∈ Ioo a vStar, ∀ d ∈ Ioo e vStar,
              RouteBFieldsEqOn SOld (routeBCanonicalOldFields d (S d))
                (routeBOldRegion a e)) ∧
            RouteBFieldsEqOn SOld P.terminalFields
              (routeBLowerRegion a vBar vStar) ∧
            RouteBFieldsC1On SLow (routeBLowerRegion a vStar b) ∧
            RouteBClassicalJetOn b (routeBLowerRegion a vStar b) SLow ∧
            RouteBFieldsEqOn SOld SLow
              (routeBOldRegion a vStar ∩ routeBLowerRegion a vStar b) ∧
            RouteBFieldsJetEqOn SOld SLow
              (routeBOldRegion a vStar) (routeBLowerRegion a vStar b) ∧
            (∀ T : Fields,
              RouteBFieldsC1On T (routeBOldRegion a vStar) →
              RouteBFieldsEqOn T P.terminalFields
                (routeBLowerRegion a vBar vStar) →
              RouteBFieldsEqOn T SLow
                (routeBOldRegion a vStar ∩ routeBLowerRegion a vStar b) ∧
              RouteBFieldsJetEqOn T SLow
                (routeBOldRegion a vStar)
                (routeBLowerRegion a vStar b)) ∧
            (∀ p ∈ routeBOldRegion a vStar,
              0 < SOld.lam p.1 p.2) ∧
            (∀ p ∈ routeBOldRegion a vStar,
              p ∈ developmentWithInitialEdge b →
              0 < SOld.r p.1 p.2 ∧ SOld.nu p.1 p.2 < 0 ∧
                0 < 1 - 2 * SOld.m p.1 p.2 / SOld.r p.1 p.2) ∧
            (∀ p ∈ routeBLowerRegion a vStar b,
              0 < SLow.lam p.1 p.2) ∧
            (∀ p ∈ routeBLowerRegion a vStar b,
              p ∈ developmentWithInitialEdge b →
              0 < SLow.r p.1 p.2 ∧ SLow.nu p.1 p.2 < 0 ∧
                0 < 1 - 2 * SLow.m p.1 p.2 / SLow.r p.1 p.2) ∧
            (∀ v ∈ Icc vStar b,
              SLow.r 0 v = v / 2 ∧ SLow.alpha 0 v = alpha₀ v) := by
  obtain ⟨P, η, hη, hηL, Z, hZ, hsafe, hLowC1, hLowJet,
    _, hinit, hradius, hBaseLow, hBaseLowJet⟩ :=
    exists_routeB_lower_cover_fields hu₀ ha haBar hBarStar hL
      hα hfamily hε htail
  obtain ⟨J⟩ := P.exists_routeBTerminalBaseJets
    ha haBar hBarStar hu₀ hα hfamily hε htail
  obtain ⟨SOld, hOldC1, hOldMatch, hOldTop⟩ :=
    P.exists_routeB_closed_old_fields_with_match J
      ha haBar hBarStar hfamily
  let b := vStar + η
  have hStarb : vStar < b := by dsimp [b]; linarith only [hη]
  let SLow := rectangleStateFields Z
  have hBaseLow' : RouteBFieldsEqOn
      (rectangleStateFields P.state.rectangleState) SLow
      (routeBLowerRegion a vBar vStar ∩
        routeBLowerRegion a vStar b) := by
    simpa only [Goursat.rectangle, routeBLowerRegion, b, SLow] using hBaseLow
  have hBaseLowJet' : RouteBFieldsJetEqOn
      (rectangleStateFields P.state.rectangleState) SLow
      (routeBLowerRegion a vBar vStar)
      (routeBLowerRegion a vStar b) := by
    simpa only [Goursat.rectangle, routeBLowerRegion, b, SLow] using hBaseLowJet
  have hLowC1' : RouteBFieldsC1On SLow
      (routeBLowerRegion a vStar b) := by
    simpa only [Goursat.rectangle, routeBLowerRegion, b, SLow] using hLowC1
  have hLowJet' : RouteBClassicalJetOn b
      (routeBLowerRegion a vStar b) SLow := by
    simpa only [Goursat.rectangle, routeBLowerRegion, b, SLow] using hLowJet
  have hsafe' : ∀ p ∈ routeBLowerRegion a vStar b,
      C1Solution.IsSafeRectangleState (Z p) := by
    intro p hp
    exact hsafe p (by simpa only [Goursat.rectangle, routeBLowerRegion, b] using hp)
  have hSeam := P.clipped_old_lower_seam
    ha haBar hBarStar hStarb SOld SLow
    hOldC1 hOldTop hBaseLow' hBaseLowJet'
  have hAnySeam : ∀ T : Fields,
      RouteBFieldsC1On T (routeBOldRegion a vStar) →
      RouteBFieldsEqOn T P.terminalFields
        (routeBLowerRegion a vBar vStar) →
      RouteBFieldsEqOn T SLow
        (routeBOldRegion a vStar ∩ routeBLowerRegion a vStar b) ∧
      RouteBFieldsJetEqOn T SLow
        (routeBOldRegion a vStar)
        (routeBLowerRegion a vStar b) := by
    intro T hTC1 hTTop
    exact P.clipped_old_lower_seam
      ha haBar hBarStar hStarb T SLow
      hTC1 hTTop hBaseLow' hBaseLowJet'
  have hOldSigns := P.closed_old_signs_of_match
    ha haBar hBarStar hStarb hu₀ hα hfamily hε htail
    hOldMatch hOldTop
  have hOldJet := routeB_closed_old_classicalJetOn
    ha (haBar.trans hBarStar) hStarb hfamily
    hOldC1 hOldMatch hOldSigns.1 hOldSigns.2
  have hLowSigns := routeB_lower_fields_signs_of_safe
    (a := a) (vStar := vStar) (b := b) (Z := Z) hsafe'
  have hLowGauge : ∀ v ∈ Icc vStar b,
      SLow.r 0 v = v / 2 ∧ SLow.alpha 0 v = alpha₀ v := by
    intro v hv
    constructor
    · change C1Solution.stateRadius (Z (0, v)) = v / 2
      exact hradius v hv
    · change C1Solution.stateAlpha (Z (0, v)) = alpha₀ v
      exact congrArg Prod.snd (hinit v hv)
  exact ⟨P, J, η, hη, hηL, SOld, SLow,
    hOldC1, hOldJet, hOldMatch, hOldTop,
    hLowC1', hLowJet', hSeam.1, hSeam.2, hAnySeam,
    hOldSigns.1, hOldSigns.2, hLowSigns.1,
    hLowSigns.2, hLowGauge⟩

end ChristodoulouBV.Uniqueness

end
