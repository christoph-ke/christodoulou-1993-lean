module

public import ChristodoulouBV.Uniqueness.RouteBAssemblyCutoff
public import ChristodoulouBV.Uniqueness.RouteBLowerTilesPackage

/-!
# The lower Route B piece at a cutoff chosen after the lifetime

The finite lower cover exists for any positive requested height. Once a
uniform axis lifetime is fixed, its request can be set to half that lifetime.
The resulting top is a prescribed axis endpoint beyond `vStar`.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- From the frozen family and tail premises, any positive uniform lifetime
has a lower strip whose top is beyond `vStar` and within that lifetime of
the selected incoming cutoff. The old and lower pieces carry the horizontal
seam, signs, classical jets, and initial data needed for clipped gluing. -/
theorem exists_routeB_lower_cover_inside_lifetime
    {alpha₀ : ℝ → ℝ} {vStar u₀ ε : ℝ} {S : ℝ → Fields}
    (hu₀ : u₀ ∈ Ioo (0 : ℝ) vStar)
    (hα : ContDiffOn ℝ 1 alpha₀ (Ici 0))
    (hfamily : ∀ d ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge d) (S d) ∧
      (∀ v ∈ Ioo (0 : ℝ) d,
        (S d).r 0 v = v / 2 ∧ (S d).alpha 0 v = alpha₀ v))
    (hε : ε < (5 - 2 * Real.sqrt 6) / 3)
    (htail : ∀ d ∈ Ioo (0 : ℝ) vStar,
      ∀ p ∈ openDevelopment u₀ vStar ∩ developmentWithInitialEdge d,
        2 * (S d).m p.1 p.2 / (S d).r p.1 p.2 ≤ ε)
    {T : ℝ} (hT : 0 < T) :
    ∃ a vBar η b : ℝ,
      u₀ < a ∧ a < vBar ∧ vBar < vStar ∧
      0 < η ∧ η < T / 2 ∧
      b = vStar + η ∧ vStar < b ∧ b - a ≤ T ∧
      min (a + T) (vStar + η) = b ∧
      ∃ P : OffAxisTerminalC1Packet a vBar vStar S,
        ∃ _J : RouteBTerminalBaseJets P,
          ∃ SOld SLow : Fields,
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
  obtain ⟨a, vBar, hu₀a, haBar, hBarStar, hgap⟩ :=
    exists_routeB_cutoff_near_terminal hu₀ hT
  have ha : 0 < a := hu₀.1.trans hu₀a
  have hhalf : 0 < T / 2 := by positivity
  obtain ⟨P, J, η, hη, hηhalf, SOld, SLow,
      hOldC1, hOldJet, hOldMatch, hOldTop,
      hLowC1, hLowJet, hOldLow, hOldLowJet, _,
      hOldLam, hOldSigns, hLowLam, hLowSigns, hLowData⟩ :=
    exists_routeB_lower_cover hu₀ ha haBar hBarStar hhalf
      hα hfamily hε htail
  obtain ⟨_, hStarb, hwidth, hmin⟩ :=
    routeB_lower_top_endpoint (haBar.trans hBarStar) hgap hη hηhalf
  refine ⟨a, vBar, η, vStar + η,
    hu₀a, haBar, hBarStar, hη, hηhalf, rfl,
    hStarb, hwidth, hmin, P, J, SOld, SLow,
    hOldC1, hOldJet, hOldMatch, hOldTop,
    hLowC1, hLowJet, hOldLow, hOldLowJet,
    hOldLam, hOldSigns, hLowLam, hLowSigns, hLowData⟩

end ChristodoulouBV.Uniqueness

end
