module

public import ChristodoulouBV.Uniqueness.RouteBAssemblyEdgeBounds
public import ChristodoulouBV.Uniqueness.RouteBAssemblyLower
public import ChristodoulouBV.Uniqueness.RouteBLowerTilesPackage
import Mathlib.Tactic.Linarith

/-!
# Choosing the Route B cutoff after its uniform lifetime

The old-family estimates determine the edge norm and prescribed axis
lifetime before an incoming cutoff is chosen. The lower cover can then be
built at that cutoff with height below half the lifetime.
-/

public section

open Set ChristodoulouBV.AxisPicard

namespace ChristodoulouBV.Uniqueness

/-- The frozen premises select a lower strip whose incoming cutoff lies
within half a uniform axis lifetime of the terminal line. Its compact old
edge obeys bounds independent of that cutoff. The lower piece retains the
universal horizontal seam interface needed for the final gluing. -/
theorem exists_routeB_lower_cover_with_uniform_edge_lifetime
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
        2 * (S d).m p.1 p.2 / (S d).r p.1 p.2 ≤ ε) :
    ∃ c Clam H T a vBar η b : ℝ,
      0 < c ∧ 0 ≤ Clam ∧ 0 ≤ H ∧
      T = uniformAxisLifetime (c / 2) (Clam + 1) (H + 1) ∧
      u₀ < a ∧ a < vBar ∧ vBar < vStar ∧
      vStar - a < T / 2 ∧ 0 < η ∧ η < T / 2 ∧
      b = vStar + η ∧ vStar < b ∧ b - a ≤ T ∧
      ∃ P : OffAxisTerminalC1Packet a vBar vStar S,
        ∃ _J : RouteBTerminalBaseJets P,
          ∃ SOld SLow : Fields,
            (∀ v ∈ Icc a vStar,
              c ≤ intervalC1Extension P.g a vStar v ∧
              |deriv (intervalC1Extension P.g a vStar) v| ≤ Clam ∧
              |intervalC1Extension P.hEdge a vStar v| ≤ H ∧
              |deriv (intervalC1Extension P.hEdge a vStar) v| ≤ H) ∧
            RouteBFieldsC1On SOld (routeBOldRegion a vStar) ∧
            RouteBFieldsEqOn SOld P.terminalFields
              (routeBLowerRegion a vBar vStar) ∧
            RouteBFieldsC1On SLow (routeBLowerRegion a vStar b) ∧
            RouteBClassicalJetOn b (routeBLowerRegion a vStar b) SLow ∧
            RouteBFieldsEqOn SOld SLow
              (routeBOldRegion a vStar ∩ routeBLowerRegion a vStar b) ∧
            RouteBFieldsJetEqOn SOld SLow
              (routeBOldRegion a vStar) (routeBLowerRegion a vStar b) ∧
            (∀ TOld : Fields,
              RouteBFieldsC1On TOld (routeBOldRegion a vStar) →
              RouteBFieldsEqOn TOld P.terminalFields
                (routeBLowerRegion a vBar vStar) →
              RouteBFieldsEqOn TOld SLow
                (routeBOldRegion a vStar ∩ routeBLowerRegion a vStar b) ∧
              RouteBFieldsJetEqOn TOld SLow
                (routeBOldRegion a vStar)
                (routeBLowerRegion a vStar b)) ∧
            (∀ p ∈ routeBLowerRegion a vStar b,
              0 < SLow.lam p.1 p.2) ∧
            (∀ p ∈ routeBLowerRegion a vStar b,
              p ∈ developmentWithInitialEdge b →
              0 < SLow.r p.1 p.2 ∧ SLow.nu p.1 p.2 < 0 ∧
                0 < 1 - 2 * SLow.m p.1 p.2 / SLow.r p.1 p.2) ∧
            (∀ v ∈ Icc vStar b,
              SLow.r 0 v = v / 2 ∧ SLow.alpha 0 v = alpha₀ v) := by
  obtain ⟨c, Clam, H, hc, hClam, hH, hbounds⟩ :=
    exists_uniform_routeB_extended_edge_bounds hu₀ hα hfamily hε htail
  let T := uniformAxisLifetime (c / 2) (Clam + 1) (H + 1)
  have hT : 0 < T := uniformAxisLifetime_pos _ _ _
  obtain ⟨a, vBar, hu₀a, haBar, hBarStar, hgap⟩ :=
    exists_routeB_cutoff_near_terminal hu₀ hT
  have ha : 0 < a := hu₀.1.trans hu₀a
  have hhalf : 0 < T / 2 := half_pos hT
  obtain ⟨P, J, η, hη, hηhalf, SOld, SLow,
      hOldC1, _, _, hOldTop, hLowC1, hLowJet, hOldLow, hOldLowJet, hAnySeam,
      _, _, hLowLam, hLowSigns, hLowData⟩ :=
    exists_routeB_lower_cover hu₀ ha haBar hBarStar hhalf
      hα hfamily hε htail
  obtain ⟨_, hStarb, hwidth, _⟩ :=
    routeB_lower_top_endpoint (haBar.trans hBarStar) hgap hη hηhalf
  refine ⟨c, Clam, H, T, a, vBar, η, vStar + η,
    hc, hClam, hH, rfl, hu₀a, haBar, hBarStar,
    hgap, hη, hηhalf, rfl, hStarb, hwidth,
    P, J, SOld, SLow, hbounds ha haBar hBarStar P,
    hOldC1, hOldTop, hLowC1, hLowJet, hOldLow, hOldLowJet,
    hAnySeam, hLowLam, hLowSigns, hLowData⟩

end ChristodoulouBV.Uniqueness

end
