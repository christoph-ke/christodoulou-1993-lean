module

public import ChristodoulouBV.Uniqueness.RouteBGluingOldFiniteMatch
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# Finite-cutoff identification of the closed old piece

The lower part is independent of which finite old member is chosen. The
upper part is the terminal trace construction, which matches each member that covers a
point below the terminal level.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The constructed closed old representative matches every canonical old
member on every strict clipped cutoff. This is the input needed by the
proved old/axis identification seam theorem. -/
theorem OffAxisTerminalC1Packet.exists_routeB_closed_old_fields_with_match
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (J : RouteBTerminalBaseJets P)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ d ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge d) (S d) ∧
      (∀ v ∈ Ioo (0 : ℝ) d,
        (S d).r 0 v = v / 2 ∧ (S d).alpha 0 v = alpha₀ v)) :
    ∃ SOld : Fields,
      RouteBFieldsC1On SOld (routeBOldRegion a vStar) ∧
      (∀ e ∈ Ioo a vStar, ∀ d ∈ Ioo e vStar,
        RouteBFieldsEqOn SOld (routeBCanonicalOldFields d (S d))
          (routeBOldRegion a e)) ∧
      RouteBFieldsEqOn SOld P.terminalFields
        (routeBLowerRegion a vBar vStar) := by
  obtain ⟨d₀, hd₀, SOld, hC1, hBottom, hTop⟩ :=
    P.exists_routeB_closed_old_fields_c1 J ha haBar hBarStar hfamily
  have hd₀' : d₀ ∈ Ioo (0 : ℝ) vStar :=
    ⟨ha.trans (haBar.trans hd₀.1), hd₀.2⟩
  refine ⟨SOld, hC1, ?_, hTop⟩
  intro e he d hd c p hp
  obtain ⟨hu0, hua, huv, hve⟩ := mem_routeBOldRegion.mp hp
  have hd' : d ∈ Ioo (0 : ℝ) vStar :=
    ⟨ha.trans (he.1.trans hd.1), hd.2⟩
  by_cases hvBar : p.2 ≤ vBar
  · have hpBottom : p ∈ routeBOldRegion a vBar :=
      mem_routeBOldRegion.mpr ⟨hu0, hua, huv, hvBar⟩
    let B := (p.2 + min d₀ d) / 2
    have hvD₀ : p.2 < d₀ := hvBar.trans_lt hd₀.1
    have hvD : p.2 < d := hve.trans_lt hd.1
    have hvMin : p.2 < min d₀ d := lt_min hvD₀ hvD
    have hvB : p.2 ≤ B := by dsimp [B]; linarith only [hvMin]
    have hBMin : B < min d₀ d := by dsimp [B]; linarith only [hvMin]
    have hB : 0 < B := by
      dsimp [B]
      have hv0 : 0 ≤ p.2 := hu0.trans huv
      linarith only [hv0, hvMin]
    have hd₀B : d₀ ∈ Ioo B vStar :=
      ⟨hBMin.trans_le (min_le_left _ _), hd₀.2⟩
    have hdB : d ∈ Ioo B vStar :=
      ⟨hBMin.trans_le (min_le_right _ _), hd.2⟩
    have hpB : p ∈ closedCoordTriangle 0 B := ⟨hu0, huv, hvB⟩
    exact (hBottom c hpBottom).trans
      (routeBCanonicalOldFields_eq_on_closed_triangle
        hB hd₀B hdB hfamily c hpB)
  · have hvBar' : vBar ≤ p.2 := (lt_of_not_ge hvBar).le
    have hpTop : p ∈ routeBLowerRegion a vBar vStar :=
      ⟨⟨hu0, hua⟩, ⟨hvBar', hve.trans he.2.le⟩⟩
    have hpD : p ∈ Icc 0 a ×ˢ Ico vBar d :=
      ⟨⟨hu0, hua⟩, ⟨hvBar', hve.trans_lt hd.1⟩⟩
    exact (hTop c hpTop).trans
      (P.terminalFields_eq_canonical_old ha haBar hd'
        (hfamily d hd').1 hpD c)

/-- Finite-cutoff matching fixes the canonical zero radius and mass on the
entire axis segment of the closed old piece. -/
theorem routeB_old_axis_of_finite_match
    {a vStar : ℝ} {S : ℝ → Fields} {SOld : Fields}
    (_ha : 0 < a) (haStar : a < vStar)
    (hMatch : ∀ e ∈ Ioo a vStar, ∀ d ∈ Ioo e vStar,
      RouteBFieldsEqOn SOld (routeBCanonicalOldFields d (S d))
        (routeBOldRegion a e)) :
    ∀ u ∈ Icc (0 : ℝ) a, SOld.r u u = 0 ∧ SOld.m u u = 0 := by
  let e := (a + vStar) / 2
  let d := (e + vStar) / 2
  have he : e ∈ Ioo a vStar := by
    dsimp [e]
    constructor <;> linarith only [haStar]
  have hd : d ∈ Ioo e vStar := by
    dsimp [d]
    constructor <;> linarith only [he.2]
  intro u hu
  have hp : (u, u) ∈ routeBOldRegion a e :=
    mem_routeBOldRegion.mpr
      ⟨hu.1, hu.2, le_rfl, hu.2.trans he.1.le⟩
  have hr := hMatch e he d hd .radius hp
  have hm := hMatch e he d hd .mass hp
  exact ⟨hr.trans (C1Solution.canonical_outgoing_axis (S d) u).1,
    hm.trans (C1Solution.canonicalMass_axis d (S d) u)⟩

end ChristodoulouBV.Uniqueness

end
