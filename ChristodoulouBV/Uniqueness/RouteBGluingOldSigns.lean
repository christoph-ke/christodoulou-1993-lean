module

public import ChristodoulouBV.Uniqueness.RouteBGluingOldMatch
public import ChristodoulouBV.Uniqueness.RouteBGluingOldTopSigns
import ChristodoulouBV.C1Solution.Extraction
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic

/-!
# Physical signs on the closed old piece

The finite old family supplies the signs below `vBar`; the terminal trace data
supply them on the closed upper rectangle.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- Finite-cutoff matching and the terminal trace data yield the expansion and
physical signs required by the corrected three-region gluing theorem. -/
theorem OffAxisTerminalC1Packet.closed_old_signs_of_match
    {alpha₀ : ℝ → ℝ} {a vBar vStar b u₀ ε : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (_hStarb : vStar < b)
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
    {SOld : Fields}
    (hMatch : ∀ e ∈ Ioo a vStar, ∀ d ∈ Ioo e vStar,
      RouteBFieldsEqOn SOld (routeBCanonicalOldFields d (S d))
        (routeBOldRegion a e))
    (hTop : RouteBFieldsEqOn SOld P.terminalFields
      (routeBLowerRegion a vBar vStar)) :
    (∀ p ∈ routeBOldRegion a vStar, 0 < SOld.lam p.1 p.2) ∧
      (∀ p ∈ routeBOldRegion a vStar,
        p ∈ developmentWithInitialEdge b →
        0 < SOld.r p.1 p.2 ∧ SOld.nu p.1 p.2 < 0 ∧
          0 < 1 - 2 * SOld.m p.1 p.2 / SOld.r p.1 p.2) := by
  let d := (vBar + vStar) / 2
  have hd : d ∈ Ioo vBar vStar := by
    dsimp [d]
    constructor <;> linarith only [hBarStar]
  have hd₀ : d ∈ Ioo (0 : ℝ) vStar :=
    ⟨ha.trans (haBar.trans hd.1), hd.2⟩
  let H := (hfamily d hd₀).1
  obtain ⟨c, hc, hlam⟩ :=
    C1Solution.exists_lam_lower_bound (ha.trans haBar) hd.1 H
  have hTopSigns := P.terminalFields_signs ha haBar hBarStar
    hu₀ hα hfamily hε htail
  have hBottomData (p : ℝ × ℝ)
      (hp : p ∈ routeBOldRegion a vStar) (hv : p.2 ≤ vBar) :
      p ∈ routeBOldRegion a vBar ∧ p ∈ closedCoordTriangle 0 vBar := by
    obtain ⟨hu0, hua, huv, _⟩ := mem_routeBOldRegion.mp hp
    exact ⟨mem_routeBOldRegion.mpr ⟨hu0, hua, huv, hv⟩,
      ⟨hu0, huv, hv⟩⟩
  have hTopData (p : ℝ × ℝ)
      (hp : p ∈ routeBOldRegion a vStar) (hv : vBar ≤ p.2) :
      p ∈ routeBLowerRegion a vBar vStar := by
    obtain ⟨hu0, hua, _, hvStar⟩ := mem_routeBOldRegion.mp hp
    exact ⟨⟨hu0, hua⟩, ⟨hv, hvStar⟩⟩
  constructor
  · intro p hp
    by_cases hv : p.2 ≤ vBar
    · obtain ⟨hpB, hpTri⟩ := hBottomData p hp hv
      have hEq := hMatch vBar ⟨haBar, hBarStar⟩ d hd .expansion hpB
      change SOld.lam p.1 p.2 = (S d).lam p.1 p.2 at hEq
      rw [hEq]
      exact hc.trans_le (hlam p hpTri)
    · have hpT := hTopData p hp (le_of_not_ge hv)
      have hEq := hTop .expansion hpT
      change SOld.lam p.1 p.2 = P.terminalFields.lam p.1 p.2 at hEq
      rw [hEq]
      exact (hTopSigns p hpT).2.1
  · intro p hp hpDev
    by_cases hv : p.2 ≤ vBar
    · obtain ⟨hpB, _⟩ := hBottomData p hp hv
      have hpD : p ∈ developmentWithInitialEdge d :=
        ⟨hpDev.1, hpDev.2.1, hv.trans_lt hd.1⟩
      have hEqR := hMatch vBar ⟨haBar, hBarStar⟩ d hd .radius hpB
      have hEqM := hMatch vBar ⟨haBar, hBarStar⟩ d hd .mass hpB
      have hEqN := hMatch vBar ⟨haBar, hBarStar⟩ d hd .contraction hpB
      change SOld.r p.1 p.2 = C1Solution.canonicalRadius (S d) p at hEqR
      change SOld.m p.1 p.2 = C1Solution.canonicalMass d (S d) p at hEqM
      change SOld.nu p.1 p.2 = (S d).nu p.1 p.2 at hEqN
      rw [C1Solution.canonicalRadius_eq_radius (ha.trans haBar)
        hd.1 H hpDev.1 hpDev.2.1 hv] at hEqR
      rw [C1Solution.canonicalMass_eq_mass hpD] at hEqM
      have hr : 0 < (S d).r p.1 p.2 := H.solution.radius_pos p hpD
      have hn : (S d).nu p.1 p.2 < 0 :=
        C1Solution.nu_neg (ha.trans haBar) hd.1 H
          hpDev.1 hpDev.2.1 hv
      have hgapDiff : 0 < (S d).r p.1 p.2 - 2 * (S d).m p.1 p.2 :=
        C1Solution.mass_gap_pos (ha.trans haBar) hd.1 H
          hpDev.1 hpDev.2.1 hv
      have hgap : 0 < 1 - 2 * (S d).m p.1 p.2 /
          (S d).r p.1 p.2 := by
        have hdiv := div_pos hgapDiff hr
        have hrne : (S d).r p.1 p.2 ≠ 0 := ne_of_gt hr
        have heq : 1 - 2 * (S d).m p.1 p.2 / (S d).r p.1 p.2 =
            ((S d).r p.1 p.2 - 2 * (S d).m p.1 p.2) /
              (S d).r p.1 p.2 := by
          calc
            1 - 2 * (S d).m p.1 p.2 / (S d).r p.1 p.2 =
                (S d).r p.1 p.2 / (S d).r p.1 p.2 -
                  2 * (S d).m p.1 p.2 / (S d).r p.1 p.2 := by
              rw [div_self hrne]
            _ = ((S d).r p.1 p.2 - 2 * (S d).m p.1 p.2) /
                (S d).r p.1 p.2 := by rw [sub_div]
        rw [heq]
        exact hdiv
      rw [hEqR, hEqM, hEqN]
      exact ⟨hr, hn, hgap⟩
    · have hpT := hTopData p hp (le_of_not_ge hv)
      have hEqR := hTop .radius hpT
      have hEqM := hTop .mass hpT
      have hEqN := hTop .contraction hpT
      change SOld.r p.1 p.2 = P.terminalFields.r p.1 p.2 at hEqR
      change SOld.m p.1 p.2 = P.terminalFields.m p.1 p.2 at hEqM
      change SOld.nu p.1 p.2 = P.terminalFields.nu p.1 p.2 at hEqN
      rw [hEqR, hEqM, hEqN]
      exact ⟨(hTopSigns p hpT).1,
        (hTopSigns p hpT).2.2.1, (hTopSigns p hpT).2.2.2⟩

end ChristodoulouBV.Uniqueness

end
