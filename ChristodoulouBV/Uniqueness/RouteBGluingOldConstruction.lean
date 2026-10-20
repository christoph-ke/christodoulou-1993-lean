module

public import ChristodoulouBV.Uniqueness.RouteBGluingOldTerminal
public import ChristodoulouBV.Uniqueness.RouteBGluingOldSeam
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# The C¹ closed old representative

One old family member supplies the lower clipped triangle. The terminal
base-jet construction supplies the upper rectangle. A shorter common upper
rectangle transfers the complete first jet across their horizontal seam.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The old family and terminal base jets yield one C¹ seven-field state
on the entire closed clipped old region, including its terminal edge. -/
theorem OffAxisTerminalC1Packet.exists_routeB_closed_old_fields_c1
    {alpha₀ : ℝ → ℝ} {a vBar vStar : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (J : RouteBTerminalBaseJets P)
    (ha : 0 < a) (haBar : a < vBar) (hBarStar : vBar < vStar)
    (hfamily : ∀ d ∈ Ioo (0 : ℝ) vStar,
      IsC1Solution (developmentWithInitialEdge d) (S d) ∧
      (∀ v ∈ Ioo (0 : ℝ) d,
        (S d).r 0 v = v / 2 ∧ (S d).alpha 0 v = alpha₀ v)) :
    ∃ d ∈ Ioo vBar vStar, ∃ SOld : Fields,
      RouteBFieldsC1On SOld (routeBOldRegion a vStar) ∧
      RouteBFieldsEqOn SOld (routeBCanonicalOldFields d (S d))
        (routeBOldRegion a vBar) ∧
      RouteBFieldsEqOn SOld P.terminalFields
        (routeBLowerRegion a vBar vStar) := by
  let d := (vBar + vStar) / 2
  let e := (vBar + d) / 2
  have hBarD : vBar < d := by dsimp [d]; linarith only [hBarStar]
  have hdStar : d < vStar := by dsimp [d]; linarith only [hBarStar]
  have hd : d ∈ Ioo (0 : ℝ) vStar :=
    ⟨ha.trans (haBar.trans hBarD), hdStar⟩
  have hBarE : vBar < e := by dsimp [e]; linarith only [hBarD]
  have heD : e < d := by dsimp [e]; linarith only [hBarD]
  have heStar : e < vStar := heD.trans hdStar
  let F := routeBCanonicalOldFields d (S d)
  let T := P.terminalFields
  have hFC1 : RouteBFieldsC1On F (closedCoordTriangle 0 e) :=
    routeBCanonicalOldFields_c1
      (ha.trans (haBar.trans hBarE)) heD (hfamily d hd).1
  have hBottom : RouteBFieldsC1On F (routeBOldRegion a vBar) := by
    intro c
    have hC1 := routeBCanonicalOldFields_c1
      (ha.trans haBar) hBarD (hfamily d hd).1
    exact (hC1 c).mono (fun p hp => hp.1)
  have hTop : RouteBFieldsC1On T
      (routeBLowerRegion a vBar vStar) := by
    simpa only [T, routeBLowerRegion] using J.terminalFields_c1
  have hTopF : RouteBFieldsEqOn T F (routeBLowerRegion a vBar e) := by
    intro c p hp
    exact P.terminalFields_eq_canonical_old ha haBar hd
      (hfamily d hd).1 ⟨hp.1, ⟨hp.2.1, hp.2.2.trans_lt heD⟩⟩ c
  have hSeam :
      RouteBFieldsEqOn F T
        (routeBOldRegion a vBar ∩ routeBLowerRegion a vBar vStar) ∧
      RouteBFieldsJetEqOn F T
        (routeBOldRegion a vBar) (routeBLowerRegion a vBar vStar) := by
    constructor
    · intro c
      exact (routeB_old_scalar_terminal_seam_of_common
        ha haBar hBarE heStar
        (routeBField F c) (routeBField T c) (routeBField F c)
        (hFC1 c) (hTop c) (fun _ _ => rfl) (hTopF c)).1
    · intro c
      exact (routeB_old_scalar_terminal_seam_of_common
        ha haBar hBarE heStar
        (routeBField F c) (routeBField T c) (routeBField F c)
        (hFC1 c) (hTop c) (fun _ _ => rfl) (hTopF c)).2
  obtain ⟨SOld, hC1, hEqBottom, hEqTop⟩ :=
    exists_routeB_old_fields_c1_glue ha haBar hBarStar F T
      hBottom hTop hSeam.1 hSeam.2
  exact ⟨d, ⟨hBarD, hdStar⟩, SOld, hC1, hEqBottom, hEqTop⟩

end ChristodoulouBV.Uniqueness

end
