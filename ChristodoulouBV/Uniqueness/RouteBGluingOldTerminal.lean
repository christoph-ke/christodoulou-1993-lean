module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverBaseJetsPackage
public import ChristodoulouBV.Uniqueness.RouteBGluingTerminalFields
public import ChristodoulouBV.Uniqueness.RouteBGluingIdentificationSeam
import all ChristodoulouBV.ForMathlib.Geometry.NullTriangle
import Mathlib.Tactic.Linarith

/-!
# The closed terminal rectangle of the old Route B piece

The base-jet package makes the seven physical fields C¹ on the rectangle.
At every point below the terminal level they coincide with a canonical
finite-cutoff old member. These are the two inputs for gluing the lower
triangle to the terminal rectangle.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The terminal base jets give C¹ regularity of all seven physical fields
on the closed upper rectangle, including `v = vStar`. -/
theorem RouteBTerminalBaseJets.terminalFields_c1
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    {P : OffAxisTerminalC1Packet a vBar vStar S}
    (J : RouteBTerminalBaseJets P) :
    RouteBFieldsC1On P.terminalFields (Icc 0 a ×ˢ Icc vBar vStar) := by
  intro c
  cases c
  · exact J.radius_full.1
  · exact J.phi_full.1
  · exact J.mass_full.1
  · exact J.lam_full.1
  · exact J.nu_full.1
  · exact J.alpha_full.1
  · exact J.beta_full.1

/-- On the strict portion of the terminal rectangle, the construction agrees
with the canonical C¹ extension of each old member that covers the point. -/
theorem OffAxisTerminalC1Packet.terminalFields_eq_canonical_old
    {a vBar vStar d : ℝ} {S : ℝ → Fields}
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (ha : 0 < a) (haBar : a < vBar)
    (hd : d ∈ Ioo (0 : ℝ) vStar)
    (H : IsC1Solution (developmentWithInitialEdge d) (S d))
    {p : ℝ × ℝ} (hp : p ∈ Icc 0 a ×ˢ Ico vBar d) :
    ∀ c : RouteBField,
      routeBField P.terminalFields c p =
        routeBField (routeBCanonicalOldFields d (S d)) c p := by
  have hEq := P.terminalFields_eq_old hd hp.1 hp.2
  have huv : p.1 < p.2 := hp.1.2.trans_lt (haBar.trans_le hp.2.1)
  have hpDev : p ∈ developmentWithInitialEdge d :=
    ⟨hp.1.1, huv, hp.2.2⟩
  let B := (p.2 + d) / 2
  have hB : 0 < B := by dsimp [B]; linarith only [ha, haBar, hp.2.1, hp.2.2]
  have hBd : B < d := by dsimp [B]; linarith only [hp.2.2]
  have hpB : p.2 ≤ B := by dsimp [B]; linarith only [hp.2.2]
  intro c
  cases c
  · exact (hEq .radius).trans
      (C1Solution.canonicalRadius_eq_radius hB hBd H hp.1.1 huv hpB).symm
  · exact hEq .scalar
  · exact (hEq .mass).trans
      (C1Solution.canonicalMass_eq_mass hpDev).symm
  · exact hEq .expansion
  · exact hEq .contraction
  · exact hEq .outgoing
  · exact hEq .incoming

end ChristodoulouBV.Uniqueness

end
