module

public import ChristodoulouBV.Uniqueness.RouteBAssemblyRestrict
import Mathlib.Tactic.Linarith

/-!
# Shortening the Route B lower piece

The lower cover is built before the exact new edge length is known. Its
classical equations, horizontal seam, initial data, and signs persist when
the top endpoint is moved closer to the old terminal line.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- A shortened lower piece retains the full classical and horizontal seam
construction required by three-region gluing. The incoming cutoff is strictly
below the terminal line, so every point of the shortened closed rectangle
lies inside the original open development. -/
theorem routeB_short_lower_packet
    {a vStar b' b : ℝ} (ha : 0 < a) (haStar : a < vStar)
    (hStarb' : vStar < b') (hbb : b' < b)
    (SLow : Fields)
    (hLowC1 : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hLowJet : RouteBClassicalJetOn b
      (routeBLowerRegion a vStar b) SLow)
    (hLowLam : ∀ p ∈ routeBLowerRegion a vStar b,
      0 < SLow.lam p.1 p.2)
    (hLowSigns : ∀ p ∈ routeBLowerRegion a vStar b,
      p ∈ developmentWithInitialEdge b →
      0 < SLow.r p.1 p.2 ∧ SLow.nu p.1 p.2 < 0 ∧
        0 < 1 - 2 * SLow.m p.1 p.2 / SLow.r p.1 p.2)
    {alpha₀ : ℝ → ℝ}
    (hLowData : ∀ v ∈ Icc vStar b,
      SLow.r 0 v = v / 2 ∧ SLow.alpha 0 v = alpha₀ v) :
    RouteBFieldsC1On SLow (routeBLowerRegion a vStar b') ∧
    RouteBClassicalJetOn b' (routeBLowerRegion a vStar b') SLow ∧
    (∀ p ∈ routeBLowerRegion a vStar b',
      0 < SLow.lam p.1 p.2) ∧
    (∀ p ∈ routeBLowerRegion a vStar b',
      0 < SLow.r p.1 p.2 ∧ SLow.nu p.1 p.2 < 0 ∧
        0 < 1 - 2 * SLow.m p.1 p.2 / SLow.r p.1 p.2) ∧
    (∀ v ∈ Icc vStar b',
      SLow.r 0 v = v / 2 ∧ SLow.alpha 0 v = alpha₀ v) := by
  have hsub : routeBLowerRegion a vStar b' ⊆
      routeBLowerRegion a vStar b :=
    routeB_lowerRegion_mono_top hbb.le
  refine ⟨(fun c => (hLowC1 c).mono hsub),
    hLowJet.restrict_lower_top ha hStarb' hbb.le hLowC1,
    (fun p hp => hLowLam p (hsub hp)), ?_, ?_⟩
  · intro p hp
    have hpDev : p ∈ developmentWithInitialEdge b := by
      refine ⟨hp.1.1, ?_, ?_⟩
      · exact (hp.1.2.trans_lt haStar).trans_le hp.2.1
      · exact hp.2.2.trans_lt hbb
    exact hLowSigns p (hsub hp) hpDev
  · intro v hv
    exact hLowData v ⟨hv.1, hv.2.trans hbb.le⟩

/-- Any old piece with the terminal trace retains the lower horizontal
seam after the top endpoint is shortened. -/
theorem routeB_short_lower_horizontal_seam
    {a vBar vStar b' b : ℝ} {S : ℝ → Fields}
    (ha : 0 < a) (hStarb' : vStar < b') (hbb : b' ≤ b)
    (P : OffAxisTerminalC1Packet a vBar vStar S)
    (SLow : Fields)
    (hLowC1 : RouteBFieldsC1On SLow (routeBLowerRegion a vStar b))
    (hAnySeam : ∀ TOld : Fields,
      RouteBFieldsC1On TOld (routeBOldRegion a vStar) →
      RouteBFieldsEqOn TOld P.terminalFields
        (routeBLowerRegion a vBar vStar) →
      RouteBFieldsEqOn TOld SLow
        (routeBOldRegion a vStar ∩ routeBLowerRegion a vStar b) ∧
      RouteBFieldsJetEqOn TOld SLow
        (routeBOldRegion a vStar)
        (routeBLowerRegion a vStar b))
    (TOld : Fields)
    (hOldC1 : RouteBFieldsC1On TOld (routeBOldRegion a vStar))
    (hOldTop : RouteBFieldsEqOn TOld P.terminalFields
      (routeBLowerRegion a vBar vStar)) :
    RouteBFieldsEqOn TOld SLow
      (routeBOldRegion a vStar ∩ routeBLowerRegion a vStar b') ∧
    RouteBFieldsJetEqOn TOld SLow
      (routeBOldRegion a vStar)
      (routeBLowerRegion a vStar b') := by
  obtain ⟨hVal, hJet⟩ := hAnySeam TOld hOldC1 hOldTop
  have hsub : routeBLowerRegion a vStar b' ⊆
      routeBLowerRegion a vStar b :=
    routeB_lowerRegion_mono_top hbb
  constructor
  · intro c p hp
    exact hVal c ⟨hp.1, hsub hp.2⟩
  · intro c p hp
    have hBig := hJet c ⟨hp.1, hsub hp.2⟩
    exact hBig.trans
      (routeB_lower_fderivWithin_eq_on_shorter ha hStarb'
        hbb (hLowC1 c) hp.2)

end ChristodoulouBV.Uniqueness

end
