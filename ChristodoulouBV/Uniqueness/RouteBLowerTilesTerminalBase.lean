module

public import ChristodoulouBV.Uniqueness.RouteBLowerCoverSafety
import all ChristodoulouBV.ForMathlib.ODE.Goursat
import Mathlib.Tactic

/-!
# Global representative of the compact terminal state

Clipping the incoming coordinate of the old family's terminal state gives a
continuous global representative for the lower tile interface.
-/

public section

open Set

namespace ChristodoulouBV.Uniqueness

/-- The old family's terminal seven-state value, extended constantly past
the endpoints of the incoming interval. -/
@[expose] def lowerTerminalBase
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    (T : OffAxisTerminalTraces a vBar vStar S) (u : ℝ) :
    C1Solution.RectangleState :=
  T.rectangleState (Goursat.clip 0 a u, vStar)

/-- The clipped terminal seven-state field is globally continuous and
agrees with the old family on the whole compact lower base. -/
theorem lowerTerminalBase_regular
    {a vBar vStar : ℝ} {S : ℝ → Fields}
    (T : OffAxisTerminalTraces a vBar vStar S)
    (ha : 0 ≤ a) (hBarStar : vBar ≤ vStar) :
    Continuous (lowerTerminalBase T) ∧
    (∀ u ∈ Icc 0 a,
      lowerTerminalBase T u = T.rectangleState (u, vStar)) := by
  have hpath : Continuous
      (fun u : ℝ => (Goursat.clip 0 a u, vStar)) :=
    (Goursat.continuous_clip 0 a).prodMk continuous_const
  have hmap : ∀ u : ℝ,
      (Goursat.clip 0 a u, vStar) ∈ Icc 0 a ×ˢ Icc vBar vStar := by
    intro u
    exact ⟨Goursat.clip_mem_Icc ha u, ⟨hBarStar, le_rfl⟩⟩
  constructor
  · exact T.rectangleState_continuousOn.comp_continuous hpath hmap
  · intro u hu
    simp only [lowerTerminalBase, Goursat.clip_eq_self hu]

end ChristodoulouBV.Uniqueness

end
