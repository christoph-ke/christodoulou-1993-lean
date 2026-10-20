module

public import Mathlib

/-! Closed outgoing null segments. -/

@[expose] public section

namespace ChristodoulouBV

/-- A closed segment of `C⁺(u)` used for the integrated equations (D4).
Christodoulou 1993, p. 1137, (1.12); `source/transcription/s1-introduction.tex:301-311`. -/
def outSeg (u v₁ v₂ : ℝ) : Set (ℝ × ℝ) :=
  {u} ×ˢ Set.Icc v₁ v₂

end ChristodoulouBV

end
