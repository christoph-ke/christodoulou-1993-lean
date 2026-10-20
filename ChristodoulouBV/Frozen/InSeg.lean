module

public import Mathlib

/-! Closed incoming null segments. -/

@[expose] public section

namespace ChristodoulouBV

/-- A closed segment of `C⁻(v)` used for the integrated equations (D4).
Christodoulou 1993, p. 1137, (1.12); `source/transcription/s1-introduction.tex:301-311`. -/
def inSeg (v u₁ u₂ : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc u₁ u₂ ×ˢ {v}

end ChristodoulouBV

end
