module

public import Mathlib

/-! The global development with its initial edge. -/

@[expose] public section

namespace ChristodoulouBV

/-- The global off-axis development, including `u = 0` by D8.
Christodoulou 1993, pp. 1135–1136, 1179, 1183;
`source/transcription/s1-introduction.tex:222-249`,
`source/transcription/s6-existence.tex:5-13,238-249`. -/
def globalDomain : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 < p.2}

end ChristodoulouBV

end
