module

public import Mathlib

/-! Axis points adjacent to a development. -/

@[expose] public section

namespace ChristodoulouBV

/-- Parameters of diagonal points in the closure of `U` (D5).
Christodoulou 1993, pp. 1146–1147; `source/transcription/s3-uniqueness.tex:27-47`. -/
def adjacentAxis (U : Set (ℝ × ℝ)) : Set ℝ :=
  {a | (a, a) ∈ closure U}

end ChristodoulouBV

end
