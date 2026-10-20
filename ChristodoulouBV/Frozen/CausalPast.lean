module

public import Mathlib

/-! The causal past of a point in the double-null chart. -/

@[expose] public section

namespace ChristodoulouBV

/-- The printed `J⁻(a,b)` has an open upper endpoint in `v`.
Christodoulou 1993, p. 1146; `source/transcription/s3-uniqueness.tex:7-13`. -/
def causalPast (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Icc 0 a ∧ p.2 ∈ Set.Ioo p.1 b}

end ChristodoulouBV

end
