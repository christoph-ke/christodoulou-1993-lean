module

public import Mathlib

/-! Seven reduced fields in double-null coordinates. -/

@[expose] public section

namespace ChristodoulouBV

/-- `r, φ, m, λ, ν, α, β` from the reduced system; D2 chooses total curried fields.
Christodoulou 1993, pp. 1133–1138, (1.5), (1.11)–(1.18);
`source/transcription/s1-introduction.tex:116-121,301-346`. -/
structure Fields where
  r : ℝ → ℝ → ℝ
  phi : ℝ → ℝ → ℝ
  m : ℝ → ℝ → ℝ
  lam : ℝ → ℝ → ℝ
  nu : ℝ → ℝ → ℝ
  alpha : ℝ → ℝ → ℝ
  beta : ℝ → ℝ → ℝ

end ChristodoulouBV

end
