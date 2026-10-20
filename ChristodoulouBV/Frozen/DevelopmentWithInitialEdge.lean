module

public import ChristodoulouBV.Frozen.OpenDevelopment

/-! The development together with its characteristic initial edge. -/

@[expose] public section

namespace ChristodoulouBV

/-- `𝒟(0,v₀)` augmented by `u = 0` so its initial data are in-domain (D8 analogue).
Christodoulou 1993, pp. 1135–1136, 1148, 1172;
`source/transcription/s1-introduction.tex:222-249`,
`source/transcription/s3-uniqueness.tex:117-120`,
`source/transcription/s5-extension-theorem.tex:4-11`. -/
def developmentWithInitialEdge (v₀ : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < v₀}

end ChristodoulouBV

end
